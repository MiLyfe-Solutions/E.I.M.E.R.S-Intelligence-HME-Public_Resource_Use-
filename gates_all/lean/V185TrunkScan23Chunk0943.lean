import V185TrunkScan23Chunk0942

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5582074 : List Nat := [3, 1, 1, 1, 1, 4, 1, 4, 2, 3, 2]
def baseStart_5582074 : Nat := 118140960795 + 5582074 * 2 ^ 59
def prefixEnd_5582074 : Nat := 4983230072969 + 3 ^ 40 * 5582074 * 2
def baseEnd_5582074 : Nat := 2866287010965698343503515

theorem tailTrace_5582074 : CollatzResearch.WordTrace tailWord_5582074 prefixEnd_5582074 2866287010965698343503515 := by
  unfold tailWord_5582074
  simp only [CollatzResearch.WordTrace]
  refine ⟨50898741194776678796212319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135729976519404476789899517 50898741194776678796212319)
  ·
    refine ⟨76348111792165018194318479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50898741194776678796212319 76348111792165018194318479)
    ·
      refine ⟨114522167688247527291477719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76348111792165018194318479 114522167688247527291477719)
      ·
        refine ⟨171783251532371290937216579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114522167688247527291477719 171783251532371290937216579)
        ·
          refine ⟨257674877298556936405824869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171783251532371290937216579 257674877298556936405824869)
          ·
            refine ⟨48314039493479425576092163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 257674877298556936405824869 48314039493479425576092163)
            ·
              refine ⟨72471059240219138364138245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48314039493479425576092163 72471059240219138364138245)
              ·
                refine ⟨13588323607541088443275921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72471059240219138364138245 13588323607541088443275921)
                ·
                  refine ⟨10191242705655816332456941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13588323607541088443275921 10191242705655816332456941)
                  ·
                    refine ⟨3821716014620931124671353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10191242705655816332456941 3821716014620931124671353)
                    ·
                      refine ⟨2866287010965698343503515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3821716014620931124671353 2866287010965698343503515)
                      ·
                        rfl

theorem cell23_5582074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 4, 2, 3, 2].length) (baseStart_5582074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5582074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5582074 prefixEnd_5582074 := by exact prefixLift 5582074
  have htrace : WordTrace (prefixWord ++ tailWord_5582074) baseStart_5582074 baseEnd_5582074 := by
    simpa [prefixWord, tailWord_5582074, baseEnd_5582074] using wordTrace_append hprefix tailTrace_5582074
  have hstable : (prefixWord ++ tailWord_5582074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5582074).length < 2 ^ (prefixWord ++ tailWord_5582074).sum := by decide
  have hdescent : baseEnd_5582074 < baseStart_5582074 := by decide
  rcases family_descends (prefixWord ++ tailWord_5582074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5582080 : List Nat := [2, 1, 1, 2, 1, 1, 3, 1, 5, 6]
def baseStart_5582080 : Nat := 118140960795 + 5582080 * 2 ^ 59
def prefixEnd_5582080 : Nat := 4983230072969 + 3 ^ 40 * 5582080 * 2
def baseEnd_5582080 : Nat := 955430030616541773342829

theorem tailTrace_5582080 : CollatzResearch.WordTrace tailWord_5582080 prefixEnd_5582080 955430030616541773342829 := by
  unfold tailWord_5582080
  simp only [CollatzResearch.WordTrace]
  refine ⟨101797591808542489104783847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135730122411389985473045129 101797591808542489104783847)
  ·
    refine ⟨152696387712813733657175771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101797591808542489104783847 152696387712813733657175771)
    ·
      refine ⟨229044581569220600485763657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152696387712813733657175771 229044581569220600485763657)
      ·
        refine ⟨171783436176915450364322743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 229044581569220600485763657 171783436176915450364322743)
        ·
          refine ⟨257675154265373175546484115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171783436176915450364322743 257675154265373175546484115)
          ·
            refine ⟨386512731398059763319726173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 257675154265373175546484115 386512731398059763319726173)
            ·
              refine ⟨144942274274272411244897315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 386512731398059763319726173 144942274274272411244897315)
              ·
                refine ⟨217413411411408616867345973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 144942274274272411244897315 217413411411408616867345973)
                ·
                  refine ⟨20382507319819557831313685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 217413411411408616867345973 20382507319819557831313685)
                  ·
                    refine ⟨955430030616541773342829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20382507319819557831313685 955430030616541773342829)
                    ·
                      rfl

theorem cell23_5582080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 5, 6].length) (baseStart_5582080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5582080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5582080 prefixEnd_5582080 := by exact prefixLift 5582080
  have htrace : WordTrace (prefixWord ++ tailWord_5582080) baseStart_5582080 baseEnd_5582080 := by
    simpa [prefixWord, tailWord_5582080, baseEnd_5582080] using wordTrace_append hprefix tailTrace_5582080
  have hstable : (prefixWord ++ tailWord_5582080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5582080).length < 2 ^ (prefixWord ++ tailWord_5582080).sum := by decide
  have hdescent : baseEnd_5582080 < baseStart_5582080 := by decide
  rcases family_descends (prefixWord ++ tailWord_5582080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5582097 : List Nat := [1, 2, 2, 1, 1, 4, 4, 1, 1, 6]
def baseStart_5582097 : Nat := 118140960795 + 5582097 * 2 ^ 59
def prefixEnd_5582097 : Nat := 4983230072969 + 3 ^ 40 * 5582097 * 2
def baseEnd_5582097 : Nat := 955432940340250584505303

theorem tailTrace_5582097 : CollatzResearch.WordTrace tailWord_5582097 prefixEnd_5582097 955432940340250584505303 := by
  unfold tailWord_5582097
  simp only [CollatzResearch.WordTrace]
  refine ⟨203595803658023390112936545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135730535772015593408624363 203595803658023390112936545)
  ·
    refine ⟨152696852743517542584702409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203595803658023390112936545 152696852743517542584702409)
    ·
      refine ⟨114522639557638156938526807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152696852743517542584702409 114522639557638156938526807)
      ·
        refine ⟨171783959336457235407790211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114522639557638156938526807 171783959336457235407790211)
        ·
          refine ⟨257675939004685853111685317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171783959336457235407790211 257675939004685853111685317)
          ·
            refine ⟨48314238563378597458440997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 257675939004685853111685317 48314238563378597458440997)
            ·
              refine ⟨9058919730633487023457687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48314238563378597458440997 9058919730633487023457687)
              ·
                refine ⟨13588379595950230535186531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9058919730633487023457687 13588379595950230535186531)
                ·
                  refine ⟨20382569393925345802779797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13588379595950230535186531 20382569393925345802779797)
                  ·
                    refine ⟨955432940340250584505303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20382569393925345802779797 955432940340250584505303)
                    ·
                      rfl

theorem cell23_5582097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 6].length) (baseStart_5582097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5582097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5582097 prefixEnd_5582097 := by exact prefixLift 5582097
  have htrace : WordTrace (prefixWord ++ tailWord_5582097) baseStart_5582097 baseEnd_5582097 := by
    simpa [prefixWord, tailWord_5582097, baseEnd_5582097] using wordTrace_append hprefix tailTrace_5582097
  have hstable : (prefixWord ++ tailWord_5582097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5582097).length < 2 ^ (prefixWord ++ tailWord_5582097).sum := by decide
  have hdescent : baseEnd_5582097 < baseStart_5582097 := by decide
  rcases family_descends (prefixWord ++ tailWord_5582097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5582131 : List Nat := [1, 1, 1, 2, 5, 4, 1, 2, 2, 4]
def baseStart_5582131 : Nat := 118140960795 + 5582131 * 2 ^ 59
def prefixEnd_5582131 : Nat := 4983230072969 + 3 ^ 40 * 5582131 * 2
def baseEnd_5582131 : Nat := 955438759787668206830251

theorem tailTrace_5582131 : CollatzResearch.WordTrace tailWord_5582131 prefixEnd_5582131 955438759787668206830251 := by
  unfold tailWord_5582131
  simp only [CollatzResearch.WordTrace]
  refine ⟨203597043739900213919674247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135731362493266809279782831 203597043739900213919674247)
  ·
    refine ⟨305395565609850320879511371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203597043739900213919674247 305395565609850320879511371)
    ·
      refine ⟨458093348414775481319267057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305395565609850320879511371 458093348414775481319267057)
      ·
        refine ⟨343570011311081610989450293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 458093348414775481319267057 343570011311081610989450293)
        ·
          refine ⟨32209688560413901030260965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 343570011311081610989450293 32209688560413901030260965)
          ·
            refine ⟨6039316605077606443173931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32209688560413901030260965 6039316605077606443173931)
            ·
              refine ⟨9058974907616409664760897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6039316605077606443173931 9058974907616409664760897)
              ·
                refine ⟨6794231180712307248570673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9058974907616409664760897 6794231180712307248570673)
                ·
                  refine ⟨5095673385534230436428005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6794231180712307248570673 5095673385534230436428005)
                  ·
                    refine ⟨955438759787668206830251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5095673385534230436428005 955438759787668206830251)
                    ·
                      rfl

theorem cell23_5582131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 2, 2, 4].length) (baseStart_5582131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5582131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5582131 prefixEnd_5582131 := by exact prefixLift 5582131
  have htrace : WordTrace (prefixWord ++ tailWord_5582131) baseStart_5582131 baseEnd_5582131 := by
    simpa [prefixWord, tailWord_5582131, baseEnd_5582131] using wordTrace_append hprefix tailTrace_5582131
  have hstable : (prefixWord ++ tailWord_5582131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5582131).length < 2 ^ (prefixWord ++ tailWord_5582131).sum := by decide
  have hdescent : baseEnd_5582131 < baseStart_5582131 := by decide
  rcases family_descends (prefixWord ++ tailWord_5582131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5582138 : List Nat := [3, 1, 1, 1, 4, 1, 1, 6, 1, 2, 2]
def baseStart_5582138 : Nat := 118140960795 + 5582138 * 2 ^ 59
def prefixEnd_5582138 : Nat := 4983230072969 + 3 ^ 40 * 5582138 * 2
def baseEnd_5582138 : Nat := 2866319873727586093103221

theorem tailTrace_5582138 : CollatzResearch.WordTrace tailWord_5582138 prefixEnd_5582138 2866319873727586093103221 := by
  unfold tailWord_5582138
  simp only [CollatzResearch.WordTrace]
  refine ⟨50899324762718713528794767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135731532700583236076786045 50899324762718713528794767)
  ·
    refine ⟨76348987144078070293192151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50899324762718713528794767 76348987144078070293192151)
    ·
      refine ⟨114523480716117105439788227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76348987144078070293192151 114523480716117105439788227)
      ·
        refine ⟨171785221074175658159682341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114523480716117105439788227 171785221074175658159682341)
        ·
          refine ⟨32209728951407935904940439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 171785221074175658159682341 32209728951407935904940439)
          ·
            refine ⟨48314593427111903857410659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32209728951407935904940439 48314593427111903857410659)
            ·
              refine ⟨72471890140667855786115989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48314593427111903857410659 72471890140667855786115989)
              ·
                refine ⟨3397119850343805739974187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 72471890140667855786115989 3397119850343805739974187)
                ·
                  refine ⟨5095679775515708609961281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3397119850343805739974187 5095679775515708609961281)
                  ·
                    refine ⟨3821759831636781457470961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5095679775515708609961281 3821759831636781457470961)
                    ·
                      refine ⟨2866319873727586093103221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3821759831636781457470961 2866319873727586093103221)
                      ·
                        rfl

theorem cell23_5582138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 6, 1, 2, 2].length) (baseStart_5582138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5582138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5582138 prefixEnd_5582138 := by exact prefixLift 5582138
  have htrace : WordTrace (prefixWord ++ tailWord_5582138) baseStart_5582138 baseEnd_5582138 := by
    simpa [prefixWord, tailWord_5582138, baseEnd_5582138] using wordTrace_append hprefix tailTrace_5582138
  have hstable : (prefixWord ++ tailWord_5582138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5582138).length < 2 ^ (prefixWord ++ tailWord_5582138).sum := by decide
  have hdescent : baseEnd_5582138 < baseStart_5582138 := by decide
  rcases family_descends (prefixWord ++ tailWord_5582138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5582141 : List Nat := [1, 4, 1, 5, 1, 1, 1, 2, 1, 1, 5]
def baseStart_5582141 : Nat := 118140960795 + 5582141 * 2 ^ 59
def prefixEnd_5582141 : Nat := 4983230072969 + 3 ^ 40 * 5582141 * 2
def baseEnd_5582141 : Nat := 2866321414169549581365707

theorem tailTrace_5582141 : CollatzResearch.WordTrace tailWord_5582141 prefixEnd_5582141 2866321414169549581365707 := by
  unfold tailWord_5582141
  simp only [CollatzResearch.WordTrace]
  refine ⟨203597408469863985627538277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135731605646575990418358851 203597408469863985627538277)
  ·
    refine ⟨38174514088099497305163427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 203597408469863985627538277 38174514088099497305163427)
    ·
      refine ⟨57261771132149245957745141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38174514088099497305163427 57261771132149245957745141)
      ·
        refine ⟨5368291043638991808538607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 57261771132149245957745141 5368291043638991808538607)
        ·
          refine ⟨8052436565458487712807911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5368291043638991808538607 8052436565458487712807911)
          ·
            refine ⟨12078654848187731569211867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8052436565458487712807911 12078654848187731569211867)
            ·
              refine ⟨18117982272281597353817801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12078654848187731569211867 18117982272281597353817801)
              ·
                refine ⟨13588486704211198015363351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18117982272281597353817801 13588486704211198015363351)
                ·
                  refine ⟨20382730056316797023045027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13588486704211198015363351 20382730056316797023045027)
                  ·
                    refine ⟨30574095084475195534567541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20382730056316797023045027 30574095084475195534567541)
                    ·
                      refine ⟨2866321414169549581365707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30574095084475195534567541 2866321414169549581365707)
                      ·
                        rfl

theorem cell23_5582141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_5582141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5582141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5582141 prefixEnd_5582141 := by exact prefixLift 5582141
  have htrace : WordTrace (prefixWord ++ tailWord_5582141) baseStart_5582141 baseEnd_5582141 := by
    simpa [prefixWord, tailWord_5582141, baseEnd_5582141] using wordTrace_append hprefix tailTrace_5582141
  have hstable : (prefixWord ++ tailWord_5582141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5582141).length < 2 ^ (prefixWord ++ tailWord_5582141).sum := by decide
  have hdescent : baseEnd_5582141 < baseStart_5582141 := by decide
  rcases family_descends (prefixWord ++ tailWord_5582141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5582166 : List Nat := [5, 2, 3, 1, 1, 2, 1, 3, 1, 1, 3]
def baseStart_5582166 : Nat := 118140960795 + 5582166 * 2 ^ 59
def prefixEnd_5582166 : Nat := 4983230072969 + 3 ^ 40 * 5582166 * 2
def baseEnd_5582166 : Nat := 2866334251185911983553093

theorem tailTrace_5582166 : CollatzResearch.WordTrace tailWord_5582166 prefixEnd_5582166 2866334251185911983553093 := by
  unfold tailWord_5582166
  simp only [CollatzResearch.WordTrace]
  refine ⟨12724895018423338431074897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 135732213529848943264798901 12724895018423338431074897)
  ·
    refine ⟨9543671263817503823306173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12724895018423338431074897 9543671263817503823306173)
    ·
      refine ⟨3578876723931563933739815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9543671263817503823306173 3578876723931563933739815)
      ·
        refine ⟨5368315085897345900609723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3578876723931563933739815 5368315085897345900609723)
        ·
          refine ⟨8052472628846018850914585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5368315085897345900609723 8052472628846018850914585)
          ·
            refine ⟨6039354471634514138185939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8052472628846018850914585 6039354471634514138185939)
            ·
              refine ⟨9059031707451771207278909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6039354471634514138185939 9059031707451771207278909)
              ·
                refine ⟨3397136890294414202729591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9059031707451771207278909 3397136890294414202729591)
                ·
                  refine ⟨5095705335441621304094387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3397136890294414202729591 5095705335441621304094387)
                  ·
                    refine ⟨7643558003162431956141581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5095705335441621304094387 7643558003162431956141581)
                    ·
                      refine ⟨2866334251185911983553093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7643558003162431956141581 2866334251185911983553093)
                      ·
                        rfl

theorem cell23_5582166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_5582166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5582166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5582166 prefixEnd_5582166 := by exact prefixLift 5582166
  have htrace : WordTrace (prefixWord ++ tailWord_5582166) baseStart_5582166 baseEnd_5582166 := by
    simpa [prefixWord, tailWord_5582166, baseEnd_5582166] using wordTrace_append hprefix tailTrace_5582166
  have hstable : (prefixWord ++ tailWord_5582166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5582166).length < 2 ^ (prefixWord ++ tailWord_5582166).sum := by decide
  have hdescent : baseEnd_5582166 < baseStart_5582166 := by decide
  rcases family_descends (prefixWord ++ tailWord_5582166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5582167 : List Nat := [1, 1, 3, 2, 3, 2, 1, 1, 2, 2, 5]
def baseStart_5582167 : Nat := 118140960795 + 5582167 * 2 ^ 59
def prefixEnd_5582167 : Nat := 4983230072969 + 3 ^ 40 * 5582167 * 2
def baseEnd_5582167 : Nat := 2866334764666566479640587

theorem tailTrace_5582167 : CollatzResearch.WordTrace tailWord_5582167 prefixEnd_5582167 2866334764666566479640587 := by
  unfold tailWord_5582167
  simp only [CollatzResearch.WordTrace]
  refine ⟨203598356767769792067984755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135732237845179861378656503 203598356767769792067984755)
  ·
    refine ⟨305397535151654688101977133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203598356767769792067984755 305397535151654688101977133)
    ·
      refine ⟨114524075681870508038241425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 305397535151654688101977133 114524075681870508038241425)
      ·
        refine ⟨85893056761402881028681069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114524075681870508038241425 85893056761402881028681069)
        ·
          refine ⟨32209896285526080385755401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85893056761402881028681069 32209896285526080385755401)
          ·
            refine ⟨24157422214144560289316551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32209896285526080385755401 24157422214144560289316551)
            ·
              refine ⟨36236133321216840433974827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24157422214144560289316551 36236133321216840433974827)
              ·
                refine ⟨54354199981825260650962241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36236133321216840433974827 54354199981825260650962241)
                ·
                  refine ⟨40765649986368945488221681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54354199981825260650962241 40765649986368945488221681)
                  ·
                    refine ⟨30574237489776709116166261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40765649986368945488221681 30574237489776709116166261)
                    ·
                      refine ⟨2866334764666566479640587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30574237489776709116166261 2866334764666566479640587)
                      ·
                        rfl

theorem cell23_5582167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 1, 2, 2, 5].length) (baseStart_5582167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5582167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5582167 prefixEnd_5582167 := by exact prefixLift 5582167
  have htrace : WordTrace (prefixWord ++ tailWord_5582167) baseStart_5582167 baseEnd_5582167 := by
    simpa [prefixWord, tailWord_5582167, baseEnd_5582167] using wordTrace_append hprefix tailTrace_5582167
  have hstable : (prefixWord ++ tailWord_5582167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5582167).length < 2 ^ (prefixWord ++ tailWord_5582167).sum := by decide
  have hdescent : baseEnd_5582167 < baseStart_5582167 := by decide
  rcases family_descends (prefixWord ++ tailWord_5582167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5582181 : List Nat := [1, 3, 1, 3, 1, 2, 1, 5, 1, 3, 2]
def baseStart_5582181 : Nat := 118140960795 + 5582181 * 2 ^ 59
def prefixEnd_5582181 : Nat := 4983230072969 + 3 ^ 40 * 5582181 * 2
def baseEnd_5582181 : Nat := 2866341953395729424865523

theorem tailTrace_5582181 : CollatzResearch.WordTrace tailWord_5582181 prefixEnd_5582181 2866341953395729424865523 := by
  unfold tailWord_5582181
  simp only [CollatzResearch.WordTrace]
  refine ⟨203598867389719072458994397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135732578259812714972662931 203598867389719072458994397)
  ·
    refine ⟨76349575271144652172122899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 203598867389719072458994397 76349575271144652172122899)
    ·
      refine ⟨114524362906716978258184349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76349575271144652172122899 114524362906716978258184349)
      ·
        refine ⟨42946636090018866846819131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114524362906716978258184349 42946636090018866846819131)
        ·
          refine ⟨64419954135028300270228697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42946636090018866846819131 64419954135028300270228697)
          ·
            refine ⟨48314965601271225202671523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64419954135028300270228697 48314965601271225202671523)
            ·
              refine ⟨72472448401906837804007285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48314965601271225202671523 72472448401906837804007285)
              ·
                refine ⟨6794292037678766044125683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 72472448401906837804007285 6794292037678766044125683)
                ·
                  refine ⟨10191438056518149066188525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6794292037678766044125683 10191438056518149066188525)
                  ·
                    refine ⟨3821789271194305899820697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10191438056518149066188525 3821789271194305899820697)
                    ·
                      refine ⟨2866341953395729424865523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3821789271194305899820697 2866341953395729424865523)
                      ·
                        rfl

theorem cell23_5582181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 5, 1, 3, 2].length) (baseStart_5582181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5582181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5582181 prefixEnd_5582181 := by exact prefixLift 5582181
  have htrace : WordTrace (prefixWord ++ tailWord_5582181) baseStart_5582181 baseEnd_5582181 := by
    simpa [prefixWord, tailWord_5582181, baseEnd_5582181] using wordTrace_append hprefix tailTrace_5582181
  have hstable : (prefixWord ++ tailWord_5582181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5582181).length < 2 ^ (prefixWord ++ tailWord_5582181).sum := by decide
  have hdescent : baseEnd_5582181 < baseStart_5582181 := by decide
  rcases family_descends (prefixWord ++ tailWord_5582181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5582228 : List Nat := [2, 4, 2, 1, 2, 2, 1, 2, 1, 4, 2]
def baseStart_5582228 : Nat := 118140960795 + 5582228 * 2 ^ 59
def prefixEnd_5582228 : Nat := 4983230072969 + 3 ^ 40 * 5582228 * 2
def baseEnd_5582228 : Nat := 2866366086986490740977807

theorem tailTrace_5582228 : CollatzResearch.WordTrace tailWord_5582228 prefixEnd_5582228 2866366086986490740977807 := by
  unfold tailWord_5582228
  simp only [CollatzResearch.WordTrace]
  refine ⟨101800290810274399742977669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135733721080365866323970225 101800290810274399742977669)
  ·
    refine ⟨19087554526926449951808313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101800290810274399742977669 19087554526926449951808313)
    ·
      refine ⟨14315665895194837463856235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19087554526926449951808313 14315665895194837463856235)
      ·
        refine ⟨21473498842792256195784353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14315665895194837463856235 21473498842792256195784353)
        ·
          refine ⟨16105124132094192146838265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21473498842792256195784353 16105124132094192146838265)
          ·
            refine ⟨12078843099070644110128699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16105124132094192146838265 12078843099070644110128699)
            ·
              refine ⟨18118264648605966165193049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12078843099070644110128699 18118264648605966165193049)
              ·
                refine ⟨13588698486454474623894787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18118264648605966165193049 13588698486454474623894787)
                ·
                  refine ⟨20383047729681711935842181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13588698486454474623894787 20383047729681711935842181)
                  ·
                    refine ⟨3821821449315320987970409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20383047729681711935842181 3821821449315320987970409)
                    ·
                      refine ⟨2866366086986490740977807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3821821449315320987970409 2866366086986490740977807)
                      ·
                        rfl

theorem cell23_5582228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 2, 1, 4, 2].length) (baseStart_5582228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5582228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5582228 prefixEnd_5582228 := by exact prefixLift 5582228
  have htrace : WordTrace (prefixWord ++ tailWord_5582228) baseStart_5582228 baseEnd_5582228 := by
    simpa [prefixWord, tailWord_5582228, baseEnd_5582228] using wordTrace_append hprefix tailTrace_5582228
  have hstable : (prefixWord ++ tailWord_5582228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5582228).length < 2 ^ (prefixWord ++ tailWord_5582228).sum := by decide
  have hdescent : baseEnd_5582228 < baseStart_5582228 := by decide
  rcases family_descends (prefixWord ++ tailWord_5582228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5582244 : List Nat := [2, 3, 1, 2, 1, 1, 1, 4, 2, 3, 3]
def baseStart_5582244 : Nat := 118140960795 + 5582244 * 2 ^ 59
def prefixEnd_5582244 : Nat := 4983230072969 + 3 ^ 40 * 5582244 * 2
def baseEnd_5582244 : Nat := 2866374302676962678377733

theorem tailTrace_5582244 : CollatzResearch.WordTrace tailWord_5582244 prefixEnd_5582244 2866374302676962678377733 := by
  unfold tailWord_5582244
  simp only [CollatzResearch.WordTrace]
  refine ⟨101800582594245417109268893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135734110125660556145691857 101800582594245417109268893)
  ·
    refine ⟨38175218472842031415975835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101800582594245417109268893 38175218472842031415975835)
    ·
      refine ⟨57262827709263047123963753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38175218472842031415975835 57262827709263047123963753)
      ·
        refine ⟨42947120781947285342972815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57262827709263047123963753 42947120781947285342972815)
        ·
          refine ⟨64420681172920928014459223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42947120781947285342972815 64420681172920928014459223)
          ·
            refine ⟨96631021759381392021688835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64420681172920928014459223 96631021759381392021688835)
            ·
              refine ⟨144946532639072088032533253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96631021759381392021688835 144946532639072088032533253)
              ·
                refine ⟨27177474869826016506099985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 144946532639072088032533253 27177474869826016506099985)
                ·
                  refine ⟨20383106152369512379574989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27177474869826016506099985 20383106152369512379574989)
                  ·
                    refine ⟨7643664807138567142340621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20383106152369512379574989 7643664807138567142340621)
                    ·
                      refine ⟨2866374302676962678377733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7643664807138567142340621 2866374302676962678377733)
                      ·
                        rfl

theorem cell23_5582244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 4, 2, 3, 3].length) (baseStart_5582244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5582244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5582244 prefixEnd_5582244 := by exact prefixLift 5582244
  have htrace : WordTrace (prefixWord ++ tailWord_5582244) baseStart_5582244 baseEnd_5582244 := by
    simpa [prefixWord, tailWord_5582244, baseEnd_5582244] using wordTrace_append hprefix tailTrace_5582244
  have hstable : (prefixWord ++ tailWord_5582244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5582244).length < 2 ^ (prefixWord ++ tailWord_5582244).sum := by decide
  have hdescent : baseEnd_5582244 < baseStart_5582244 := by decide
  rcases family_descends (prefixWord ++ tailWord_5582244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5582261 : List Nat := [1, 3, 3, 2, 2, 2, 1, 1, 2, 3, 3]
def baseStart_5582261 : Nat := 118140960795 + 5582261 * 2 ^ 59
def prefixEnd_5582261 : Nat := 4983230072969 + 3 ^ 40 * 5582261 * 2
def baseEnd_5582261 : Nat := 2866383031848089111865155

theorem tailTrace_5582261 : CollatzResearch.WordTrace tailWord_5582261 prefixEnd_5582261 2866383031848089111865155 := by
  unfold tailWord_5582261
  simp only [CollatzResearch.WordTrace]
  refine ⟨203601785229429246121906637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135734523486286164081271091 203601785229429246121906637)
  ·
    refine ⟨76350669461035967295714989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 203601785229429246121906637 76350669461035967295714989)
    ·
      refine ⟨28631501047888487735893121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76350669461035967295714989 28631501047888487735893121)
      ·
        refine ⟨21473625785916365801919841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28631501047888487735893121 21473625785916365801919841)
        ·
          refine ⟨16105219339437274351439881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21473625785916365801919841 16105219339437274351439881)
          ·
            refine ⟨12078914504577955763579911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16105219339437274351439881 12078914504577955763579911)
            ·
              refine ⟨18118371756866933645369867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12078914504577955763579911 18118371756866933645369867)
              ·
                refine ⟨27177557635300400468054801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18118371756866933645369867 27177557635300400468054801)
                ·
                  refine ⟨20383168226475300351041101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27177557635300400468054801 20383168226475300351041101)
                  ·
                    refine ⟨7643688084928237631640413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20383168226475300351041101 7643688084928237631640413)
                    ·
                      refine ⟨2866383031848089111865155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7643688084928237631640413 2866383031848089111865155)
                      ·
                        rfl

theorem cell23_5582261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 1, 2, 3, 3].length) (baseStart_5582261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5582261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5582261 prefixEnd_5582261 := by exact prefixLift 5582261
  have htrace : WordTrace (prefixWord ++ tailWord_5582261) baseStart_5582261 baseEnd_5582261 := by
    simpa [prefixWord, tailWord_5582261, baseEnd_5582261] using wordTrace_append hprefix tailTrace_5582261
  have hstable : (prefixWord ++ tailWord_5582261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5582261).length < 2 ^ (prefixWord ++ tailWord_5582261).sum := by decide
  have hdescent : baseEnd_5582261 < baseStart_5582261 := by decide
  rcases family_descends (prefixWord ++ tailWord_5582261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5582311 : List Nat := [1, 1, 5, 2, 1, 2, 1, 3, 3, 4]
def baseStart_5582311 : Nat := 118140960795 + 5582311 * 2 ^ 59
def prefixEnd_5582311 : Nat := 4983230072969 + 3 ^ 40 * 5582311 * 2
def baseEnd_5582311 : Nat := 955469568626937972079975

theorem tailTrace_5582311 : CollatzResearch.WordTrace tailWord_5582311 prefixEnd_5582311 955469568626937972079975 := by
  unfold tailWord_5582311
  simp only [CollatzResearch.WordTrace]
  refine ⟨203603608879248104661226787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135735739252832069774151191 203603608879248104661226787)
  ·
    refine ⟨305405413318872156991840181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203603608879248104661226787 305405413318872156991840181)
    ·
      refine ⟨28631757498644264717985017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 305405413318872156991840181 28631757498644264717985017)
      ·
        refine ⟨21473818123983198538488763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28631757498644264717985017 21473818123983198538488763)
        ·
          refine ⟨32210727185974797807733145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21473818123983198538488763 32210727185974797807733145)
          ·
            refine ⟨24158045389481098355799859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32210727185974797807733145 24158045389481098355799859)
            ·
              refine ⟨36237068084221647533699789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24158045389481098355799859 36237068084221647533699789)
              ·
                refine ⟨13588900531583117825137421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36237068084221647533699789 13588900531583117825137421)
                ·
                  refine ⟨5095837699343669184426533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13588900531583117825137421 5095837699343669184426533)
                  ·
                    refine ⟨955469568626937972079975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5095837699343669184426533 955469568626937972079975)
                    ·
                      rfl

theorem cell23_5582311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 3, 3, 4].length) (baseStart_5582311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5582311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5582311 prefixEnd_5582311 := by exact prefixLift 5582311
  have htrace : WordTrace (prefixWord ++ tailWord_5582311) baseStart_5582311 baseEnd_5582311 := by
    simpa [prefixWord, tailWord_5582311, baseEnd_5582311] using wordTrace_append hprefix tailTrace_5582311
  have hstable : (prefixWord ++ tailWord_5582311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5582311).length < 2 ^ (prefixWord ++ tailWord_5582311).sum := by decide
  have hdescent : baseEnd_5582311 < baseStart_5582311 := by decide
  rcases family_descends (prefixWord ++ tailWord_5582311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5582338 : List Nat := [3, 4, 1, 2, 1, 1, 2, 1, 1, 4, 3]
def baseStart_5582338 : Nat := 118140960795 + 5582338 * 2 ^ 59
def prefixEnd_5582338 : Nat := 4983230072969 + 3 ^ 40 * 5582338 * 2
def baseEnd_5582338 : Nat := 2866422569858485310602301

theorem tailTrace_5582338 : CollatzResearch.WordTrace tailWord_5582338 prefixEnd_5582338 2866422569858485310602301 := by
  unfold tailWord_5582338
  simp only [CollatzResearch.WordTrace]
  refine ⟨50901148412537572068114917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135736395766766858848306445 50901148412537572068114917)
  ·
    refine ⟨9543965327350794762771547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50901148412537572068114917 9543965327350794762771547)
    ·
      refine ⟨14315947991026192144157321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9543965327350794762771547 14315947991026192144157321)
      ·
        refine ⟨10736960993269644108117991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14315947991026192144157321 10736960993269644108117991)
        ·
          refine ⟨16105441489904466162176987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10736960993269644108117991 16105441489904466162176987)
          ·
            refine ⟨24158162234856699243265481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16105441489904466162176987 24158162234856699243265481)
            ·
              refine ⟨18118621676142524432449111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24158162234856699243265481 18118621676142524432449111)
              ·
                refine ⟨27177932514213786648673667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18118621676142524432449111 27177932514213786648673667)
                ·
                  refine ⟨40766898771320679973010501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27177932514213786648673667 40766898771320679973010501)
                  ·
                    refine ⟨7643793519622627494939469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40766898771320679973010501 7643793519622627494939469)
                    ·
                      refine ⟨2866422569858485310602301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7643793519622627494939469 2866422569858485310602301)
                      ·
                        rfl

theorem cell23_5582338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_5582338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5582338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5582338 prefixEnd_5582338 := by exact prefixLift 5582338
  have htrace : WordTrace (prefixWord ++ tailWord_5582338) baseStart_5582338 baseEnd_5582338 := by
    simpa [prefixWord, tailWord_5582338, baseEnd_5582338] using wordTrace_append hprefix tailTrace_5582338
  have hstable : (prefixWord ++ tailWord_5582338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5582338).length < 2 ^ (prefixWord ++ tailWord_5582338).sum := by decide
  have hdescent : baseEnd_5582338 < baseStart_5582338 := by decide
  rcases family_descends (prefixWord ++ tailWord_5582338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5582378 : List Nat := [3, 1, 4, 1, 1, 1, 1, 2, 4, 3, 2]
def baseStart_5582378 : Nat := 118140960795 + 5582378 * 2 ^ 59
def prefixEnd_5582378 : Nat := 4983230072969 + 3 ^ 40 * 5582378 * 2
def baseEnd_5582378 : Nat := 2866443109084665154102117

theorem tailTrace_5582378 : CollatzResearch.WordTrace tailWord_5582378 prefixEnd_5582378 2866443109084665154102117 := by
  unfold tailWord_5582378
  simp only [CollatzResearch.WordTrace]
  refine ⟨50901513142501343775978947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135737368380003583402610525 50901513142501343775978947)
  ·
    refine ⟨76352269713752015663968421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50901513142501343775978947 76352269713752015663968421)
    ·
      refine ⟨14316050571328502936994079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76352269713752015663968421 14316050571328502936994079)
      ·
        refine ⟨21474075856992754405491119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14316050571328502936994079 21474075856992754405491119)
        ·
          refine ⟨32211113785489131608236679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21474075856992754405491119 32211113785489131608236679)
          ·
            refine ⟨48316670678233697412355019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32211113785489131608236679 48316670678233697412355019)
            ·
              refine ⟨72475006017350546118532529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48316670678233697412355019 72475006017350546118532529)
              ·
                refine ⟨54356254513012909588899397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72475006017350546118532529 54356254513012909588899397)
                ·
                  refine ⟨10191797721189920547918637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54356254513012909588899397 10191797721189920547918637)
                  ·
                    refine ⟨3821924145446220205469489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10191797721189920547918637 3821924145446220205469489)
                    ·
                      refine ⟨2866443109084665154102117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3821924145446220205469489 2866443109084665154102117)
                      ·
                        rfl

theorem cell23_5582378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 2, 4, 3, 2].length) (baseStart_5582378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5582378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5582378 prefixEnd_5582378 := by exact prefixLift 5582378
  have htrace : WordTrace (prefixWord ++ tailWord_5582378) baseStart_5582378 baseEnd_5582378 := by
    simpa [prefixWord, tailWord_5582378, baseEnd_5582378] using wordTrace_append hprefix tailTrace_5582378
  have hstable : (prefixWord ++ tailWord_5582378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5582378).length < 2 ^ (prefixWord ++ tailWord_5582378).sum := by decide
  have hdescent : baseEnd_5582378 < baseStart_5582378 := by decide
  rcases family_descends (prefixWord ++ tailWord_5582378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5582384 : List Nat := [2, 1, 1, 1, 2, 3, 1, 5, 1, 6]
def baseStart_5582384 : Nat := 118140960795 + 5582384 * 2 ^ 59
def prefixEnd_5582384 : Nat := 4983230072969 + 3 ^ 40 * 5582384 * 2
def baseEnd_5582384 : Nat := 955482063322864043542363

theorem tailTrace_5582384 : CollatzResearch.WordTrace tailWord_5582384 prefixEnd_5582384 955482063322864043542363 := by
  unfold tailWord_5582384
  simp only [CollatzResearch.WordTrace]
  refine ⟨101803135703991819064317103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135737514271989092085756137 101803135703991819064317103)
  ·
    refine ⟨152704703555987728596475655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101803135703991819064317103 152704703555987728596475655)
    ·
      refine ⟨229057055333981592894713483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152704703555987728596475655 229057055333981592894713483)
      ·
        refine ⟨343585583000972389342070225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229057055333981592894713483 343585583000972389342070225)
        ·
          refine ⟨257689187250729292006552669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 343585583000972389342070225 257689187250729292006552669)
          ·
            refine ⟨96633445219023484502457251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 257689187250729292006552669 96633445219023484502457251)
            ·
              refine ⟨144950167828535226753685877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96633445219023484502457251 144950167828535226753685877)
              ·
                refine ⟨13589078233925177508158051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 144950167828535226753685877 13589078233925177508158051)
                ·
                  refine ⟨20383617350887766262237077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13589078233925177508158051 20383617350887766262237077)
                  ·
                    refine ⟨955482063322864043542363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20383617350887766262237077 955482063322864043542363)
                    ·
                      rfl

theorem cell23_5582384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 5, 1, 6].length) (baseStart_5582384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5582384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5582384 prefixEnd_5582384 := by exact prefixLift 5582384
  have htrace : WordTrace (prefixWord ++ tailWord_5582384) baseStart_5582384 baseEnd_5582384 := by
    simpa [prefixWord, tailWord_5582384, baseEnd_5582384] using wordTrace_append hprefix tailTrace_5582384
  have hstable : (prefixWord ++ tailWord_5582384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5582384).length < 2 ^ (prefixWord ++ tailWord_5582384).sum := by decide
  have hdescent : baseEnd_5582384 < baseStart_5582384 := by decide
  rcases family_descends (prefixWord ++ tailWord_5582384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5582391 : List Nat := [1, 1, 3, 1, 2, 5, 1, 1, 3, 1, 4]
def baseStart_5582391 : Nat := 118140960795 + 5582391 * 2 ^ 59
def prefixEnd_5582391 : Nat := 4983230072969 + 3 ^ 40 * 5582391 * 2
def baseEnd_5582391 : Nat := 2866449784333173603239557

theorem tailTrace_5582391 : CollatzResearch.WordTrace tailWord_5582391 prefixEnd_5582391 2866449784333173603239557 := by
  unfold tailWord_5582391
  simp only [CollatzResearch.WordTrace]
  refine ⟨203606526718958278324139027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135737684479305518882759351 203606526718958278324139027)
  ·
    refine ⟨305409790078437417486208541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203606526718958278324139027 305409790078437417486208541)
    ·
      refine ⟨114528671279414031557328203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 305409790078437417486208541 114528671279414031557328203)
      ·
        refine ⟨171793006919121047335992305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114528671279414031557328203 171793006919121047335992305)
        ·
          refine ⟨128844755189340785501994229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171793006919121047335992305 128844755189340785501994229)
          ·
            refine ⟨12079195799000698640811959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 128844755189340785501994229 12079195799000698640811959)
            ·
              refine ⟨18118793698501047961217939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12079195799000698640811959 18118793698501047961217939)
              ·
                refine ⟨27178190547751571941826909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18118793698501047961217939 27178190547751571941826909)
                ·
                  refine ⟨10191821455406839478185091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27178190547751571941826909 10191821455406839478185091)
                  ·
                    refine ⟨15287732183110259217277637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10191821455406839478185091 15287732183110259217277637)
                    ·
                      refine ⟨2866449784333173603239557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15287732183110259217277637 2866449784333173603239557)
                      ·
                        rfl

theorem cell23_5582391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 1, 3, 1, 4].length) (baseStart_5582391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5582391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5582391 prefixEnd_5582391 := by exact prefixLift 5582391
  have htrace : WordTrace (prefixWord ++ tailWord_5582391) baseStart_5582391 baseEnd_5582391 := by
    simpa [prefixWord, tailWord_5582391, baseEnd_5582391] using wordTrace_append hprefix tailTrace_5582391
  have hstable : (prefixWord ++ tailWord_5582391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5582391).length < 2 ^ (prefixWord ++ tailWord_5582391).sum := by decide
  have hdescent : baseEnd_5582391 < baseStart_5582391 := by decide
  rcases family_descends (prefixWord ++ tailWord_5582391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5582401 : List Nat := [1, 2, 5, 1, 1, 1, 3, 2, 1, 6]
def baseStart_5582401 : Nat := 118140960795 + 5582401 * 2 ^ 59
def prefixEnd_5582401 : Nat := 4983230072969 + 3 ^ 40 * 5582401 * 2
def baseEnd_5582401 : Nat := 955484973046572854704837

theorem tailTrace_5582401 : CollatzResearch.WordTrace tailWord_5582401 prefixEnd_5582401 955484973046572854704837 := by
  unfold tailWord_5582401
  simp only [CollatzResearch.WordTrace]
  refine ⟨203606891448922050032003057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135737927632614700021335371 203606891448922050032003057)
  ·
    refine ⟨152705168586691537524002293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203606891448922050032003057 152705168586691537524002293)
    ·
      refine ⟨14316109555002331642875215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 152705168586691537524002293 14316109555002331642875215)
      ·
        refine ⟨21474164332503497464312823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14316109555002331642875215 21474164332503497464312823)
        ·
          refine ⟨32211246498755246196469235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21474164332503497464312823 32211246498755246196469235)
          ·
            refine ⟨48316869748132869294703853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32211246498755246196469235 48316869748132869294703853)
            ·
              refine ⟨18118826155549825985513945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48316869748132869294703853 18118826155549825985513945)
              ·
                refine ⟨13589119616662369489135459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18118826155549825985513945 13589119616662369489135459)
                ·
                  refine ⟨20383679424993554233703189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13589119616662369489135459 20383679424993554233703189)
                  ·
                    refine ⟨955484973046572854704837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20383679424993554233703189 955484973046572854704837)
                    ·
                      rfl

theorem cell23_5582401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_5582401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5582401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5582401 prefixEnd_5582401 := by exact prefixLift 5582401
  have htrace : WordTrace (prefixWord ++ tailWord_5582401) baseStart_5582401 baseEnd_5582401 := by
    simpa [prefixWord, tailWord_5582401, baseEnd_5582401] using wordTrace_append hprefix tailTrace_5582401
  have hstable : (prefixWord ++ tailWord_5582401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5582401).length < 2 ^ (prefixWord ++ tailWord_5582401).sum := by decide
  have hdescent : baseEnd_5582401 < baseStart_5582401 := by decide
  rcases family_descends (prefixWord ++ tailWord_5582401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5582418 : List Nat := [3, 2, 2, 1, 2, 2, 1, 4, 2, 4]
def baseStart_5582418 : Nat := 118140960795 + 5582418 * 2 ^ 59
def prefixEnd_5582418 : Nat := 4983230072969 + 3 ^ 40 * 5582418 * 2
def baseEnd_5582418 : Nat := 955487882770281665867311

theorem tailTrace_5582418 : CollatzResearch.WordTrace tailWord_5582418 prefixEnd_5582418 955487882770281665867311 := by
  unfold tailWord_5582418
  simp only [CollatzResearch.WordTrace]
  refine ⟨50901877872465115483842977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135738340993240307956914605 50901877872465115483842977)
  ·
    refine ⟨38176408404348836612882233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50901877872465115483842977 38176408404348836612882233)
    ·
      refine ⟨28632306303261627459661675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38176408404348836612882233 28632306303261627459661675)
      ·
        refine ⟨42948459454892441189492513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28632306303261627459661675 42948459454892441189492513)
        ·
          refine ⟨32211344591169330892119385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42948459454892441189492513 32211344591169330892119385)
          ·
            refine ⟨24158508443376998169089539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32211344591169330892119385 24158508443376998169089539)
            ·
              refine ⟨36237762665065497253634309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24158508443376998169089539 36237762665065497253634309)
              ·
                refine ⟨6794580499699780735056433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36237762665065497253634309 6794580499699780735056433)
                ·
                  refine ⟨5095935374774835551292325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6794580499699780735056433 5095935374774835551292325)
                  ·
                    refine ⟨955487882770281665867311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5095935374774835551292325 955487882770281665867311)
                    ·
                      rfl

theorem cell23_5582418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 4, 2, 4].length) (baseStart_5582418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5582418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5582418 prefixEnd_5582418 := by exact prefixLift 5582418
  have htrace : WordTrace (prefixWord ++ tailWord_5582418) baseStart_5582418 baseEnd_5582418 := by
    simpa [prefixWord, tailWord_5582418, baseEnd_5582418] using wordTrace_append hprefix tailTrace_5582418
  have hstable : (prefixWord ++ tailWord_5582418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5582418).length < 2 ^ (prefixWord ++ tailWord_5582418).sum := by decide
  have hdescent : baseEnd_5582418 < baseStart_5582418 := by decide
  rcases family_descends (prefixWord ++ tailWord_5582418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5582428 : List Nat := [2, 2, 4, 1, 2, 1, 1, 2, 3, 2, 3]
def baseStart_5582428 : Nat := 118140960795 + 5582428 * 2 ^ 59
def prefixEnd_5582428 : Nat := 4983230072969 + 3 ^ 40 * 5582428 * 2
def baseEnd_5582428 : Nat := 2866468783117389958476887

theorem tailTrace_5582428 : CollatzResearch.WordTrace tailWord_5582428 prefixEnd_5582428 2866468783117389958476887 := by
  unfold tailWord_5582428
  simp only [CollatzResearch.WordTrace]
  refine ⟨101803938109912116821617969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135738584146549489095490625 101803938109912116821617969)
  ·
    refine ⟨76352953582434087616213477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101803938109912116821617969 76352953582434087616213477)
    ·
      refine ⟨14316178796706391428040027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76352953582434087616213477 14316178796706391428040027)
      ·
        refine ⟨21474268195059587142060041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14316178796706391428040027 21474268195059587142060041)
        ·
          refine ⟨16105701146294690356545031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21474268195059587142060041 16105701146294690356545031)
          ·
            refine ⟨24158551719442035534817547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16105701146294690356545031 24158551719442035534817547)
            ·
              refine ⟨36237827579163053302226321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24158551719442035534817547 36237827579163053302226321)
              ·
                refine ⟨27178370684372289976669741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36237827579163053302226321 27178370684372289976669741)
                ·
                  refine ⟨10191889006639608741251153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27178370684372289976669741 10191889006639608741251153)
                  ·
                    refine ⟨7643916754979706555938365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10191889006639608741251153 7643916754979706555938365)
                    ·
                      refine ⟨2866468783117389958476887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7643916754979706555938365 2866468783117389958476887)
                      ·
                        rfl

theorem cell23_5582428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 2, 3, 2, 3].length) (baseStart_5582428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5582428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5582428 prefixEnd_5582428 := by exact prefixLift 5582428
  have htrace : WordTrace (prefixWord ++ tailWord_5582428) baseStart_5582428 baseEnd_5582428 := by
    simpa [prefixWord, tailWord_5582428, baseEnd_5582428] using wordTrace_append hprefix tailTrace_5582428
  have hstable : (prefixWord ++ tailWord_5582428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5582428).length < 2 ^ (prefixWord ++ tailWord_5582428).sum := by decide
  have hdescent : baseEnd_5582428 < baseStart_5582428 := by decide
  rcases family_descends (prefixWord ++ tailWord_5582428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5582441 : List Nat := [1, 2, 1, 1, 1, 4, 3, 3, 1, 3, 3]
def baseStart_5582441 : Nat := 118140960795 + 5582441 * 2 ^ 59
def prefixEnd_5582441 : Nat := 4983230072969 + 3 ^ 40 * 5582441 * 2
def baseEnd_5582441 : Nat := 2866475458365898407614327

theorem tailTrace_5582441 : CollatzResearch.WordTrace tailWord_5582441 prefixEnd_5582441 2866475458365898407614327 := by
  unfold tailWord_5582441
  simp only [CollatzResearch.WordTrace]
  refine ⟨203608350368777136863459177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135738900245851424575639451 203608350368777136863459177)
  ·
    refine ⟨152706262776582852647594383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203608350368777136863459177 152706262776582852647594383)
    ·
      refine ⟨229059394164874278971391575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152706262776582852647594383 229059394164874278971391575)
      ·
        refine ⟨343589091247311418457087363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229059394164874278971391575 343589091247311418457087363)
        ·
          refine ⟨515383636870967127685631045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 343589091247311418457087363 515383636870967127685631045)
          ·
            refine ⟨96634431913306336441055821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 515383636870967127685631045 96634431913306336441055821)
            ·
              refine ⟨36237911967489876165395933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96634431913306336441055821 36237911967489876165395933)
              ·
                refine ⟨13589216987808703562023475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36237911967489876165395933 13589216987808703562023475)
                ·
                  refine ⟨20383825481713055343035213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13589216987808703562023475 20383825481713055343035213)
                  ·
                    refine ⟨7643934555642395753638205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20383825481713055343035213 7643934555642395753638205)
                    ·
                      refine ⟨2866475458365898407614327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7643934555642395753638205 2866475458365898407614327)
                      ·
                        rfl

theorem cell23_5582441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 3, 1, 3, 3].length) (baseStart_5582441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5582441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5582441 prefixEnd_5582441 := by exact prefixLift 5582441
  have htrace : WordTrace (prefixWord ++ tailWord_5582441) baseStart_5582441 baseEnd_5582441 := by
    simpa [prefixWord, tailWord_5582441, baseEnd_5582441] using wordTrace_append hprefix tailTrace_5582441
  have hstable : (prefixWord ++ tailWord_5582441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5582441).length < 2 ^ (prefixWord ++ tailWord_5582441).sum := by decide
  have hdescent : baseEnd_5582441 < baseStart_5582441 := by decide
  rcases family_descends (prefixWord ++ tailWord_5582441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5582444 : List Nat := [2, 2, 1, 1, 3, 1, 1, 1, 4, 7]
def baseStart_5582444 : Nat := 118140960795 + 5582444 * 2 ^ 59
def prefixEnd_5582444 : Nat := 4983230072969 + 3 ^ 40 * 5582444 * 2
def baseEnd_5582444 : Nat := 955492332935953965292271

theorem tailTrace_5582444 : CollatzResearch.WordTrace tailWord_5582444 prefixEnd_5582444 955492332935953965292271 := by
  unfold tailWord_5582444
  simp only [CollatzResearch.WordTrace]
  refine ⟨101804229893883134187909193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135738973191844178917212257 101804229893883134187909193)
  ·
    refine ⟨76353172420412350640931895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101804229893883134187909193 76353172420412350640931895)
    ·
      refine ⟨114529758630618525961397843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76353172420412350640931895 114529758630618525961397843)
      ·
        refine ⟨171794637945927788942096765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114529758630618525961397843 171794637945927788942096765)
        ·
          refine ⟨64422989229722920853286287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 171794637945927788942096765 64422989229722920853286287)
          ·
            refine ⟨96634483844584381279929431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64422989229722920853286287 96634483844584381279929431)
            ·
              refine ⟨144951725766876571919894147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96634483844584381279929431 144951725766876571919894147)
              ·
                refine ⟨217427588650314857879841221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 144951725766876571919894147 217427588650314857879841221)
                ·
                  refine ⟨40767672871934035852470229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 217427588650314857879841221 40767672871934035852470229)
                  ·
                    refine ⟨955492332935953965292271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40767672871934035852470229 955492332935953965292271)
                    ·
                      rfl

theorem cell23_5582444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 7].length) (baseStart_5582444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5582444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5582444 prefixEnd_5582444 := by exact prefixLift 5582444
  have htrace : WordTrace (prefixWord ++ tailWord_5582444) baseStart_5582444 baseEnd_5582444 := by
    simpa [prefixWord, tailWord_5582444, baseEnd_5582444] using wordTrace_append hprefix tailTrace_5582444
  have hstable : (prefixWord ++ tailWord_5582444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5582444).length < 2 ^ (prefixWord ++ tailWord_5582444).sum := by decide
  have hdescent : baseEnd_5582444 < baseStart_5582444 := by decide
  rcases family_descends (prefixWord ++ tailWord_5582444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5582492 : List Nat := [2, 2, 3, 2, 4, 1, 1, 1, 1, 3, 3]
def baseStart_5582492 : Nat := 118140960795 + 5582492 * 2 ^ 59
def prefixEnd_5582492 : Nat := 4983230072969 + 3 ^ 40 * 5582492 * 2
def baseEnd_5582492 : Nat := 2866501645879277708076593

theorem tailTrace_5582492 : CollatzResearch.WordTrace tailWord_5582492 prefixEnd_5582492 2866501645879277708076593 := by
  unfold tailWord_5582492
  simp only [CollatzResearch.WordTrace]
  refine ⟨101805105245796186286782865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135740140327728248382377153 101805105245796186286782865)
  ·
    refine ⟨76353828934347139715087149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101805105245796186286782865 76353828934347139715087149)
    ·
      refine ⟨28632685850380177393157681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76353828934347139715087149 28632685850380177393157681)
      ·
        refine ⟨21474514387785133044868261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28632685850380177393157681 21474514387785133044868261)
        ·
          refine ⟨4026471447709712445912799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21474514387785133044868261 4026471447709712445912799)
          ·
            refine ⟨6039707171564568668869199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4026471447709712445912799 6039707171564568668869199)
            ·
              refine ⟨9059560757346853003303799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6039707171564568668869199 9059560757346853003303799)
              ·
                refine ⟨13589341136020279504955699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9059560757346853003303799 13589341136020279504955699)
                ·
                  refine ⟨20384011704030419257433549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13589341136020279504955699 20384011704030419257433549)
                  ·
                    refine ⟨7644004389011407221537581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20384011704030419257433549 7644004389011407221537581)
                    ·
                      refine ⟨2866501645879277708076593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7644004389011407221537581 2866501645879277708076593)
                      ·
                        rfl

theorem cell23_5582492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 1, 1, 3, 3].length) (baseStart_5582492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5582492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5582492 prefixEnd_5582492 := by exact prefixLift 5582492
  have htrace : WordTrace (prefixWord ++ tailWord_5582492) baseStart_5582492 baseEnd_5582492 := by
    simpa [prefixWord, tailWord_5582492, baseEnd_5582492] using wordTrace_append hprefix tailTrace_5582492
  have hstable : (prefixWord ++ tailWord_5582492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5582492).length < 2 ^ (prefixWord ++ tailWord_5582492).sum := by decide
  have hdescent : baseEnd_5582492 < baseStart_5582492 := by decide
  rcases family_descends (prefixWord ++ tailWord_5582492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5582501 : List Nat := [1, 3, 1, 2, 1, 2, 2, 2, 2, 4, 3]
def baseStart_5582501 : Nat := 118140960795 + 5582501 * 2 ^ 59
def prefixEnd_5582501 : Nat := 4983230072969 + 3 ^ 40 * 5582501 * 2
def baseEnd_5582501 : Nat := 2866506267205168172864051

theorem tailTrace_5582501 : CollatzResearch.WordTrace tailWord_5582501 prefixEnd_5582501 2866506267205168172864051 := by
  unfold tailWord_5582501
  simp only [CollatzResearch.WordTrace]
  refine ⟨203610538748559767110643357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135740359165706511407095571 203610538748559767110643357)
  ·
    refine ⟨76353952030709912666491259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 203610538748559767110643357 76353952030709912666491259)
    ·
      refine ⟨114530928046064868999736889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76353952030709912666491259 114530928046064868999736889)
      ·
        refine ⟨85898196034548651749802667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114530928046064868999736889 85898196034548651749802667)
        ·
          refine ⟨128847294051822977624704001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85898196034548651749802667 128847294051822977624704001)
          ·
            refine ⟨96635470538867233218528001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128847294051822977624704001 96635470538867233218528001)
            ·
              refine ⟨72476602904150424913896001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96635470538867233218528001 72476602904150424913896001)
              ·
                refine ⟨54357452178112818685422001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72476602904150424913896001 54357452178112818685422001)
                ·
                  refine ⟨40768089133584614014066501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54357452178112818685422001 40768089133584614014066501)
                  ·
                    refine ⟨7644016712547115127637469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40768089133584614014066501 7644016712547115127637469)
                    ·
                      refine ⟨2866506267205168172864051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7644016712547115127637469 2866506267205168172864051)
                      ·
                        rfl

theorem cell23_5582501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 2, 2, 4, 3].length) (baseStart_5582501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5582501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5582501 prefixEnd_5582501 := by exact prefixLift 5582501
  have htrace : WordTrace (prefixWord ++ tailWord_5582501) baseStart_5582501 baseEnd_5582501 := by
    simpa [prefixWord, tailWord_5582501, baseEnd_5582501] using wordTrace_append hprefix tailTrace_5582501
  have hstable : (prefixWord ++ tailWord_5582501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5582501).length < 2 ^ (prefixWord ++ tailWord_5582501).sum := by decide
  have hdescent : baseEnd_5582501 < baseStart_5582501 := by decide
  rcases family_descends (prefixWord ++ tailWord_5582501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5582532 : List Nat := [2, 3, 3, 1, 1, 1, 2, 4, 2, 2, 2]
def baseStart_5582532 : Nat := 118140960795 + 5582532 * 2 ^ 59
def prefixEnd_5582532 : Nat := 4983230072969 + 3 ^ 40 * 5582532 * 2
def baseEnd_5582532 : Nat := 2866522185105457551576409

theorem tailTrace_5582532 : CollatzResearch.WordTrace tailWord_5582532 prefixEnd_5582532 2866522185105457551576409 := by
  unfold tailWord_5582532
  simp only [CollatzResearch.WordTrace]
  refine ⟨101805834705723729702510925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135741112940964972936681233 101805834705723729702510925)
  ·
    refine ⟨38177188014646398638441597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101805834705723729702510925 38177188014646398638441597)
    ·
      refine ⟨14316445505492399489415599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38177188014646398638441597 14316445505492399489415599)
      ·
        refine ⟨21474668258238599234123399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14316445505492399489415599 21474668258238599234123399)
        ·
          refine ⟨32212002387357898851185099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21474668258238599234123399 32212002387357898851185099)
          ·
            refine ⟨48318003581036848276777649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32212002387357898851185099 48318003581036848276777649)
            ·
              refine ⟨36238502685777636207583237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48318003581036848276777649 36238502685777636207583237)
              ·
                refine ⟨6794719253583306788921857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36238502685777636207583237 6794719253583306788921857)
                ·
                  refine ⟨5096039440187480091691393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6794719253583306788921857 5096039440187480091691393)
                  ·
                    refine ⟨3822029580140610068768545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5096039440187480091691393 3822029580140610068768545)
                    ·
                      refine ⟨2866522185105457551576409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3822029580140610068768545 2866522185105457551576409)
                      ·
                        rfl

theorem cell23_5582532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 4, 2, 2, 2].length) (baseStart_5582532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5582532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5582532 prefixEnd_5582532 := by exact prefixLift 5582532
  have htrace : WordTrace (prefixWord ++ tailWord_5582532) baseStart_5582532 baseEnd_5582532 := by
    simpa [prefixWord, tailWord_5582532, baseEnd_5582532] using wordTrace_append hprefix tailTrace_5582532
  have hstable : (prefixWord ++ tailWord_5582532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5582532).length < 2 ^ (prefixWord ++ tailWord_5582532).sum := by decide
  have hdescent : baseEnd_5582532 < baseStart_5582532 := by decide
  rcases family_descends (prefixWord ++ tailWord_5582532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5582551 : List Nat := [1, 1, 3, 2, 1, 3, 1, 2, 4, 5]
def baseStart_5582551 : Nat := 118140960795 + 5582551 * 2 ^ 59
def prefixEnd_5582551 : Nat := 4983230072969 + 3 ^ 40 * 5582551 * 2
def baseEnd_5582551 : Nat := 955510647079297659079607

theorem tailTrace_5582551 : CollatzResearch.WordTrace tailWord_5582551 prefixEnd_5582551 955510647079297659079607 := by
  unfold tailWord_5582551
  simp only [CollatzResearch.WordTrace]
  refine ⟨203612362398378625649963507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135741574932252417099975671 203612362398378625649963507)
  ·
    refine ⟨305418543597567938474945261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203612362398378625649963507 305418543597567938474945261)
    ·
      refine ⟨114531953849087976928104473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 305418543597567938474945261 114531953849087976928104473)
      ·
        refine ⟨85898965386815982696078355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114531953849087976928104473 85898965386815982696078355)
        ·
          refine ⟨128848448080223974044117533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85898965386815982696078355 128848448080223974044117533)
          ·
            refine ⟨48318168030083990266544075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 128848448080223974044117533 48318168030083990266544075)
            ·
              refine ⟨72477252045125985399816113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48318168030083990266544075 72477252045125985399816113)
              ·
                refine ⟨54357939033844489049862085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72477252045125985399816113 54357939033844489049862085)
                ·
                  refine ⟨10192113568845841696849141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54357939033844489049862085 10192113568845841696849141)
                  ·
                    refine ⟨955510647079297659079607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10192113568845841696849141 955510647079297659079607)
                    ·
                      rfl

theorem cell23_5582551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 2, 4, 5].length) (baseStart_5582551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5582551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5582551 prefixEnd_5582551 := by exact prefixLift 5582551
  have htrace : WordTrace (prefixWord ++ tailWord_5582551) baseStart_5582551 baseEnd_5582551 := by
    simpa [prefixWord, tailWord_5582551, baseEnd_5582551] using wordTrace_append hprefix tailTrace_5582551
  have hstable : (prefixWord ++ tailWord_5582551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5582551).length < 2 ^ (prefixWord ++ tailWord_5582551).sum := by decide
  have hdescent : baseEnd_5582551 < baseStart_5582551 := by decide
  rcases family_descends (prefixWord ++ tailWord_5582551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5582568 : List Nat := [2, 1, 4, 1, 3, 1, 1, 3, 2, 5]
def baseStart_5582568 : Nat := 118140960795 + 5582568 * 2 ^ 59
def prefixEnd_5582568 : Nat := 4983230072969 + 3 ^ 40 * 5582568 * 2
def baseEnd_5582568 : Nat := 955513556803006470242081

theorem tailTrace_5582568 : CollatzResearch.WordTrace tailWord_5582568 prefixEnd_5582568 955513556803006470242081 := by
  unfold tailWord_5582568
  simp only [CollatzResearch.WordTrace]
  refine ⟨101806491219658518776666179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135741988292878025035554905 101806491219658518776666179)
  ·
    refine ⟨152709736829487778164999269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101806491219658518776666179 152709736829487778164999269)
    ·
      refine ⟨28633075655528958405937363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 152709736829487778164999269 28633075655528958405937363)
      ·
        refine ⟨42949613483293437608906045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28633075655528958405937363 42949613483293437608906045)
        ·
          refine ⟨16106105056235039103339767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42949613483293437608906045 16106105056235039103339767)
          ·
            refine ⟨24159157584352558655009651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16106105056235039103339767 24159157584352558655009651)
            ·
              refine ⟨36238736376528837982514477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24159157584352558655009651 36238736376528837982514477)
              ·
                refine ⟨13589526141198314243442929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36238736376528837982514477 13589526141198314243442929)
                ·
                  refine ⟨10192144605898735682582197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13589526141198314243442929 10192144605898735682582197)
                  ·
                    refine ⟨955513556803006470242081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10192144605898735682582197 955513556803006470242081)
                    ·
                      rfl

theorem cell23_5582568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 3, 2, 5].length) (baseStart_5582568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5582568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5582568 prefixEnd_5582568 := by exact prefixLift 5582568
  have htrace : WordTrace (prefixWord ++ tailWord_5582568) baseStart_5582568 baseEnd_5582568 := by
    simpa [prefixWord, tailWord_5582568, baseEnd_5582568] using wordTrace_append hprefix tailTrace_5582568
  have hstable : (prefixWord ++ tailWord_5582568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5582568).length < 2 ^ (prefixWord ++ tailWord_5582568).sum := by decide
  have hdescent : baseEnd_5582568 < baseStart_5582568 := by decide
  rcases family_descends (prefixWord ++ tailWord_5582568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5582571 : List Nat := [1, 1, 1, 1, 2, 4, 2, 3, 1, 3, 4]
def baseStart_5582571 : Nat := 118140960795 + 5582571 * 2 ^ 59
def prefixEnd_5582571 : Nat := 4983230072969 + 3 ^ 40 * 5582571 * 2
def baseEnd_5582571 : Nat := 2866542210850982898988729

theorem tailTrace_5582571 : CollatzResearch.WordTrace tailWord_5582571 prefixEnd_5582571 2866542210850982898988729 := by
  unfold tailWord_5582571
  simp only [CollatzResearch.WordTrace]
  refine ⟨203613091858306169065691567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135742061238870779377127711 203613091858306169065691567)
  ·
    refine ⟨305419637787459253598537351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203613091858306169065691567 305419637787459253598537351)
    ·
      refine ⟨458129456681188880397806027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305419637787459253598537351 458129456681188880397806027)
      ·
        refine ⟨687194185021783320596709041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 458129456681188880397806027 687194185021783320596709041)
        ·
          refine ⟨515395638766337490447531781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 687194185021783320596709041 515395638766337490447531781)
          ·
            refine ⟨96636682268688279458912209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 515395638766337490447531781 96636682268688279458912209)
            ·
              refine ⟨72477511701516209594184157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96636682268688279458912209 72477511701516209594184157)
              ·
                refine ⟨27179066888068578597819059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72477511701516209594184157 27179066888068578597819059)
                ·
                  refine ⟨40768600332102867896728589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27179066888068578597819059 40768600332102867896728589)
                  ·
                    refine ⟨15288225124538575461273221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40768600332102867896728589 15288225124538575461273221)
                    ·
                      refine ⟨2866542210850982898988729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15288225124538575461273221 2866542210850982898988729)
                      ·
                        rfl

theorem cell23_5582571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 3, 1, 3, 4].length) (baseStart_5582571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5582571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5582571 prefixEnd_5582571 := by exact prefixLift 5582571
  have htrace : WordTrace (prefixWord ++ tailWord_5582571) baseStart_5582571 baseEnd_5582571 := by
    simpa [prefixWord, tailWord_5582571, baseEnd_5582571] using wordTrace_append hprefix tailTrace_5582571
  have hstable : (prefixWord ++ tailWord_5582571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5582571).length < 2 ^ (prefixWord ++ tailWord_5582571).sum := by decide
  have hdescent : baseEnd_5582571 < baseStart_5582571 := by decide
  rcases family_descends (prefixWord ++ tailWord_5582571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5582588 : List Nat := [2, 2, 2, 1, 3, 1, 1, 4, 2, 1, 4]
def baseStart_5582588 : Nat := 118140960795 + 5582588 * 2 ^ 59
def prefixEnd_5582588 : Nat := 4983230072969 + 3 ^ 40 * 5582588 * 2
def baseEnd_5582588 : Nat := 2866550940022109332476151

theorem tailTrace_5582588 : CollatzResearch.WordTrace tailWord_5582588 prefixEnd_5582588 2866550940022109332476151 := by
  unfold tailWord_5582588
  simp only [CollatzResearch.WordTrace]
  refine ⟨101806855949622290484530209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135742474599496387312706945 101806855949622290484530209)
  ·
    refine ⟨76355141962216717863397657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101806855949622290484530209 76355141962216717863397657)
    ·
      refine ⟨57266356471662538397548243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76355141962216717863397657 57266356471662538397548243)
      ·
        refine ⟨85899534707493807596322365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57266356471662538397548243 85899534707493807596322365)
        ·
          refine ⟨32212325515310177848620887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85899534707493807596322365 32212325515310177848620887)
          ·
            refine ⟨48318488272965266772931331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32212325515310177848620887 48318488272965266772931331)
            ·
              refine ⟨72477732409447900159396997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48318488272965266772931331 72477732409447900159396997)
              ·
                refine ⟨13589574826771481279886937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72477732409447900159396997 13589574826771481279886937)
                ·
                  refine ⟨10192181120078610959915203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13589574826771481279886937 10192181120078610959915203)
                  ·
                    refine ⟨15288271680117916439872805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10192181120078610959915203 15288271680117916439872805)
                    ·
                      refine ⟨2866550940022109332476151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15288271680117916439872805 2866550940022109332476151)
                      ·
                        rfl

theorem cell23_5582588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 4, 2, 1, 4].length) (baseStart_5582588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5582588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5582588 prefixEnd_5582588 := by exact prefixLift 5582588
  have htrace : WordTrace (prefixWord ++ tailWord_5582588) baseStart_5582588 baseEnd_5582588 := by
    simpa [prefixWord, tailWord_5582588, baseEnd_5582588] using wordTrace_append hprefix tailTrace_5582588
  have hstable : (prefixWord ++ tailWord_5582588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5582588).length < 2 ^ (prefixWord ++ tailWord_5582588).sum := by decide
  have hdescent : baseEnd_5582588 < baseStart_5582588 := by decide
  rcases family_descends (prefixWord ++ tailWord_5582588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5582601 : List Nat := [1, 2, 1, 1, 3, 2, 1, 2, 2, 4, 4]
def baseStart_5582601 : Nat := 118140960795 + 5582601 * 2 ^ 59
def prefixEnd_5582601 : Nat := 4983230072969 + 3 ^ 40 * 5582601 * 2
def baseEnd_5582601 : Nat := 2866557615270617781613591

theorem tailTrace_5582601 : CollatzResearch.WordTrace tailWord_5582601 prefixEnd_5582601 2866557615270617781613591 := by
  unfold tailWord_5582601
  simp only [CollatzResearch.WordTrace]
  refine ⟨203614186048197484189283657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135742790698798322792855771 203614186048197484189283657)
  ·
    refine ⟨152710639536148113141962743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203614186048197484189283657 152710639536148113141962743)
    ·
      refine ⟨229065959304222169712944115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152710639536148113141962743 229065959304222169712944115)
      ·
        refine ⟨343598938956333254569416173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229065959304222169712944115 343598938956333254569416173)
        ·
          refine ⟨128849602108624970463531065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 343598938956333254569416173 128849602108624970463531065)
          ·
            refine ⟨96637201581468727847648299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128849602108624970463531065 96637201581468727847648299)
            ·
              refine ⟨144955802372203091771472449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96637201581468727847648299 144955802372203091771472449)
              ·
                refine ⟨108716851779152318828604337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 144955802372203091771472449 108716851779152318828604337)
                ·
                  refine ⟨81537638834364239121453253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 108716851779152318828604337 81537638834364239121453253)
                  ·
                    refine ⟨15288307281443294835272485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 81537638834364239121453253 15288307281443294835272485)
                    ·
                      refine ⟨2866557615270617781613591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15288307281443294835272485 2866557615270617781613591)
                      ·
                        rfl

theorem cell23_5582601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 2, 4, 4].length) (baseStart_5582601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5582601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5582601 prefixEnd_5582601 := by exact prefixLift 5582601
  have htrace : WordTrace (prefixWord ++ tailWord_5582601) baseStart_5582601 baseEnd_5582601 := by
    simpa [prefixWord, tailWord_5582601, baseEnd_5582601] using wordTrace_append hprefix tailTrace_5582601
  have hstable : (prefixWord ++ tailWord_5582601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5582601).length < 2 ^ (prefixWord ++ tailWord_5582601).sum := by decide
  have hdescent : baseEnd_5582601 < baseStart_5582601 := by decide
  rcases family_descends (prefixWord ++ tailWord_5582601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5582615 : List Nat := [1, 1, 3, 4, 2, 2, 1, 2, 3, 4]
def baseStart_5582615 : Nat := 118140960795 + 5582615 * 2 ^ 59
def prefixEnd_5582615 : Nat := 4983230072969 + 3 ^ 40 * 5582615 * 2
def baseEnd_5582615 : Nat := 955521601333260242279509

theorem tailTrace_5582615 : CollatzResearch.WordTrace tailWord_5582615 prefixEnd_5582615 955521601333260242279509 := by
  unfold tailWord_5582615
  simp only [CollatzResearch.WordTrace]
  refine ⟨203614696670146764580293299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135743131113431176386862199 203614696670146764580293299)
  ·
    refine ⟨305422045005220146870439949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203614696670146764580293299 305422045005220146870439949)
    ·
      refine ⟨114533266876957555076414981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 305422045005220146870439949 114533266876957555076414981)
      ·
        refine ⟨21474987539429541576827809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 114533266876957555076414981 21474987539429541576827809)
        ·
          refine ⟨16106240654572156182620857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21474987539429541576827809 16106240654572156182620857)
          ·
            refine ⟨12079680490929117136965643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16106240654572156182620857 12079680490929117136965643)
            ·
              refine ⟨18119520736393675705448465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12079680490929117136965643 18119520736393675705448465)
              ·
                refine ⟨13589640552295256779086349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18119520736393675705448465 13589640552295256779086349)
                ·
                  refine ⟨5096115207110721292157381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13589640552295256779086349 5096115207110721292157381)
                  ·
                    refine ⟨955521601333260242279509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5096115207110721292157381 955521601333260242279509)
                    ·
                      rfl

theorem cell23_5582615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 2, 3, 4].length) (baseStart_5582615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5582615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5582615 prefixEnd_5582615 := by exact prefixLift 5582615
  have htrace : WordTrace (prefixWord ++ tailWord_5582615) baseStart_5582615 baseEnd_5582615 := by
    simpa [prefixWord, tailWord_5582615, baseEnd_5582615] using wordTrace_append hprefix tailTrace_5582615
  have hstable : (prefixWord ++ tailWord_5582615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5582615).length < 2 ^ (prefixWord ++ tailWord_5582615).sum := by decide
  have hdescent : baseEnd_5582615 < baseStart_5582615 := by decide
  rcases family_descends (prefixWord ++ tailWord_5582615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5582625 : List Nat := [1, 2, 3, 2, 1, 3, 3, 1, 2, 2, 3]
def baseStart_5582625 : Nat := 118140960795 + 5582625 * 2 ^ 59
def prefixEnd_5582625 : Nat := 4983230072969 + 3 ^ 40 * 5582625 * 2
def baseEnd_5582625 : Nat := 2866569938806325687713481

theorem tailTrace_5582625 : CollatzResearch.WordTrace tailWord_5582625 prefixEnd_5582625 2866569938806325687713481 := by
  unfold tailWord_5582625
  simp only [CollatzResearch.WordTrace]
  refine ⟨203615061400110536288157329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135743374266740357525438219 203615061400110536288157329)
  ·
    refine ⟨152711296050082902216117997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203615061400110536288157329 152711296050082902216117997)
    ·
      refine ⟨57266736018781088331044249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152711296050082902216117997 57266736018781088331044249)
      ·
        refine ⟨42950052014085816248283187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57266736018781088331044249 42950052014085816248283187)
        ·
          refine ⟨64425078021128724372424781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42950052014085816248283187 64425078021128724372424781)
          ·
            refine ⟨24159404257923271639659293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64425078021128724372424781 24159404257923271639659293)
            ·
              refine ⟨9059776596721226864872235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24159404257923271639659293 9059776596721226864872235)
              ·
                refine ⟨13589664895081840297308353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9059776596721226864872235 13589664895081840297308353)
                ·
                  refine ⟨10192248671311380222981265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13589664895081840297308353 10192248671311380222981265)
                  ·
                    refine ⟨7644186503483535167235949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10192248671311380222981265 7644186503483535167235949)
                    ·
                      refine ⟨2866569938806325687713481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7644186503483535167235949 2866569938806325687713481)
                      ·
                        rfl

theorem cell23_5582625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 1, 2, 2, 3].length) (baseStart_5582625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5582625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5582625 prefixEnd_5582625 := by exact prefixLift 5582625
  have htrace : WordTrace (prefixWord ++ tailWord_5582625) baseStart_5582625 baseEnd_5582625 := by
    simpa [prefixWord, tailWord_5582625, baseEnd_5582625] using wordTrace_append hprefix tailTrace_5582625
  have hstable : (prefixWord ++ tailWord_5582625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5582625).length < 2 ^ (prefixWord ++ tailWord_5582625).sum := by decide
  have hdescent : baseEnd_5582625 < baseStart_5582625 := by decide
  rcases family_descends (prefixWord ++ tailWord_5582625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5582632 : List Nat := [2, 1, 5, 1, 1, 2, 1, 5, 1, 4]
def baseStart_5582632 : Nat := 118140960795 + 5582632 * 2 ^ 59
def prefixEnd_5582632 : Nat := 4983230072969 + 3 ^ 40 * 5582632 * 2
def baseEnd_5582632 : Nat := 955524511056969053441983

theorem tailTrace_5582632 : CollatzResearch.WordTrace tailWord_5582632 prefixEnd_5582632 955524511056969053441983 := by
  unfold tailWord_5582632
  simp only [CollatzResearch.WordTrace]
  refine ⟨101807658355542588241831075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135743544474056784322441433 101807658355542588241831075)
  ·
    refine ⟨152711487533313882362746613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101807658355542588241831075 152711487533313882362746613)
    ·
      refine ⟨14316701956248176471507495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 152711487533313882362746613 14316701956248176471507495)
      ·
        refine ⟨21475052934372264707261243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14316701956248176471507495 21475052934372264707261243)
        ·
          refine ⟨32212579401558397060891865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21475052934372264707261243 32212579401558397060891865)
          ·
            refine ⟨24159434551168797795668899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32212579401558397060891865 24159434551168797795668899)
            ·
              refine ⟨36239151826753196693503349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24159434551168797795668899 36239151826753196693503349)
              ·
                refine ⟨3397420483758112190015939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36239151826753196693503349 3397420483758112190015939)
                ·
                  refine ⟨5096130725637168285023909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3397420483758112190015939 5096130725637168285023909)
                  ·
                    refine ⟨955524511056969053441983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5096130725637168285023909 955524511056969053441983)
                    ·
                      rfl

theorem cell23_5582632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 5, 1, 4].length) (baseStart_5582632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5582632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5582632 prefixEnd_5582632 := by exact prefixLift 5582632
  have htrace : WordTrace (prefixWord ++ tailWord_5582632) baseStart_5582632 baseEnd_5582632 := by
    simpa [prefixWord, tailWord_5582632, baseEnd_5582632] using wordTrace_append hprefix tailTrace_5582632
  have hstable : (prefixWord ++ tailWord_5582632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5582632).length < 2 ^ (prefixWord ++ tailWord_5582632).sum := by decide
  have hdescent : baseEnd_5582632 < baseStart_5582632 := by decide
  rcases family_descends (prefixWord ++ tailWord_5582632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5582695 : List Nat := [1, 1, 5, 1, 2, 1, 1, 5, 1, 1, 4]
def baseStart_5582695 : Nat := 118140960795 + 5582695 * 2 ^ 59
def prefixEnd_5582695 : Nat := 4983230072969 + 3 ^ 40 * 5582695 * 2
def baseEnd_5582695 : Nat := 2866605882452140413838159

theorem tailTrace_5582695 : CollatzResearch.WordTrace tailWord_5582695 prefixEnd_5582695 2866605882452140413838159 := by
  unfold tailWord_5582695
  simp only [CollatzResearch.WordTrace]
  refine ⟨203617614509856938243205539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135745076339904625495470359 203617614509856938243205539)
  ·
    refine ⟨305426421764785407364808309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203617614509856938243205539 305426421764785407364808309)
    ·
      refine ⟨28633727040448631940450779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 305426421764785407364808309 28633727040448631940450779)
      ·
        refine ⟨42950590560672947910676169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28633727040448631940450779 42950590560672947910676169)
        ·
          refine ⟨32212942920504710933007127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42950590560672947910676169 32212942920504710933007127)
          ·
            refine ⟨48319414380757066399510691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32212942920504710933007127 48319414380757066399510691)
            ·
              refine ⟨72479121571135599599266037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48319414380757066399510691 72479121571135599599266037)
              ·
                refine ⟨6794917647293962462431191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 72479121571135599599266037 6794917647293962462431191)
                ·
                  refine ⟨10192376470940943693646787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6794917647293962462431191 10192376470940943693646787)
                  ·
                    refine ⟨15288564706411415540470181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10192376470940943693646787 15288564706411415540470181)
                    ·
                      refine ⟨2866605882452140413838159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15288564706411415540470181 2866605882452140413838159)
                      ·
                        rfl

theorem cell23_5582695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 5, 1, 1, 4].length) (baseStart_5582695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5582695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5582695 prefixEnd_5582695 := by exact prefixLift 5582695
  have htrace : WordTrace (prefixWord ++ tailWord_5582695) baseStart_5582695 baseEnd_5582695 := by
    simpa [prefixWord, tailWord_5582695, baseEnd_5582695] using wordTrace_append hprefix tailTrace_5582695
  have hstable : (prefixWord ++ tailWord_5582695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5582695).length < 2 ^ (prefixWord ++ tailWord_5582695).sum := by decide
  have hdescent : baseEnd_5582695 < baseStart_5582695 := by decide
  rcases family_descends (prefixWord ++ tailWord_5582695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5582705 : List Nat := [1, 2, 2, 2, 1, 3, 2, 4, 2, 4]
def baseStart_5582705 : Nat := 118140960795 + 5582705 * 2 ^ 59
def prefixEnd_5582705 : Nat := 4983230072969 + 3 ^ 40 * 5582705 * 2
def baseEnd_5582705 : Nat := 955537005752895124904371

theorem tailTrace_5582705 : CollatzResearch.WordTrace tailWord_5582705 prefixEnd_5582705 955537005752895124904371 := by
  unfold tailWord_5582705
  simp only [CollatzResearch.WordTrace]
  refine ⟨203617979239820709951069569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135745319493213806634046379 203617979239820709951069569)
  ·
    refine ⟨152713484429865532463302177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203617979239820709951069569 152713484429865532463302177)
    ·
      refine ⟨114535113322399149347476633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152713484429865532463302177 114535113322399149347476633)
      ·
        refine ⟨85901334991799362010607475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114535113322399149347476633 85901334991799362010607475)
        ·
          refine ⟨128852002487699043015911213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85901334991799362010607475 128852002487699043015911213)
          ·
            refine ⟨48319500932887141130966705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 128852002487699043015911213 48319500932887141130966705)
            ·
              refine ⟨36239625699665355848225029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48319500932887141130966705 36239625699665355848225029)
              ·
                refine ⟨6794929818687254221542193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36239625699665355848225029 6794929818687254221542193)
                ·
                  refine ⟨5096197364015440666156645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6794929818687254221542193 5096197364015440666156645)
                  ·
                    refine ⟨955537005752895124904371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5096197364015440666156645 955537005752895124904371)
                    ·
                      rfl

theorem cell23_5582705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 4, 2, 4].length) (baseStart_5582705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5582705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5582705 prefixEnd_5582705 := by exact prefixLift 5582705
  have htrace : WordTrace (prefixWord ++ tailWord_5582705) baseStart_5582705 baseEnd_5582705 := by
    simpa [prefixWord, tailWord_5582705, baseEnd_5582705] using wordTrace_append hprefix tailTrace_5582705
  have hstable : (prefixWord ++ tailWord_5582705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5582705).length < 2 ^ (prefixWord ++ tailWord_5582705).sum := by decide
  have hdescent : baseEnd_5582705 < baseStart_5582705 := by decide
  rcases family_descends (prefixWord ++ tailWord_5582705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5582745 : List Nat := [1, 2, 1, 2, 1, 3, 2, 1, 6, 1, 3]
def baseStart_5582745 : Nat := 118140960795 + 5582745 * 2 ^ 59
def prefixEnd_5582745 : Nat := 4983230072969 + 3 ^ 40 * 5582745 * 2
def baseEnd_5582745 : Nat := 2866631556484865218212929

theorem tailTrace_5582745 : CollatzResearch.WordTrace tailWord_5582745 prefixEnd_5582745 2866631556484865218212929 := by
  unfold tailWord_5582745
  simp only [CollatzResearch.WordTrace]
  refine ⟨203619438159675796782525689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135746292106450531188350459 203619438159675796782525689)
  ·
    refine ⟨152714578619756847586894267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203619438159675796782525689 152714578619756847586894267)
    ·
      refine ⟨229071867929635271380341401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152714578619756847586894267 229071867929635271380341401)
      ·
        refine ⟨171803900947226453535256051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 229071867929635271380341401 171803900947226453535256051)
        ·
          refine ⟨257705851420839680302884077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171803900947226453535256051 257705851420839680302884077)
          ·
            refine ⟨96639694282814880113581529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 257705851420839680302884077 96639694282814880113581529)
            ·
              refine ⟨72479770712111160085186147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96639694282814880113581529 72479770712111160085186147)
              ·
                refine ⟨108719656068166740127779221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72479770712111160085186147 108719656068166740127779221)
                ·
                  refine ⟨5096233878195315943489651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 108719656068166740127779221 5096233878195315943489651)
                  ·
                    refine ⟨7644350817292973915234477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5096233878195315943489651 7644350817292973915234477)
                    ·
                      refine ⟨2866631556484865218212929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7644350817292973915234477 2866631556484865218212929)
                      ·
                        rfl

theorem cell23_5582745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 6, 1, 3].length) (baseStart_5582745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5582745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5582745 prefixEnd_5582745 := by exact prefixLift 5582745
  have htrace : WordTrace (prefixWord ++ tailWord_5582745) baseStart_5582745 baseEnd_5582745 := by
    simpa [prefixWord, tailWord_5582745, baseEnd_5582745] using wordTrace_append hprefix tailTrace_5582745
  have hstable : (prefixWord ++ tailWord_5582745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5582745).length < 2 ^ (prefixWord ++ tailWord_5582745).sum := by decide
  have hdescent : baseEnd_5582745 < baseStart_5582745 := by decide
  rcases family_descends (prefixWord ++ tailWord_5582745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5582749 : List Nat := [1, 4, 2, 1, 2, 3, 3, 1, 1, 2, 3]
def baseStart_5582749 : Nat := 118140960795 + 5582749 * 2 ^ 59
def prefixEnd_5582749 : Nat := 4983230072969 + 3 ^ 40 * 5582749 * 2
def baseEnd_5582749 : Nat := 2866633610407483202562911

theorem tailTrace_5582749 : CollatzResearch.WordTrace tailWord_5582749 prefixEnd_5582749 2866633610407483202562911 := by
  unfold tailWord_5582749
  simp only [CollatzResearch.WordTrace]
  refine ⟨203619584051661305465671301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135746389367774203643780867 203619584051661305465671301)
  ·
    refine ⟨38178672009686494774813369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 203619584051661305465671301 38178672009686494774813369)
    ·
      refine ⟨28634004007264871081110027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38178672009686494774813369 28634004007264871081110027)
      ·
        refine ⟨42951006010897306621665041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28634004007264871081110027 42951006010897306621665041)
        ·
          refine ⟨32213254508172979966248781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42951006010897306621665041 32213254508172979966248781)
          ·
            refine ⟨12079970440564867487343293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32213254508172979966248781 12079970440564867487343293)
            ·
              refine ⟨4529988915211825307753735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12079970440564867487343293 4529988915211825307753735)
              ·
                refine ⟨6794983372817737961630603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4529988915211825307753735 6794983372817737961630603)
                ·
                  refine ⟨10192475059226606942445905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6794983372817737961630603 10192475059226606942445905)
                  ·
                    refine ⟨7644356294419955206834429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10192475059226606942445905 7644356294419955206834429)
                    ·
                      refine ⟨2866633610407483202562911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7644356294419955206834429 2866633610407483202562911)
                      ·
                        rfl

theorem cell23_5582749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 3, 1, 1, 2, 3].length) (baseStart_5582749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5582749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5582749 prefixEnd_5582749 := by exact prefixLift 5582749
  have htrace : WordTrace (prefixWord ++ tailWord_5582749) baseStart_5582749 baseEnd_5582749 := by
    simpa [prefixWord, tailWord_5582749, baseEnd_5582749] using wordTrace_append hprefix tailTrace_5582749
  have hstable : (prefixWord ++ tailWord_5582749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5582749).length < 2 ^ (prefixWord ++ tailWord_5582749).sum := by decide
  have hdescent : baseEnd_5582749 < baseStart_5582749 := by decide
  rcases family_descends (prefixWord ++ tailWord_5582749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5582808 : List Nat := [2, 1, 2, 2, 2, 2, 1, 2, 9]
def baseStart_5582808 : Nat := 118140960795 + 5582808 * 2 ^ 59
def prefixEnd_5582808 : Nat := 4983230072969 + 3 ^ 40 * 5582808 * 2
def baseEnd_5582808 : Nat := 318518211751788719080571

theorem tailTrace_5582808 : CollatzResearch.WordTrace tailWord_5582808 prefixEnd_5582808 318518211751788719080571 := by
  unfold tailWord_5582808
  simp only [CollatzResearch.WordTrace]
  refine ⟨101810867979223779271034539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135747823972298372361379385 101810867979223779271034539)
  ·
    refine ⟨152716301968835668906551809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101810867979223779271034539 152716301968835668906551809)
    ·
      refine ⟨114537226476626751679913857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152716301968835668906551809 114537226476626751679913857)
      ·
        refine ⟨85902919857470063759935393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114537226476626751679913857 85902919857470063759935393)
        ·
          refine ⟨64427189893102547819951545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85902919857470063759935393 64427189893102547819951545)
          ·
            refine ⟨48320392419826910864963659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64427189893102547819951545 48320392419826910864963659)
            ·
              refine ⟨72480588629740366297445489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48320392419826910864963659 72480588629740366297445489)
              ·
                refine ⟨54360441472305274723084117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72480588629740366297445489 54360441472305274723084117)
                ·
                  refine ⟨318518211751788719080571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 54360441472305274723084117 318518211751788719080571)
                  ·
                    rfl

theorem cell23_5582808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 2, 9].length) (baseStart_5582808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5582808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5582808 prefixEnd_5582808 := by exact prefixLift 5582808
  have htrace : WordTrace (prefixWord ++ tailWord_5582808) baseStart_5582808 baseEnd_5582808 := by
    simpa [prefixWord, tailWord_5582808, baseEnd_5582808] using wordTrace_append hprefix tailTrace_5582808
  have hstable : (prefixWord ++ tailWord_5582808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5582808).length < 2 ^ (prefixWord ++ tailWord_5582808).sum := by decide
  have hdescent : baseEnd_5582808 < baseStart_5582808 := by decide
  rcases family_descends (prefixWord ++ tailWord_5582808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5582813 : List Nat := [1, 4, 3, 1, 4, 1, 1, 2, 2, 1, 3]
def baseStart_5582813 : Nat := 118140960795 + 5582813 * 2 ^ 59
def prefixEnd_5582813 : Nat := 4983230072969 + 3 ^ 40 * 5582813 * 2
def baseEnd_5582813 : Nat := 2866666473169370952162617

theorem tailTrace_5582813 : CollatzResearch.WordTrace tailWord_5582813 prefixEnd_5582813 2866666473169370952162617 := by
  unfold tailWord_5582813
  simp only [CollatzResearch.WordTrace]
  refine ⟨203621918323429444396001093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135747945548952962930667395 203621918323429444396001093)
  ·
    refine ⟨38179109685643020824250205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 203621918323429444396001093 38179109685643020824250205)
    ·
      refine ⟨14317166132116132809093827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38179109685643020824250205 14317166132116132809093827)
      ·
        refine ⟨21475749198174199213640741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14317166132116132809093827 21475749198174199213640741)
        ·
          refine ⟨4026702974657662352557639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21475749198174199213640741 4026702974657662352557639)
          ·
            refine ⟨6040054461986493528836459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4026702974657662352557639 6040054461986493528836459)
            ·
              refine ⟨9060081692979740293254689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6040054461986493528836459 9060081692979740293254689)
              ·
                refine ⟨6795061269734805219941017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9060081692979740293254689 6795061269734805219941017)
                ·
                  refine ⟨5096295952301103914955763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6795061269734805219941017 5096295952301103914955763)
                  ·
                    refine ⟨7644443928451655872433645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5096295952301103914955763 7644443928451655872433645)
                    ·
                      refine ⟨2866666473169370952162617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7644443928451655872433645 2866666473169370952162617)
                      ·
                        rfl

theorem cell23_5582813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 2, 2, 1, 3].length) (baseStart_5582813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5582813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5582813 prefixEnd_5582813 := by exact prefixLift 5582813
  have htrace : WordTrace (prefixWord ++ tailWord_5582813) baseStart_5582813 baseEnd_5582813 := by
    simpa [prefixWord, tailWord_5582813, baseEnd_5582813] using wordTrace_append hprefix tailTrace_5582813
  have hstable : (prefixWord ++ tailWord_5582813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5582813).length < 2 ^ (prefixWord ++ tailWord_5582813).sum := by decide
  have hdescent : baseEnd_5582813 < baseStart_5582813 := by decide
  rcases family_descends (prefixWord ++ tailWord_5582813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5582815 : List Nat := [1, 1, 2, 3, 4, 1, 1, 2, 2, 2, 4]
def baseStart_5582815 : Nat := 118140960795 + 5582815 * 2 ^ 59
def prefixEnd_5582815 : Nat := 4983230072969 + 3 ^ 40 * 5582815 * 2
def baseEnd_5582815 : Nat := 2866667500130679944337607

theorem tailTrace_5582815 : CollatzResearch.WordTrace tailWord_5582815 prefixEnd_5582815 2866667500130679944337607 := by
  unfold tailWord_5582815
  simp only [CollatzResearch.WordTrace]
  refine ⟨203621991269422198737573899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135747994179614799158382599 203621991269422198737573899)
  ·
    refine ⟨305432986904133298106360849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203621991269422198737573899 305432986904133298106360849)
    ·
      refine ⟨229074740178099973579770637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 305432986904133298106360849 229074740178099973579770637)
      ·
        refine ⟨85903027566787490092413989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 229074740178099973579770637 85903027566787490092413989)
        ·
          refine ⟨16106817668772654392327623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85903027566787490092413989 16106817668772654392327623)
          ·
            refine ⟨24160226503158981588491435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16106817668772654392327623 24160226503158981588491435)
            ·
              refine ⟨36240339754738472382737153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24160226503158981588491435 36240339754738472382737153)
              ·
                refine ⟨27180254816053854287052865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36240339754738472382737153 27180254816053854287052865)
                ·
                  refine ⟨20385191112040390715289649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27180254816053854287052865 20385191112040390715289649)
                  ·
                    refine ⟨15288893334030293036467237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20385191112040390715289649 15288893334030293036467237)
                    ·
                      refine ⟨2866667500130679944337607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15288893334030293036467237 2866667500130679944337607)
                      ·
                        rfl

theorem cell23_5582815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 2, 2, 2, 4].length) (baseStart_5582815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5582815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5582815 prefixEnd_5582815 := by exact prefixLift 5582815
  have htrace : WordTrace (prefixWord ++ tailWord_5582815) baseStart_5582815 baseEnd_5582815 := by
    simpa [prefixWord, tailWord_5582815, baseEnd_5582815] using wordTrace_append hprefix tailTrace_5582815
  have hstable : (prefixWord ++ tailWord_5582815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5582815).length < 2 ^ (prefixWord ++ tailWord_5582815).sum := by decide
  have hdescent : baseEnd_5582815 < baseStart_5582815 := by decide
  rcases family_descends (prefixWord ++ tailWord_5582815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5582819 : List Nat := [1, 1, 1, 6, 1, 3, 1, 1, 4, 2, 2]
def baseStart_5582819 : Nat := 118140960795 + 5582819 * 2 ^ 59
def prefixEnd_5582819 : Nat := 4983230072969 + 3 ^ 40 * 5582819 * 2
def baseEnd_5582819 : Nat := 2866669554053297928687589

theorem tailTrace_5582819 : CollatzResearch.WordTrace tailWord_5582819 prefixEnd_5582819 2866669554053297928687589 := by
  unfold tailWord_5582819
  simp only [CollatzResearch.WordTrace]
  refine ⟨203622137161407707420719511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135748091440938471613813007 203622137161407707420719511)
  ·
    refine ⟨305433205742111561131079267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203622137161407707420719511 305433205742111561131079267)
    ·
      refine ⟨458149808613167341696618901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305433205742111561131079267 458149808613167341696618901)
      ·
        refine ⟨21475772278742219142029011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 458149808613167341696618901 21475772278742219142029011)
        ·
          refine ⟨32213658418113328713043517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21475772278742219142029011 32213658418113328713043517)
          ·
            refine ⟨12080121906792498267391319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32213658418113328713043517 12080121906792498267391319)
            ·
              refine ⟨18120182860188747401086979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12080121906792498267391319 18120182860188747401086979)
              ·
                refine ⟨27180274290283121101630469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18120182860188747401086979 27180274290283121101630469)
                ·
                  refine ⟨5096301429428085206555713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27180274290283121101630469 5096301429428085206555713)
                  ·
                    refine ⟨3822226072071063904916785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5096301429428085206555713 3822226072071063904916785)
                    ·
                      refine ⟨2866669554053297928687589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3822226072071063904916785 2866669554053297928687589)
                      ·
                        rfl

theorem cell23_5582819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 1, 4, 2, 2].length) (baseStart_5582819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5582819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5582819 prefixEnd_5582819 := by exact prefixLift 5582819
  have htrace : WordTrace (prefixWord ++ tailWord_5582819) baseStart_5582819 baseEnd_5582819 := by
    simpa [prefixWord, tailWord_5582819, baseEnd_5582819] using wordTrace_append hprefix tailTrace_5582819
  have hstable : (prefixWord ++ tailWord_5582819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5582819).length < 2 ^ (prefixWord ++ tailWord_5582819).sum := by decide
  have hdescent : baseEnd_5582819 < baseStart_5582819 := by decide
  rcases family_descends (prefixWord ++ tailWord_5582819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5582848 : List Nat := [2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 7]
def baseStart_5582848 : Nat := 118140960795 + 5582848 * 2 ^ 59
def prefixEnd_5582848 : Nat := 4983230072969 + 3 ^ 40 * 5582848 * 2
def baseEnd_5582848 : Nat := 2866684444992278315224955

theorem tailTrace_5582848 : CollatzResearch.WordTrace tailWord_5582848 prefixEnd_5582848 2866684444992278315224955 := by
  unfold tailWord_5582848
  simp only [CollatzResearch.WordTrace]
  refine ⟨101811597439151322686762599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135748796585535096915683465 101811597439151322686762599)
  ·
    refine ⟨152717396158726984030143899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101811597439151322686762599 152717396158726984030143899)
    ·
      refine ⟨229076094238090476045215849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152717396158726984030143899 229076094238090476045215849)
      ·
        refine ⟨171807070678567857033911887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 229076094238090476045215849 171807070678567857033911887)
        ·
          refine ⟨257710606017851785550867831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171807070678567857033911887 257710606017851785550867831)
          ·
            refine ⟨386565909026777678326301747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 257710606017851785550867831 386565909026777678326301747)
            ·
              refine ⟨579848863540166517489452621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 386565909026777678326301747 579848863540166517489452621)
              ·
                refine ⟨217443323827562444058544733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 579848863540166517489452621 217443323827562444058544733)
                ·
                  refine ⟨81541246435335916521954275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 217443323827562444058544733 81541246435335916521954275)
                  ·
                    refine ⟨122311869653003874782931413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 81541246435335916521954275 122311869653003874782931413)
                    ·
                      refine ⟨2866684444992278315224955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 122311869653003874782931413 2866684444992278315224955)
                      ·
                        rfl

theorem cell23_5582848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 7].length) (baseStart_5582848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5582848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5582848 prefixEnd_5582848 := by exact prefixLift 5582848
  have htrace : WordTrace (prefixWord ++ tailWord_5582848) baseStart_5582848 baseEnd_5582848 := by
    simpa [prefixWord, tailWord_5582848, baseEnd_5582848] using wordTrace_append hprefix tailTrace_5582848
  have hstable : (prefixWord ++ tailWord_5582848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5582848).length < 2 ^ (prefixWord ++ tailWord_5582848).sum := by decide
  have hdescent : baseEnd_5582848 < baseStart_5582848 := by decide
  rcases family_descends (prefixWord ++ tailWord_5582848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5582855 : List Nat := [1, 1, 4, 3, 1, 2, 2, 1, 1, 7]
def baseStart_5582855 : Nat := 118140960795 + 5582855 * 2 ^ 59
def prefixEnd_5582855 : Nat := 4983230072969 + 3 ^ 40 * 5582855 * 2
def baseEnd_5582855 : Nat := 955562679785619929279141

theorem tailTrace_5582855 : CollatzResearch.WordTrace tailWord_5582855 prefixEnd_5582855 955562679785619929279141 := by
  unfold tailWord_5582855
  simp only [CollatzResearch.WordTrace]
  refine ⟨203623450189277285569030019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135748966792851523712686679 203623450189277285569030019)
  ·
    refine ⟨305435175283915928353545029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203623450189277285569030019 305435175283915928353545029)
    ·
      refine ⟨57269095365734236566289693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 305435175283915928353545029 57269095365734236566289693)
      ·
        refine ⟨21475910762150338712358635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57269095365734236566289693 21475910762150338712358635)
        ·
          refine ⟨32213866143225508068537953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21475910762150338712358635 32213866143225508068537953)
          ·
            refine ⟨24160399607419131051403465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32213866143225508068537953 24160399607419131051403465)
            ·
              refine ⟨18120299705564348288552599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24160399607419131051403465 18120299705564348288552599)
              ·
                refine ⟨27180449558346522432828899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18120299705564348288552599 27180449558346522432828899)
                ·
                  refine ⟨40770674337519783649243349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27180449558346522432828899 40770674337519783649243349)
                  ·
                    refine ⟨955562679785619929279141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40770674337519783649243349 955562679785619929279141)
                    ·
                      rfl

theorem cell23_5582855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 1, 1, 7].length) (baseStart_5582855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5582855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5582855 prefixEnd_5582855 := by exact prefixLift 5582855
  have htrace : WordTrace (prefixWord ++ tailWord_5582855) baseStart_5582855 baseEnd_5582855 := by
    simpa [prefixWord, tailWord_5582855, baseEnd_5582855] using wordTrace_append hprefix tailTrace_5582855
  have hstable : (prefixWord ++ tailWord_5582855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5582855).length < 2 ^ (prefixWord ++ tailWord_5582855).sum := by decide
  have hdescent : baseEnd_5582855 < baseStart_5582855 := by decide
  rcases family_descends (prefixWord ++ tailWord_5582855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5582887 : List Nat := [1, 1, 7, 1, 3, 1, 2, 1, 2, 2, 2]
def baseStart_5582887 : Nat := 118140960795 + 5582887 * 2 ^ 59
def prefixEnd_5582887 : Nat := 4983230072969 + 3 ^ 40 * 5582887 * 2
def baseEnd_5582887 : Nat := 2866704470737803662637277

theorem tailTrace_5582887 : CollatzResearch.WordTrace tailWord_5582887 prefixEnd_5582887 2866704470737803662637277 := by
  unfold tailWord_5582887
  simp only [CollatzResearch.WordTrace]
  refine ⟨203624617325161355034194915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135749744883440903356129943 203624617325161355034194915)
  ·
    refine ⟨305436925987742032551292373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203624617325161355034194915 305436925987742032551292373)
    ·
      refine ⟨7158677952837703887920915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 305436925987742032551292373 7158677952837703887920915)
      ·
        refine ⟨10738016929256555831881373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7158677952837703887920915 10738016929256555831881373)
        ·
          refine ⟨4026756348471208436955515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10738016929256555831881373 4026756348471208436955515)
          ·
            refine ⟨6040134522706812655433273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4026756348471208436955515 6040134522706812655433273)
            ·
              refine ⟨4530100892030109491574955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6040134522706812655433273 4530100892030109491574955)
              ·
                refine ⟨6795151338045164237362433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4530100892030109491574955 6795151338045164237362433)
                ·
                  refine ⟨5096363503533873178021825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6795151338045164237362433 5096363503533873178021825)
                  ·
                    refine ⟨3822272627650404883516369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5096363503533873178021825 3822272627650404883516369)
                    ·
                      refine ⟨2866704470737803662637277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3822272627650404883516369 2866704470737803662637277)
                      ·
                        rfl

theorem cell23_5582887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 2, 1, 2, 2, 2].length) (baseStart_5582887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5582887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5582887 prefixEnd_5582887 := by exact prefixLift 5582887
  have htrace : WordTrace (prefixWord ++ tailWord_5582887) baseStart_5582887 baseEnd_5582887 := by
    simpa [prefixWord, tailWord_5582887, baseEnd_5582887] using wordTrace_append hprefix tailTrace_5582887
  have hstable : (prefixWord ++ tailWord_5582887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5582887).length < 2 ^ (prefixWord ++ tailWord_5582887).sum := by decide
  have hdescent : baseEnd_5582887 < baseStart_5582887 := by decide
  rcases family_descends (prefixWord ++ tailWord_5582887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5582895 : List Nat := [1, 1, 2, 1, 2, 1, 1, 6, 1, 4, 3]
def baseStart_5582895 : Nat := 118140960795 + 5582895 * 2 ^ 59
def prefixEnd_5582895 : Nat := 4983230072969 + 3 ^ 40 * 5582895 * 2
def baseEnd_5582895 : Nat := 2866708578583039631337239

theorem tailTrace_5582895 : CollatzResearch.WordTrace tailWord_5582895 prefixEnd_5582895 2866708578583039631337239 := by
  unfold tailWord_5582895
  simp only [CollatzResearch.WordTrace]
  refine ⟨203624909109132372400486139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135749939406088248266990759 203624909109132372400486139)
  ·
    refine ⟨305437363663698558600729209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203624909109132372400486139 305437363663698558600729209)
    ·
      refine ⟨229078022747773918950546907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 305437363663698558600729209 229078022747773918950546907)
      ·
        refine ⟨343617034121660878425820361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229078022747773918950546907 343617034121660878425820361)
        ·
          refine ⟨257712775591245658819365271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 343617034121660878425820361 257712775591245658819365271)
          ·
            refine ⟨386569163386868488229047907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 257712775591245658819365271 386569163386868488229047907)
            ·
              refine ⟨579853745080302732343571861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 386569163386868488229047907 579853745080302732343571861)
              ·
                refine ⟨27180644300639190578604931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 579853745080302732343571861 27180644300639190578604931)
                ·
                  refine ⟨40770966450958785867907397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27180644300639190578604931 40770966450958785867907397)
                  ·
                    refine ⟨7644556209554772350232637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40770966450958785867907397 7644556209554772350232637)
                    ·
                      refine ⟨2866708578583039631337239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7644556209554772350232637 2866708578583039631337239)
                      ·
                        rfl

theorem cell23_5582895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 6, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 6, 1, 4, 3].length) (baseStart_5582895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5582895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5582895 prefixEnd_5582895 := by exact prefixLift 5582895
  have htrace : WordTrace (prefixWord ++ tailWord_5582895) baseStart_5582895 baseEnd_5582895 := by
    simpa [prefixWord, tailWord_5582895, baseEnd_5582895] using wordTrace_append hprefix tailTrace_5582895
  have hstable : (prefixWord ++ tailWord_5582895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5582895).length < 2 ^ (prefixWord ++ tailWord_5582895).sum := by decide
  have hdescent : baseEnd_5582895 < baseStart_5582895 := by decide
  rcases family_descends (prefixWord ++ tailWord_5582895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5582912 : List Nat := [2, 1, 1, 2, 2, 4, 1, 3, 2, 2, 3]
def baseStart_5582912 : Nat := 118140960795 + 5582912 * 2 ^ 59
def prefixEnd_5582912 : Nat := 4983230072969 + 3 ^ 40 * 5582912 * 2
def baseEnd_5582912 : Nat := 2866717307754166064824661

theorem tailTrace_5582912 : CollatzResearch.WordTrace tailWord_5582912 prefixEnd_5582912 2866717307754166064824661 := by
  unfold tailWord_5582912
  simp only [CollatzResearch.WordTrace]
  refine ⟨101812764575035392151927495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135750352766713856202569993 101812764575035392151927495)
  ·
    refine ⟨152719146862553088227891243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101812764575035392151927495 152719146862553088227891243)
    ·
      refine ⟨229078720293829632341836865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152719146862553088227891243 229078720293829632341836865)
      ·
        refine ⟨171809040220372224256377649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 229078720293829632341836865 171809040220372224256377649)
        ·
          refine ⟨128856780165279168192283237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171809040220372224256377649 128856780165279168192283237)
          ·
            refine ⟨24160646280989844036053107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 128856780165279168192283237 24160646280989844036053107)
            ·
              refine ⟨36240969421484766054079661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24160646280989844036053107 36240969421484766054079661)
              ·
                refine ⟨13590363533056787270279873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36240969421484766054079661 13590363533056787270279873)
                ·
                  refine ⟨10192772649792590452709905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13590363533056787270279873 10192772649792590452709905)
                  ·
                    refine ⟨7644579487344442839532429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10192772649792590452709905 7644579487344442839532429)
                    ·
                      refine ⟨2866717307754166064824661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7644579487344442839532429 2866717307754166064824661)
                      ·
                        rfl

theorem cell23_5582912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 3, 2, 2, 3].length) (baseStart_5582912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5582912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5582912 prefixEnd_5582912 := by exact prefixLift 5582912
  have htrace : WordTrace (prefixWord ++ tailWord_5582912) baseStart_5582912 baseEnd_5582912 := by
    simpa [prefixWord, tailWord_5582912, baseEnd_5582912] using wordTrace_append hprefix tailTrace_5582912
  have hstable : (prefixWord ++ tailWord_5582912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5582912).length < 2 ^ (prefixWord ++ tailWord_5582912).sum := by decide
  have hdescent : baseEnd_5582912 < baseStart_5582912 := by decide
  rcases family_descends (prefixWord ++ tailWord_5582912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5582919 : List Nat := [1, 1, 4, 1, 3, 1, 2, 5, 1, 4]
def baseStart_5582919 : Nat := 118140960795 + 5582919 * 2 ^ 59
def prefixEnd_5582919 : Nat := 4983230072969 + 3 ^ 40 * 5582919 * 2
def baseEnd_5582919 : Nat := 955573634039582512479043

theorem tailTrace_5582919 : CollatzResearch.WordTrace tailWord_5582919 prefixEnd_5582919 955573634039582512479043 := by
  unfold tailWord_5582919
  simp only [CollatzResearch.WordTrace]
  refine ⟨203625784461045424499359811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135750522974030282999573207 203625784461045424499359811)
  ·
    refine ⟨305438676691568136749039717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203625784461045424499359811 305438676691568136749039717)
    ·
      refine ⟨57269751879669025640444947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 305438676691568136749039717 57269751879669025640444947)
      ·
        refine ⟨85904627819503538460667421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57269751879669025640444947 85904627819503538460667421)
        ·
          refine ⟨32214235432313826922750283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85904627819503538460667421 32214235432313826922750283)
          ·
            refine ⟨48321353148470740384125425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32214235432313826922750283 48321353148470740384125425)
            ·
              refine ⟨36241014861353055288094069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48321353148470740384125425 36241014861353055288094069)
              ·
                refine ⟨3397595143251848933258819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36241014861353055288094069 3397595143251848933258819)
                ·
                  refine ⟨5096392714877773399888229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3397595143251848933258819 5096392714877773399888229)
                  ·
                    refine ⟨955573634039582512479043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5096392714877773399888229 955573634039582512479043)
                    ·
                      rfl

theorem cell23_5582919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 5, 1, 4].length) (baseStart_5582919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5582919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5582919 prefixEnd_5582919 := by exact prefixLift 5582919
  have htrace : WordTrace (prefixWord ++ tailWord_5582919) baseStart_5582919 baseEnd_5582919 := by
    simpa [prefixWord, tailWord_5582919, baseEnd_5582919] using wordTrace_append hprefix tailTrace_5582919
  have hstable : (prefixWord ++ tailWord_5582919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5582919).length < 2 ^ (prefixWord ++ tailWord_5582919).sum := by decide
  have hdescent : baseEnd_5582919 < baseStart_5582919 := by decide
  rcases family_descends (prefixWord ++ tailWord_5582919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5582936 : List Nat := [2, 1, 2, 2, 1, 4, 4, 2, 1, 4]
def baseStart_5582936 : Nat := 118140960795 + 5582936 * 2 ^ 59
def prefixEnd_5582936 : Nat := 4983230072969 + 3 ^ 40 * 5582936 * 2
def baseEnd_5582936 : Nat := 955576543763291323641517

theorem tailTrace_5582936 : CollatzResearch.WordTrace tailWord_5582936 prefixEnd_5582936 955576543763291323641517 := by
  unfold tailWord_5582936
  simp only [CollatzResearch.WordTrace]
  refine ⟨101813202250991918201364331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135750936334655890935152441 101813202250991918201364331)
  ·
    refine ⟨152719803376487877302046497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101813202250991918201364331 152719803376487877302046497)
    ·
      refine ⟨114539852532365907976534873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152719803376487877302046497 114539852532365907976534873)
      ·
        refine ⟨85904889399274430982401155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114539852532365907976534873 85904889399274430982401155)
        ·
          refine ⟨128857334098911646473601733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85904889399274430982401155 128857334098911646473601733)
          ·
            refine ⟨24160750143545933713800325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 128857334098911646473601733 24160750143545933713800325)
            ·
              refine ⟨4530140651914862571337561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24160750143545933713800325 4530140651914862571337561)
              ·
                refine ⟨3397605488936146928503171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4530140651914862571337561 3397605488936146928503171)
                ·
                  refine ⟨5096408233404220392754757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3397605488936146928503171 5096408233404220392754757)
                  ·
                    refine ⟨955576543763291323641517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5096408233404220392754757 955576543763291323641517)
                    ·
                      rfl

theorem cell23_5582936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 4, 2, 1, 4].length) (baseStart_5582936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5582936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5582936 prefixEnd_5582936 := by exact prefixLift 5582936
  have htrace : WordTrace (prefixWord ++ tailWord_5582936) baseStart_5582936 baseEnd_5582936 := by
    simpa [prefixWord, tailWord_5582936, baseEnd_5582936] using wordTrace_append hprefix tailTrace_5582936
  have hstable : (prefixWord ++ tailWord_5582936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5582936).length < 2 ^ (prefixWord ++ tailWord_5582936).sum := by decide
  have hdescent : baseEnd_5582936 < baseStart_5582936 := by decide
  rcases family_descends (prefixWord ++ tailWord_5582936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5582959 : List Nat := [1, 1, 2, 1, 3, 5, 1, 2, 3, 1, 3]
def baseStart_5582959 : Nat := 118140960795 + 5582959 * 2 ^ 59
def prefixEnd_5582959 : Nat := 4983230072969 + 3 ^ 40 * 5582959 * 2
def baseEnd_5582959 : Nat := 2866741441344927380936945

theorem tailTrace_5582959 : CollatzResearch.WordTrace tailWord_5582959 prefixEnd_5582959 2866741441344927380936945 := by
  unfold tailWord_5582959
  simp only [CollatzResearch.WordTrace]
  refine ⟨203627243380900511330815931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135751495587267007553877287 203627243380900511330815931)
  ·
    refine ⟨305440865071350766996223897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203627243380900511330815931 305440865071350766996223897)
    ·
      refine ⟨229080648803513075247167923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 305440865071350766996223897 229080648803513075247167923)
      ·
        refine ⟨343620973205269612870751885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229080648803513075247167923 343620973205269612870751885)
        ·
          refine ⟨128857864951976104826531957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 343620973205269612870751885 128857864951976104826531957)
          ·
            refine ⟨12080424839247759827487371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 128857864951976104826531957 12080424839247759827487371)
            ·
              refine ⟨18120637258871639741231057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12080424839247759827487371 18120637258871639741231057)
              ·
                refine ⟨13590477944153729805923293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18120637258871639741231057 13590477944153729805923293)
                ·
                  refine ⟨5096429229057648677221235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13590477944153729805923293 5096429229057648677221235)
                  ·
                    refine ⟨7644643843586473015831853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5096429229057648677221235 7644643843586473015831853)
                    ·
                      refine ⟨2866741441344927380936945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7644643843586473015831853 2866741441344927380936945)
                      ·
                        rfl

theorem cell23_5582959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 2, 3, 1, 3].length) (baseStart_5582959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5582959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5582959 prefixEnd_5582959 := by exact prefixLift 5582959
  have htrace : WordTrace (prefixWord ++ tailWord_5582959) baseStart_5582959 baseEnd_5582959 := by
    simpa [prefixWord, tailWord_5582959, baseEnd_5582959] using wordTrace_append hprefix tailTrace_5582959
  have hstable : (prefixWord ++ tailWord_5582959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5582959).length < 2 ^ (prefixWord ++ tailWord_5582959).sum := by decide
  have hdescent : baseEnd_5582959 < baseStart_5582959 := by decide
  rcases family_descends (prefixWord ++ tailWord_5582959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5582962 : List Nat := [3, 2, 1, 2, 2, 2, 2, 1, 3, 5]
def baseStart_5582962 : Nat := 118140960795 + 5582962 * 2 ^ 59
def prefixEnd_5582962 : Nat := 4983230072969 + 3 ^ 40 * 5582962 * 2
def baseEnd_5582962 : Nat := 955580993928963623066477

theorem tailTrace_5582962 : CollatzResearch.WordTrace tailWord_5582962 prefixEnd_5582962 955580993928963623066477 := by
  unfold tailWord_5582962
  simp only [CollatzResearch.WordTrace]
  refine ⟨50906838199972410710793785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135751568533259761895450093 50906838199972410710793785)
  ·
    refine ⟨38180128649979308033095339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50906838199972410710793785 38180128649979308033095339)
    ·
      refine ⟨57270192974968962049643009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38180128649979308033095339 57270192974968962049643009)
      ·
        refine ⟨42952644731226721537232257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57270192974968962049643009 42952644731226721537232257)
        ·
          refine ⟨32214483548420041152924193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42952644731226721537232257 32214483548420041152924193)
          ·
            refine ⟨24160862661315030864693145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32214483548420041152924193 24160862661315030864693145)
            ·
              refine ⟨18120646995986273148519859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24160862661315030864693145 18120646995986273148519859)
              ·
                refine ⟨27180970493979409722779789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18120646995986273148519859 27180970493979409722779789)
                ·
                  refine ⟨10192863935242278646042421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27180970493979409722779789 10192863935242278646042421)
                  ·
                    refine ⟨955580993928963623066477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10192863935242278646042421 955580993928963623066477)
                    ·
                      rfl

theorem cell23_5582962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 1, 3, 5].length) (baseStart_5582962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5582962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5582962 prefixEnd_5582962 := by exact prefixLift 5582962
  have htrace : WordTrace (prefixWord ++ tailWord_5582962) baseStart_5582962 baseEnd_5582962 := by
    simpa [prefixWord, tailWord_5582962, baseEnd_5582962] using wordTrace_append hprefix tailTrace_5582962
  have hstable : (prefixWord ++ tailWord_5582962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5582962).length < 2 ^ (prefixWord ++ tailWord_5582962).sum := by decide
  have hdescent : baseEnd_5582962 < baseStart_5582962 := by decide
  rcases family_descends (prefixWord ++ tailWord_5582962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5582969 : List Nat := [1, 2, 1, 3, 4, 2, 1, 1, 1, 5, 2]
def baseStart_5582969 : Nat := 118140960795 + 5582969 * 2 ^ 59
def prefixEnd_5582969 : Nat := 4983230072969 + 3 ^ 40 * 5582969 * 2
def baseEnd_5582969 : Nat := 2866746576151472341811899

theorem tailTrace_5582969 : CollatzResearch.WordTrace tailWord_5582969 prefixEnd_5582969 2866746576151472341811899 := by
  unfold tailWord_5582969
  simp only [CollatzResearch.WordTrace]
  refine ⟨203627608110864283038679961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135751738740576188692453307 203627608110864283038679961)
  ·
    refine ⟨152720706083148212279009971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203627608110864283038679961 152720706083148212279009971)
    ·
      refine ⟨229081059124722318418514957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152720706083148212279009971 229081059124722318418514957)
      ·
        refine ⟨85905397171770869406943109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 229081059124722318418514957 85905397171770869406943109)
        ·
          refine ⟨16107261969707038013801833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85905397171770869406943109 16107261969707038013801833)
          ·
            refine ⟨12080446477280278510351375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16107261969707038013801833 12080446477280278510351375)
            ·
              refine ⟨18120669715920417765527063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12080446477280278510351375 18120669715920417765527063)
              ·
                refine ⟨27181004573880626648290595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18120669715920417765527063 27181004573880626648290595)
                ·
                  refine ⟨40771506860820939972435893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27181004573880626648290595 40771506860820939972435893)
                  ·
                    refine ⟨3822328768201963122415865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40771506860820939972435893 3822328768201963122415865)
                    ·
                      refine ⟨2866746576151472341811899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3822328768201963122415865 2866746576151472341811899)
                      ·
                        rfl

theorem cell23_5582969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 1, 1, 5, 2].length) (baseStart_5582969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5582969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5582969 prefixEnd_5582969 := by exact prefixLift 5582969
  have htrace : WordTrace (prefixWord ++ tailWord_5582969) baseStart_5582969 baseEnd_5582969 := by
    simpa [prefixWord, tailWord_5582969, baseEnd_5582969] using wordTrace_append hprefix tailTrace_5582969
  have hstable : (prefixWord ++ tailWord_5582969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5582969).length < 2 ^ (prefixWord ++ tailWord_5582969).sum := by decide
  have hdescent : baseEnd_5582969 < baseStart_5582969 := by decide
  rcases family_descends (prefixWord ++ tailWord_5582969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5582979 : List Nat := [1, 1, 1, 3, 3, 3, 4, 1, 1, 5]
def baseStart_5582979 : Nat := 118140960795 + 5582979 * 2 ^ 59
def prefixEnd_5582979 : Nat := 4983230072969 + 3 ^ 40 * 5582979 * 2
def baseEnd_5582979 : Nat := 955583903652672434228951

theorem tailTrace_5582979 : CollatzResearch.WordTrace tailWord_5582979 prefixEnd_5582979 955583903652672434228951 := by
  unfold tailWord_5582979
  simp only [CollatzResearch.WordTrace]
  refine ⟨203627972840828054746543991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135751981893885369831029327 203627972840828054746543991)
  ·
    refine ⟨305441959261242082119815987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203627972840828054746543991 305441959261242082119815987)
    ·
      refine ⟨458162938891863123179723981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305441959261242082119815987 458162938891863123179723981)
      ·
        refine ⟨171811102084448671192396493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 458162938891863123179723981 171811102084448671192396493)
        ·
          refine ⟨64429163281668251697148685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 171811102084448671192396493 64429163281668251697148685)
          ·
            refine ⟨24160936230625594386430757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64429163281668251697148685 24160936230625594386430757)
            ·
              refine ⟨4530175543242298947455767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24160936230625594386430757 4530175543242298947455767)
              ·
                refine ⟨6795263314863448421183651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4530175543242298947455767 6795263314863448421183651)
                ·
                  refine ⟨10192894972295172631775477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6795263314863448421183651 10192894972295172631775477)
                  ·
                    refine ⟨955583903652672434228951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10192894972295172631775477 955583903652672434228951)
                    ·
                      rfl

theorem cell23_5582979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 4, 1, 1, 5].length) (baseStart_5582979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5582979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5582979 prefixEnd_5582979 := by exact prefixLift 5582979
  have htrace : WordTrace (prefixWord ++ tailWord_5582979) baseStart_5582979 baseEnd_5582979 := by
    simpa [prefixWord, tailWord_5582979, baseEnd_5582979] using wordTrace_append hprefix tailTrace_5582979
  have hstable : (prefixWord ++ tailWord_5582979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5582979).length < 2 ^ (prefixWord ++ tailWord_5582979).sum := by decide
  have hdescent : baseEnd_5582979 < baseStart_5582979 := by decide
  rcases family_descends (prefixWord ++ tailWord_5582979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5582992 : List Nat := [2, 1, 1, 1, 1, 1, 7, 1, 4, 4]
def baseStart_5582992 : Nat := 118140960795 + 5582992 * 2 ^ 59
def prefixEnd_5582992 : Nat := 4983230072969 + 3 ^ 40 * 5582992 * 2
def baseEnd_5582992 : Nat := 955586128735508583941431

theorem tailTrace_5582992 : CollatzResearch.WordTrace tailWord_5582992 prefixEnd_5582992 955586128735508583941431 := by
  unfold tailWord_5582992
  simp only [CollatzResearch.WordTrace]
  refine ⟨101814223494890478983383615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135752297993187305311178153 101814223494890478983383615)
  ·
    refine ⟨152721335242335718475075423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101814223494890478983383615 152721335242335718475075423)
    ·
      refine ⟨229082002863503577712613135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152721335242335718475075423 229082002863503577712613135)
      ·
        refine ⟨343623004295255366568919703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229082002863503577712613135 343623004295255366568919703)
        ·
          refine ⟨515434506442883049853379555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 343623004295255366568919703 515434506442883049853379555)
          ·
            refine ⟨773151759664324574780069333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 515434506442883049853379555 773151759664324574780069333)
            ·
              refine ⟨18120744367132607221407875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 773151759664324574780069333 18120744367132607221407875)
              ·
                refine ⟨27181116550698910832111813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18120744367132607221407875 27181116550698910832111813)
                ·
                  refine ⟨5096459353256045781020965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27181116550698910832111813 5096459353256045781020965)
                  ·
                    refine ⟨955586128735508583941431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5096459353256045781020965 955586128735508583941431)
                    ·
                      rfl

theorem cell23_5582992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 1, 4, 4].length) (baseStart_5582992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5582992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5582992 prefixEnd_5582992 := by exact prefixLift 5582992
  have htrace : WordTrace (prefixWord ++ tailWord_5582992) baseStart_5582992 baseEnd_5582992 := by
    simpa [prefixWord, tailWord_5582992, baseEnd_5582992] using wordTrace_append hprefix tailTrace_5582992
  have hstable : (prefixWord ++ tailWord_5582992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5582992).length < 2 ^ (prefixWord ++ tailWord_5582992).sum := by decide
  have hdescent : baseEnd_5582992 < baseStart_5582992 := by decide
  rcases family_descends (prefixWord ++ tailWord_5582992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5582995 : List Nat := [1, 1, 1, 2, 1, 2, 3, 4, 1, 1, 6]
def baseStart_5582995 : Nat := 118140960795 + 5582995 * 2 ^ 59
def prefixEnd_5582995 : Nat := 4983230072969 + 3 ^ 40 * 5582995 * 2
def baseEnd_5582995 : Nat := 2866759926648489240086779

theorem tailTrace_5582995 : CollatzResearch.WordTrace tailWord_5582995 prefixEnd_5582995 2866759926648489240086779 := by
  unfold tailWord_5582995
  simp only [CollatzResearch.WordTrace]
  refine ⟨203628556408770089479126439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135752370939180059652750959 203628556408770089479126439)
  ·
    refine ⟨305442834613155134218689659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203628556408770089479126439 305442834613155134218689659)
    ·
      refine ⟨458164251919732701328034489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305442834613155134218689659 458164251919732701328034489)
      ·
        refine ⟨343623188939799525996025867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 458164251919732701328034489 343623188939799525996025867)
        ·
          refine ⟨515434783409699288994038801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 343623188939799525996025867 515434783409699288994038801)
          ·
            refine ⟨386576087557274466745529101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 515434783409699288994038801 386576087557274466745529101)
            ·
              refine ⟨144966032833977925029573413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 386576087557274466745529101 144966032833977925029573413)
              ·
                refine ⟨27181131156370860943045015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 144966032833977925029573413 27181131156370860943045015)
                ·
                  refine ⟨40771696734556291414567523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27181131156370860943045015 40771696734556291414567523)
                  ·
                    refine ⟨61157545101834437121851285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40771696734556291414567523 61157545101834437121851285)
                    ·
                      refine ⟨2866759926648489240086779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61157545101834437121851285 2866759926648489240086779)
                      ·
                        rfl

theorem cell23_5582995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 4, 1, 1, 6].length) (baseStart_5582995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5582995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5582995 prefixEnd_5582995 := by exact prefixLift 5582995
  have htrace : WordTrace (prefixWord ++ tailWord_5582995) baseStart_5582995 baseEnd_5582995 := by
    simpa [prefixWord, tailWord_5582995, baseEnd_5582995] using wordTrace_append hprefix tailTrace_5582995
  have hstable : (prefixWord ++ tailWord_5582995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5582995).length < 2 ^ (prefixWord ++ tailWord_5582995).sum := by decide
  have hdescent : baseEnd_5582995 < baseStart_5582995 := by decide
  rcases family_descends (prefixWord ++ tailWord_5582995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5583009 : List Nat := [1, 2, 3, 3, 1, 4, 1, 1, 1, 6]
def baseStart_5583009 : Nat := 118140960795 + 5583009 * 2 ^ 59
def prefixEnd_5583009 : Nat := 4983230072969 + 3 ^ 40 * 5583009 * 2
def baseEnd_5583009 : Nat := 955589038459217395103905

theorem tailTrace_5583009 : CollatzResearch.WordTrace tailWord_5583009 prefixEnd_5583009 955589038459217395103905 := by
  unfold tailWord_5583009
  simp only [CollatzResearch.WordTrace]
  refine ⟨203629067030719369870136081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135752711353812913246757387 203629067030719369870136081)
  ·
    refine ⟨152721800273039527402602061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203629067030719369870136081 152721800273039527402602061)
    ·
      refine ⟨57270675102389822775975773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152721800273039527402602061 57270675102389822775975773)
      ·
        refine ⟨21476503163396183540990915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57270675102389822775975773 21476503163396183540990915)
        ·
          refine ⟨32214754745094275311486373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21476503163396183540990915 32214754745094275311486373)
          ·
            refine ⟨6040266514705176620903695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32214754745094275311486373 6040266514705176620903695)
            ·
              refine ⟨9060399772057764931355543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6040266514705176620903695 9060399772057764931355543)
              ·
                refine ⟨13590599658086647397033315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9060399772057764931355543 13590599658086647397033315)
                ·
                  refine ⟨20385899487129971095549973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13590599658086647397033315 20385899487129971095549973)
                  ·
                    refine ⟨955589038459217395103905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20385899487129971095549973 955589038459217395103905)
                    ·
                      rfl

theorem cell23_5583009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 1, 1, 6].length) (baseStart_5583009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5583009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5583009 prefixEnd_5583009 := by exact prefixLift 5583009
  have htrace : WordTrace (prefixWord ++ tailWord_5583009) baseStart_5583009 baseEnd_5583009 := by
    simpa [prefixWord, tailWord_5583009, baseEnd_5583009] using wordTrace_append hprefix tailTrace_5583009
  have hstable : (prefixWord ++ tailWord_5583009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5583009).length < 2 ^ (prefixWord ++ tailWord_5583009).sum := by decide
  have hdescent : baseEnd_5583009 < baseStart_5583009 := by decide
  rcases family_descends (prefixWord ++ tailWord_5583009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5583032 : List Nat := [2, 1, 2, 1, 2, 1, 4, 1, 3, 3, 3]
def baseStart_5583032 : Nat := 118140960795 + 5583032 * 2 ^ 59
def prefixEnd_5583032 : Nat := 4983230072969 + 3 ^ 40 * 5583032 * 2
def baseEnd_5583032 : Nat := 2866778925432705595324109

theorem tailTrace_5583032 : CollatzResearch.WordTrace tailWord_5583032 prefixEnd_5583032 2866778925432705595324109 := by
  unfold tailWord_5583032
  simp only [CollatzResearch.WordTrace]
  refine ⟨101814952954818022399111675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135753270606424029865482233 101814952954818022399111675)
  ·
    refine ⟨152722429432227033598667513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101814952954818022399111675 152722429432227033598667513)
    ·
      refine ⟨114541822074170275199000635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152722429432227033598667513 114541822074170275199000635)
      ·
        refine ⟨171812733111255412798500953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114541822074170275199000635 171812733111255412798500953)
        ·
          refine ⟨128859549833441559598875715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171812733111255412798500953 128859549833441559598875715)
          ·
            refine ⟨193289324750162339398313573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128859549833441559598875715 193289324750162339398313573)
            ·
              refine ⟨36241748390655438637183795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 193289324750162339398313573 36241748390655438637183795)
              ·
                refine ⟨54362622585983157955775693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36241748390655438637183795 54362622585983157955775693)
                ·
                  refine ⟨20385983469743684233415885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54362622585983157955775693 20385983469743684233415885)
                  ·
                    refine ⟨7644743801153881587530957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20385983469743684233415885 7644743801153881587530957)
                    ·
                      refine ⟨2866778925432705595324109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7644743801153881587530957 2866778925432705595324109)
                      ·
                        rfl

theorem cell23_5583032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 1, 3, 3, 3].length) (baseStart_5583032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5583032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5583032 prefixEnd_5583032 := by exact prefixLift 5583032
  have htrace : WordTrace (prefixWord ++ tailWord_5583032) baseStart_5583032 baseEnd_5583032 := by
    simpa [prefixWord, tailWord_5583032, baseEnd_5583032] using wordTrace_append hprefix tailTrace_5583032
  have hstable : (prefixWord ++ tailWord_5583032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5583032).length < 2 ^ (prefixWord ++ tailWord_5583032).sum := by decide
  have hdescent : baseEnd_5583032 < baseStart_5583032 := by decide
  rcases family_descends (prefixWord ++ tailWord_5583032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5583050 : List Nat := [3, 1, 2, 1, 3, 1, 5, 2, 1, 2, 2]
def baseStart_5583050 : Nat := 118140960795 + 5583050 * 2 ^ 59
def prefixEnd_5583050 : Nat := 4983230072969 + 3 ^ 40 * 5583050 * 2
def baseEnd_5583050 : Nat := 2866788168084486524899027

theorem tailTrace_5583050 : CollatzResearch.WordTrace tailWord_5583050 prefixEnd_5583050 2866788168084486524899027 := by
  unfold tailWord_5583050
  simp only [CollatzResearch.WordTrace]
  refine ⟨50907640605892708468094651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135753708282380555914919069 50907640605892708468094651)
  ·
    refine ⟨76361460908839062702141977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50907640605892708468094651 76361460908839062702141977)
    ·
      refine ⟨57271095681629297026606483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76361460908839062702141977 57271095681629297026606483)
      ·
        refine ⟨85906643522443945539909725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57271095681629297026606483 85906643522443945539909725)
        ·
          refine ⟨32214991320916479577466147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85906643522443945539909725 32214991320916479577466147)
          ·
            refine ⟨48322486981374719366199221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32214991320916479577466147 48322486981374719366199221)
            ·
              refine ⟨4530233154503879940581177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48322486981374719366199221 4530233154503879940581177)
              ·
                refine ⟨3397674865877909955435883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4530233154503879940581177 3397674865877909955435883)
                ·
                  refine ⟨5096512298816864933153825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3397674865877909955435883 5096512298816864933153825)
                  ·
                    refine ⟨3822384224112648699865369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5096512298816864933153825 3822384224112648699865369)
                    ·
                      refine ⟨2866788168084486524899027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3822384224112648699865369 2866788168084486524899027)
                      ·
                        rfl

theorem cell23_5583050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 5, 2, 1, 2, 2].length) (baseStart_5583050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5583050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5583050 prefixEnd_5583050 := by exact prefixLift 5583050
  have htrace : WordTrace (prefixWord ++ tailWord_5583050) baseStart_5583050 baseEnd_5583050 := by
    simpa [prefixWord, tailWord_5583050, baseEnd_5583050] using wordTrace_append hprefix tailTrace_5583050
  have hstable : (prefixWord ++ tailWord_5583050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5583050).length < 2 ^ (prefixWord ++ tailWord_5583050).sum := by decide
  have hdescent : baseEnd_5583050 < baseStart_5583050 := by decide
  rcases family_descends (prefixWord ++ tailWord_5583050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5583089 : List Nat := [1, 2, 2, 2, 2, 1, 3, 1, 3, 4, 2]
def baseStart_5583089 : Nat := 118140960795 + 5583089 * 2 ^ 59
def prefixEnd_5583089 : Nat := 4983230072969 + 3 ^ 40 * 5583089 * 2
def baseEnd_5583089 : Nat := 2866808193830011872311347

theorem tailTrace_5583089 : CollatzResearch.WordTrace tailWord_5583089 prefixEnd_5583089 2866808193830011872311347 := by
  unfold tailWord_5583089
  simp only [CollatzResearch.WordTrace]
  refine ⟨203631984870429543533048321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135754656580286362355365547 203631984870429543533048321)
  ·
    refine ⟨152723988652822157649786241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203631984870429543533048321 152723988652822157649786241)
    ·
      refine ⟨114542991489616618237339681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152723988652822157649786241 114542991489616618237339681)
      ·
        refine ⟨85907243617212463678004761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114542991489616618237339681 85907243617212463678004761)
        ·
          refine ⟨64430432712909347758503571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85907243617212463678004761 64430432712909347758503571)
          ·
            refine ⟨96645649069364021637755357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64430432712909347758503571 96645649069364021637755357)
            ·
              refine ⟨36242118401011508114158259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96645649069364021637755357 36242118401011508114158259)
              ·
                refine ⟨54363177601517262171237389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36242118401011508114158259 54363177601517262171237389)
                ·
                  refine ⟨20386191600568973314214021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54363177601517262171237389 20386191600568973314214021)
                  ·
                    refine ⟨3822410925106682496415129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20386191600568973314214021 3822410925106682496415129)
                    ·
                      refine ⟨2866808193830011872311347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3822410925106682496415129 2866808193830011872311347)
                      ·
                        rfl

theorem cell23_5583089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 1, 3, 4, 2].length) (baseStart_5583089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5583089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5583089 prefixEnd_5583089 := by exact prefixLift 5583089
  have htrace : WordTrace (prefixWord ++ tailWord_5583089) baseStart_5583089 baseEnd_5583089 := by
    simpa [prefixWord, tailWord_5583089, baseEnd_5583089] using wordTrace_append hprefix tailTrace_5583089
  have hstable : (prefixWord ++ tailWord_5583089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5583089).length < 2 ^ (prefixWord ++ tailWord_5583089).sum := by decide
  have hdescent : baseEnd_5583089 < baseStart_5583089 := by decide
  rcases family_descends (prefixWord ++ tailWord_5583089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5583152 : List Nat := [2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 5]
def baseStart_5583152 : Nat := 118140960795 + 5583152 * 2 ^ 59
def prefixEnd_5583152 : Nat := 4983230072969 + 3 ^ 40 * 5583152 * 2
def baseEnd_5583152 : Nat := 2866840543111245125823557

theorem tailTrace_5583152 : CollatzResearch.WordTrace tailWord_5583152 prefixEnd_5583152 2866840543111245125823557 := by
  unfold tailWord_5583152
  simp only [CollatzResearch.WordTrace]
  refine ⟨101817141334600652646295855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135756188446134203528394473 101817141334600652646295855)
  ·
    refine ⟨152725712001900978969443783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101817141334600652646295855 152725712001900978969443783)
    ·
      refine ⟨229088568002851468454165675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152725712001900978969443783 229088568002851468454165675)
      ·
        refine ⟨343632852004277202681248513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229088568002851468454165675 343632852004277202681248513)
        ·
          refine ⟨257724639003207902010936385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 343632852004277202681248513 257724639003207902010936385)
          ·
            refine ⟨193293479252405926508202289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 257724639003207902010936385 193293479252405926508202289)
            ·
              refine ⟨144970109439304444881151717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 193293479252405926508202289 144970109439304444881151717)
              ·
                refine ⟨27181895519869583415215947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 144970109439304444881151717 27181895519869583415215947)
                ·
                  refine ⟨40772843279804375122823921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27181895519869583415215947 40772843279804375122823921)
                  ·
                    refine ⟨30579632459853281342117941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40772843279804375122823921 30579632459853281342117941)
                    ·
                      refine ⟨2866840543111245125823557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30579632459853281342117941 2866840543111245125823557)
                      ·
                        rfl

theorem cell23_5583152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 5].length) (baseStart_5583152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5583152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5583152 prefixEnd_5583152 := by exact prefixLift 5583152
  have htrace : WordTrace (prefixWord ++ tailWord_5583152) baseStart_5583152 baseEnd_5583152 := by
    simpa [prefixWord, tailWord_5583152, baseEnd_5583152] using wordTrace_append hprefix tailTrace_5583152
  have hstable : (prefixWord ++ tailWord_5583152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5583152).length < 2 ^ (prefixWord ++ tailWord_5583152).sum := by decide
  have hdescent : baseEnd_5583152 < baseStart_5583152 := by decide
  rcases family_descends (prefixWord ++ tailWord_5583152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5583156 : List Nat := [2, 5, 1, 1, 1, 2, 1, 2, 2, 3, 3]
def baseStart_5583156 : Nat := 118140960795 + 5583156 * 2 ^ 59
def prefixEnd_5583156 : Nat := 4983230072969 + 3 ^ 40 * 5583156 * 2
def baseEnd_5583156 : Nat := 2866842597033863110173539

theorem tailTrace_5583156 : CollatzResearch.WordTrace tailWord_5583156 prefixEnd_5583156 2866842597033863110173539 := by
  unfold tailWord_5583156
  simp only [CollatzResearch.WordTrace]
  refine ⟨101817214280593406987868661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135756285707457875983824881 101817214280593406987868661)
  ·
    refine ⟨9545363838805631905112687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 101817214280593406987868661 9545363838805631905112687)
    ·
      refine ⟨14318045758208447857669031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9545363838805631905112687 14318045758208447857669031)
      ·
        refine ⟨21477068637312671786503547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14318045758208447857669031 21477068637312671786503547)
        ·
          refine ⟨32215602955969007679755321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21477068637312671786503547 32215602955969007679755321)
          ·
            refine ⟨24161702216976755759816491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32215602955969007679755321 24161702216976755759816491)
            ·
              refine ⟨36242553325465133639724737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24161702216976755759816491 36242553325465133639724737)
              ·
                refine ⟨27181914994098850229793553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36242553325465133639724737 27181914994098850229793553)
                ·
                  refine ⟨20386436245574137672345165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27181914994098850229793553 20386436245574137672345165)
                  ·
                    refine ⟨7644913592090301627129437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20386436245574137672345165 7644913592090301627129437)
                    ·
                      refine ⟨2866842597033863110173539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7644913592090301627129437 2866842597033863110173539)
                      ·
                        rfl

theorem cell23_5583156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 2, 2, 3, 3].length) (baseStart_5583156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5583156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5583156 prefixEnd_5583156 := by exact prefixLift 5583156
  have htrace : WordTrace (prefixWord ++ tailWord_5583156) baseStart_5583156 baseEnd_5583156 := by
    simpa [prefixWord, tailWord_5583156, baseEnd_5583156] using wordTrace_append hprefix tailTrace_5583156
  have hstable : (prefixWord ++ tailWord_5583156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5583156).length < 2 ^ (prefixWord ++ tailWord_5583156).sum := by decide
  have hdescent : baseEnd_5583156 < baseStart_5583156 := by decide
  rcases family_descends (prefixWord ++ tailWord_5583156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5583179 : List Nat := [1, 1, 1, 1, 3, 1, 1, 5, 1, 6, 2]
def baseStart_5583179 : Nat := 118140960795 + 5583179 * 2 ^ 59
def prefixEnd_5583179 : Nat := 4983230072969 + 3 ^ 40 * 5583179 * 2
def baseEnd_5583179 : Nat := 2866854407088916520185933

theorem tailTrace_5583179 : CollatzResearch.WordTrace tailWord_5583179 prefixEnd_5583179 2866854407088916520185933 := by
  unfold tailWord_5583179
  simp only [CollatzResearch.WordTrace]
  refine ⟨203635267440103488903824591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135756844960068992602549727 203635267440103488903824591)
  ·
    refine ⟨305452901160155233355736887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203635267440103488903824591 305452901160155233355736887)
    ·
      refine ⟨458179351740232850033605331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305452901160155233355736887 458179351740232850033605331)
      ·
        refine ⟨687269027610349275050407997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 458179351740232850033605331 687269027610349275050407997)
        ·
          refine ⟨257725885353880978143902999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 687269027610349275050407997 257725885353880978143902999)
          ·
            refine ⟨386588828030821467215854499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 257725885353880978143902999 386588828030821467215854499)
            ·
              refine ⟨579883242046232200823781749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 386588828030821467215854499 579883242046232200823781749)
              ·
                refine ⟨54364053941834268827229539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 579883242046232200823781749 54364053941834268827229539)
                ·
                  refine ⟨81546080912751403240844309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54364053941834268827229539 81546080912751403240844309)
                  ·
                    refine ⟨3822472542785222026914577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 81546080912751403240844309 3822472542785222026914577)
                    ·
                      refine ⟨2866854407088916520185933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3822472542785222026914577 2866854407088916520185933)
                      ·
                        rfl

theorem cell23_5583179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 5, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 5, 1, 6, 2].length) (baseStart_5583179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5583179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5583179 prefixEnd_5583179 := by exact prefixLift 5583179
  have htrace : WordTrace (prefixWord ++ tailWord_5583179) baseStart_5583179 baseEnd_5583179 := by
    simpa [prefixWord, tailWord_5583179, baseEnd_5583179] using wordTrace_append hprefix tailTrace_5583179
  have hstable : (prefixWord ++ tailWord_5583179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5583179).length < 2 ^ (prefixWord ++ tailWord_5583179).sum := by decide
  have hdescent : baseEnd_5583179 < baseStart_5583179 := by decide
  rcases family_descends (prefixWord ++ tailWord_5583179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5583192 : List Nat := [2, 1, 2, 2, 1, 1, 2, 2, 1, 3, 6]
def baseStart_5583192 : Nat := 118140960795 + 5583192 * 2 ^ 59
def prefixEnd_5583192 : Nat := 4983230072969 + 3 ^ 40 * 5583192 * 2
def baseEnd_5583192 : Nat := 2866861082337424969323373

theorem tailTrace_5583192 : CollatzResearch.WordTrace tailWord_5583192 prefixEnd_5583192 2866861082337424969323373 := by
  unfold tailWord_5583192
  simp only [CollatzResearch.WordTrace]
  refine ⟨101817870794528196062023915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135757161059370928082698553 101817870794528196062023915)
  ·
    refine ⟨152726806191792294093035873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101817870794528196062023915 152726806191792294093035873)
    ·
      refine ⟨114545104643844220569776905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152726806191792294093035873 114545104643844220569776905)
      ·
        refine ⟨85908828482883165427332679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114545104643844220569776905 85908828482883165427332679)
        ·
          refine ⟨128863242724324748140999019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85908828482883165427332679 128863242724324748140999019)
          ·
            refine ⟨193294864086487122211498529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128863242724324748140999019 193294864086487122211498529)
            ·
              refine ⟨144971148064865341658623897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 193294864086487122211498529 144971148064865341658623897)
              ·
                refine ⟨108728361048649006243967923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 144971148064865341658623897 108728361048649006243967923)
                ·
                  refine ⟨163092541572973509365951885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 108728361048649006243967923 163092541572973509365951885)
                  ·
                    refine ⟨61159703089865066012231957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 163092541572973509365951885 61159703089865066012231957)
                    ·
                      refine ⟨2866861082337424969323373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61159703089865066012231957 2866861082337424969323373)
                      ·
                        rfl

theorem cell23_5583192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 1, 3, 6].length) (baseStart_5583192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5583192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5583192 prefixEnd_5583192 := by exact prefixLift 5583192
  have htrace : WordTrace (prefixWord ++ tailWord_5583192) baseStart_5583192 baseEnd_5583192 := by
    simpa [prefixWord, tailWord_5583192, baseEnd_5583192] using wordTrace_append hprefix tailTrace_5583192
  have hstable : (prefixWord ++ tailWord_5583192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5583192).length < 2 ^ (prefixWord ++ tailWord_5583192).sum := by decide
  have hdescent : baseEnd_5583192 < baseStart_5583192 := by decide
  rcases family_descends (prefixWord ++ tailWord_5583192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5583199 : List Nat := [1, 1, 2, 3, 1, 2, 4, 1, 1, 4, 3]
def baseStart_5583199 : Nat := 118140960795 + 5583199 * 2 ^ 59
def prefixEnd_5583199 : Nat := 4983230072969 + 3 ^ 40 * 5583199 * 2
def baseEnd_5583199 : Nat := 2866864676702006441935841

theorem tailTrace_5583199 : CollatzResearch.WordTrace tailWord_5583199 prefixEnd_5583199 2866864676702006441935841 := by
  unfold tailWord_5583199
  simp only [CollatzResearch.WordTrace]
  refine ⟨203635996900031032319552651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135757331266687354879701767 203635996900031032319552651)
  ·
    refine ⟨305453995350046548479328977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203635996900031032319552651 305453995350046548479328977)
    ·
      refine ⟨229090496512534911359496733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 305453995350046548479328977 229090496512534911359496733)
      ·
        refine ⟨85908936192200591759811275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 229090496512534911359496733 85908936192200591759811275)
        ·
          refine ⟨128863404288300887639716913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85908936192200591759811275 128863404288300887639716913)
          ·
            refine ⟨96647553216225665729787685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128863404288300887639716913 96647553216225665729787685)
            ·
              refine ⟨18121416228042312324335191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 96647553216225665729787685 18121416228042312324335191)
              ·
                refine ⟨27182124342063468486502787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18121416228042312324335191 27182124342063468486502787)
                ·
                  refine ⟨40773186513095202729754181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27182124342063468486502787 40773186513095202729754181)
                  ·
                    refine ⟨7644972471205350511828909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40773186513095202729754181 7644972471205350511828909)
                    ·
                      refine ⟨2866864676702006441935841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7644972471205350511828909 2866864676702006441935841)
                      ·
                        rfl

theorem cell23_5583199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 1, 1, 4, 3].length) (baseStart_5583199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5583199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5583199 prefixEnd_5583199 := by exact prefixLift 5583199
  have htrace : WordTrace (prefixWord ++ tailWord_5583199) baseStart_5583199 baseEnd_5583199 := by
    simpa [prefixWord, tailWord_5583199, baseEnd_5583199] using wordTrace_append hprefix tailTrace_5583199
  have hstable : (prefixWord ++ tailWord_5583199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5583199).length < 2 ^ (prefixWord ++ tailWord_5583199).sum := by decide
  have hdescent : baseEnd_5583199 < baseStart_5583199 := by decide
  rcases family_descends (prefixWord ++ tailWord_5583199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5583216 : List Nat := [2, 1, 1, 1, 4, 4, 1, 2, 2, 2, 3]
def baseStart_5583216 : Nat := 118140960795 + 5583216 * 2 ^ 59
def prefixEnd_5583216 : Nat := 4983230072969 + 3 ^ 40 * 5583216 * 2
def baseEnd_5583216 : Nat := 2866873405873132875423263

theorem tailTrace_5583216 : CollatzResearch.WordTrace tailWord_5583216 prefixEnd_5583216 2866873405873132875423263 := by
  unfold tailWord_5583216
  simp only [CollatzResearch.WordTrace]
  refine ⟨101818308470484722111460751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135757744627312962815281001 101818308470484722111460751)
  ·
    refine ⟨152727462705727083167191127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101818308470484722111460751 152727462705727083167191127)
    ·
      refine ⟨229091194058590624750786691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152727462705727083167191127 229091194058590624750786691)
      ·
        refine ⟨343636791087885937126180037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229091194058590624750786691 343636791087885937126180037)
        ·
          refine ⟨64431898328978613211158757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 343636791087885937126180037 64431898328978613211158757)
          ·
            refine ⟨12080980936683489977092267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64431898328978613211158757 12080980936683489977092267)
            ·
              refine ⟨18121471405025234965638401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12080980936683489977092267 18121471405025234965638401)
              ·
                refine ⟨13591103553768926224228801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18121471405025234965638401 13591103553768926224228801)
                ·
                  refine ⟨10193327665326694668171601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13591103553768926224228801 10193327665326694668171601)
                  ·
                    refine ⟨7644995748995021001128701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10193327665326694668171601 7644995748995021001128701)
                    ·
                      refine ⟨2866873405873132875423263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7644995748995021001128701 2866873405873132875423263)
                      ·
                        rfl

theorem cell23_5583216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 2, 2, 2, 3].length) (baseStart_5583216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5583216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5583216 prefixEnd_5583216 := by exact prefixLift 5583216
  have htrace : WordTrace (prefixWord ++ tailWord_5583216) baseStart_5583216 baseEnd_5583216 := by
    simpa [prefixWord, tailWord_5583216, baseEnd_5583216] using wordTrace_append hprefix tailTrace_5583216
  have hstable : (prefixWord ++ tailWord_5583216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5583216).length < 2 ^ (prefixWord ++ tailWord_5583216).sum := by decide
  have hdescent : baseEnd_5583216 < baseStart_5583216 := by decide
  rcases family_descends (prefixWord ++ tailWord_5583216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5583232 : List Nat := [2, 1, 1, 2, 1, 2, 1, 1, 1, 11]
def baseStart_5583232 : Nat := 118140960795 + 5583232 * 2 ^ 59
def prefixEnd_5583232 : Nat := 4983230072969 + 3 ^ 40 * 5583232 * 2
def baseEnd_5583232 : Nat := 955627207187868270941063

theorem tailTrace_5583232 : CollatzResearch.WordTrace tailWord_5583232 prefixEnd_5583232 955627207187868270941063 := by
  unfold tailWord_5583232
  simp only [CollatzResearch.WordTrace]
  refine ⟨101818600254455739477751975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135758133672607652637002633 101818600254455739477751975)
  ·
    refine ⟨152727900381683609216627963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101818600254455739477751975 152727900381683609216627963)
    ·
      refine ⟨229091850572525413824941945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152727900381683609216627963 229091850572525413824941945)
      ·
        refine ⟨171818887929394060368706459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 229091850572525413824941945 171818887929394060368706459)
        ·
          refine ⟨257728331894091090553059689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171818887929394060368706459 257728331894091090553059689)
          ·
            refine ⟨193296248920568317914794767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 257728331894091090553059689 193296248920568317914794767)
            ·
              refine ⟨289944373380852476872192151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 193296248920568317914794767 289944373380852476872192151)
              ·
                refine ⟨434916560071278715308288227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 289944373380852476872192151 434916560071278715308288227)
                ·
                  refine ⟨652374840106918072962432341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 434916560071278715308288227 652374840106918072962432341)
                  ·
                    refine ⟨955627207187868270941063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 652374840106918072962432341 955627207187868270941063)
                    ·
                      rfl

theorem cell23_5583232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 1, 11].length) (baseStart_5583232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5583232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5583232 prefixEnd_5583232 := by exact prefixLift 5583232
  have htrace : WordTrace (prefixWord ++ tailWord_5583232) baseStart_5583232 baseEnd_5583232 := by
    simpa [prefixWord, tailWord_5583232, baseEnd_5583232] using wordTrace_append hprefix tailTrace_5583232
  have hstable : (prefixWord ++ tailWord_5583232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5583232).length < 2 ^ (prefixWord ++ tailWord_5583232).sum := by decide
  have hdescent : baseEnd_5583232 < baseStart_5583232 := by decide
  rcases family_descends (prefixWord ++ tailWord_5583232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5583274 : List Nat := [3, 1, 6, 1, 1, 1, 1, 4, 1, 4]
def baseStart_5583274 : Nat := 118140960795 + 5583274 * 2 ^ 59
def prefixEnd_5583274 : Nat := 4983230072969 + 3 ^ 40 * 5583274 * 2
def baseEnd_5583274 : Nat := 955634395917031216165999

theorem tailTrace_5583274 : CollatzResearch.WordTrace tailWord_5583274 prefixEnd_5583274 955634395917031216165999 := by
  unfold tailWord_5583274
  simp only [CollatzResearch.WordTrace]
  refine ⟨50909683093689830032133219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135759154916506213419021917 50909683093689830032133219)
  ·
    refine ⟨76364524640534745048199829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50909683093689830032133219 76364524640534745048199829)
    ·
      refine ⟨3579587092525066174134367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 76364524640534745048199829 3579587092525066174134367)
      ·
        refine ⟨5369380638787599261201551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3579587092525066174134367 5369380638787599261201551)
        ·
          refine ⟨8054070958181398891802327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5369380638787599261201551 8054070958181398891802327)
          ·
            refine ⟨12081106437272098337703491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8054070958181398891802327 12081106437272098337703491)
            ·
              refine ⟨18121659655908147506555237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12081106437272098337703491 18121659655908147506555237)
              ·
                refine ⟨3397811185482777657479107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18121659655908147506555237 3397811185482777657479107)
                ·
                  refine ⟨5096716778224166486218661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3397811185482777657479107 5096716778224166486218661)
                  ·
                    refine ⟨955634395917031216165999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5096716778224166486218661 955634395917031216165999)
                    ·
                      rfl

theorem cell23_5583274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_5583274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5583274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5583274 prefixEnd_5583274 := by exact prefixLift 5583274
  have htrace : WordTrace (prefixWord ++ tailWord_5583274) baseStart_5583274 baseEnd_5583274 := by
    simpa [prefixWord, tailWord_5583274, baseEnd_5583274] using wordTrace_append hprefix tailTrace_5583274
  have hstable : (prefixWord ++ tailWord_5583274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5583274).length < 2 ^ (prefixWord ++ tailWord_5583274).sum := by decide
  have hdescent : baseEnd_5583274 < baseStart_5583274 := by decide
  rcases family_descends (prefixWord ++ tailWord_5583274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5583303 : List Nat := [1, 1, 4, 1, 1, 4, 1, 1, 5, 2, 2]
def baseStart_5583303 : Nat := 118140960795 + 5583303 * 2 ^ 59
def prefixEnd_5583303 : Nat := 4983230072969 + 3 ^ 40 * 5583303 * 2
def baseEnd_5583303 : Nat := 2866918078690074035035363

theorem tailTrace_5583303 : CollatzResearch.WordTrace tailWord_5583303 prefixEnd_5583303 2866918078690074035035363 := by
  unfold tailWord_5583303
  simp only [CollatzResearch.WordTrace]
  refine ⟨203639790091654258081338563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135759860061102838720892375 203639790091654258081338563)
  ·
    refine ⟨305459685137481387122007845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203639790091654258081338563 305459685137481387122007845)
    ·
      refine ⟨57273690963277760085376471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 305459685137481387122007845 57273690963277760085376471)
      ·
        refine ⟨85910536444916640128064707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57273690963277760085376471 85910536444916640128064707)
        ·
          refine ⟨128865804667374960192097061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85910536444916640128064707 128865804667374960192097061)
          ·
            refine ⟨24162338375132805036018199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 128865804667374960192097061 24162338375132805036018199)
            ·
              refine ⟨36243507562699207554027299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24162338375132805036018199 36243507562699207554027299)
              ·
                refine ⟨54365261344048811331040949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36243507562699207554027299 54365261344048811331040949)
                ·
                  refine ⟨5096743251004576062285089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54365261344048811331040949 5096743251004576062285089)
                  ·
                    refine ⟨3822557438253432046713817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5096743251004576062285089 3822557438253432046713817)
                    ·
                      refine ⟨2866918078690074035035363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3822557438253432046713817 2866918078690074035035363)
                      ·
                        rfl

theorem cell23_5583303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 1, 5, 2, 2].length) (baseStart_5583303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5583303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5583303 prefixEnd_5583303 := by exact prefixLift 5583303
  have htrace : WordTrace (prefixWord ++ tailWord_5583303) baseStart_5583303 baseEnd_5583303 := by
    simpa [prefixWord, tailWord_5583303, baseEnd_5583303] using wordTrace_append hprefix tailTrace_5583303
  have hstable : (prefixWord ++ tailWord_5583303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5583303).length < 2 ^ (prefixWord ++ tailWord_5583303).sum := by decide
  have hdescent : baseEnd_5583303 < baseStart_5583303 := by decide
  rcases family_descends (prefixWord ++ tailWord_5583303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5583306 : List Nat := [3, 1, 2, 1, 2, 2, 1, 3, 3, 2, 3]
def baseStart_5583306 : Nat := 118140960795 + 5583306 * 2 ^ 59
def prefixEnd_5583306 : Nat := 4983230072969 + 3 ^ 40 * 5583306 * 2
def baseEnd_5583306 : Nat := 2866919619132037523297849

theorem tailTrace_5583306 : CollatzResearch.WordTrace tailWord_5583306 prefixEnd_5583306 2866919619132037523297849 := by
  unfold tailWord_5583306
  simp only [CollatzResearch.WordTrace]
  refine ⟨50909974877660847398424443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135759933007095593062465181 50909974877660847398424443)
  ·
    refine ⟨76364962316491271097636665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50909974877660847398424443 76364962316491271097636665)
    ·
      refine ⟨57273721737368453323227499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76364962316491271097636665 57273721737368453323227499)
      ·
        refine ⟨85910582606052679984841249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57273721737368453323227499 85910582606052679984841249)
        ·
          refine ⟨64432936954539509988630937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85910582606052679984841249 64432936954539509988630937)
          ·
            refine ⟨48324702715904632491473203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64432936954539509988630937 48324702715904632491473203)
            ·
              refine ⟨72487054073856948737209805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48324702715904632491473203 72487054073856948737209805)
              ·
                refine ⟨27182645277696355776453677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72487054073856948737209805 27182645277696355776453677)
                ·
                  refine ⟨10193491979136133416170129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27182645277696355776453677 10193491979136133416170129)
                  ·
                    refine ⟨7645118984352100062127597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10193491979136133416170129 7645118984352100062127597)
                    ·
                      refine ⟨2866919619132037523297849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7645118984352100062127597 2866919619132037523297849)
                      ·
                        rfl

theorem cell23_5583306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 3, 3, 2, 3].length) (baseStart_5583306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5583306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5583306 prefixEnd_5583306 := by exact prefixLift 5583306
  have htrace : WordTrace (prefixWord ++ tailWord_5583306) baseStart_5583306 baseEnd_5583306 := by
    simpa [prefixWord, tailWord_5583306, baseEnd_5583306] using wordTrace_append hprefix tailTrace_5583306
  have hstable : (prefixWord ++ tailWord_5583306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5583306).length < 2 ^ (prefixWord ++ tailWord_5583306).sum := by decide
  have hdescent : baseEnd_5583306 < baseStart_5583306 := by decide
  rcases family_descends (prefixWord ++ tailWord_5583306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5583314 : List Nat := [3, 2, 2, 4, 1, 1, 2, 3, 1, 1, 3]
def baseStart_5583314 : Nat := 118140960795 + 5583314 * 2 ^ 59
def prefixEnd_5583314 : Nat := 4983230072969 + 3 ^ 40 * 5583314 * 2
def baseEnd_5583314 : Nat := 2866923726977273491997813

theorem tailTrace_5583314 : CollatzResearch.WordTrace tailWord_5583314 prefixEnd_5583314 2866923726977273491997813 := by
  unfold tailWord_5583314
  simp only [CollatzResearch.WordTrace]
  refine ⟨50910047823653601739997249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135760127529742937973325997 50910047823653601739997249)
  ·
    refine ⟨38182535867740201304997937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50910047823653601739997249 38182535867740201304997937)
    ·
      refine ⟨28636901900805150978748453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38182535867740201304997937 28636901900805150978748453)
      ·
        refine ⟨5369419106400965808515335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28636901900805150978748453 5369419106400965808515335)
        ·
          refine ⟨8054128659601448712773003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5369419106400965808515335 8054128659601448712773003)
          ·
            refine ⟨12081192989402173069159505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8054128659601448712773003 12081192989402173069159505)
            ·
              refine ⟨9060894742051629801869629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12081192989402173069159505 9060894742051629801869629)
              ·
                refine ⟨3397835528269361175701111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9060894742051629801869629 3397835528269361175701111)
                ·
                  refine ⟨5096753292404041763551667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3397835528269361175701111 5096753292404041763551667)
                  ·
                    refine ⟨7645129938606062645327501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5096753292404041763551667 7645129938606062645327501)
                    ·
                      refine ⟨2866923726977273491997813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7645129938606062645327501 2866923726977273491997813)
                      ·
                        rfl

theorem cell23_5583314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_5583314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5583314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5583314 prefixEnd_5583314 := by exact prefixLift 5583314
  have htrace : WordTrace (prefixWord ++ tailWord_5583314) baseStart_5583314 baseEnd_5583314 := by
    simpa [prefixWord, tailWord_5583314, baseEnd_5583314] using wordTrace_append hprefix tailTrace_5583314
  have hstable : (prefixWord ++ tailWord_5583314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5583314).length < 2 ^ (prefixWord ++ tailWord_5583314).sum := by decide
  have hdescent : baseEnd_5583314 < baseStart_5583314 := by decide
  rcases family_descends (prefixWord ++ tailWord_5583314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5583353 : List Nat := [1, 2, 1, 3, 1, 2, 2, 5, 2, 1, 3]
def baseStart_5583353 : Nat := 118140960795 + 5583353 * 2 ^ 59
def prefixEnd_5583353 : Nat := 4983230072969 + 3 ^ 40 * 5583353 * 2
def baseEnd_5583353 : Nat := 2866943752722798839410133

theorem tailTrace_5583353 : CollatzResearch.WordTrace tailWord_5583353 prefixEnd_5583353 2866943752722798839410133 := by
  unfold tailWord_5583353
  simp only [CollatzResearch.WordTrace]
  refine ⟨203641613741473116620658713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135761075827648744413772475 203641613741473116620658713)
  ·
    refine ⟨152731210306104837465494035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203641613741473116620658713 152731210306104837465494035)
    ·
      refine ⟨229096815459157256198241053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152731210306104837465494035 229096815459157256198241053)
      ·
        refine ⟨85911305797183971074340395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 229096815459157256198241053 85911305797183971074340395)
        ·
          refine ⟨128866958695775956611510593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85911305797183971074340395 128866958695775956611510593)
          ·
            refine ⟨96650219021831967458632945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128866958695775956611510593 96650219021831967458632945)
            ·
              refine ⟨72487664266373975593974709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96650219021831967458632945 72487664266373975593974709)
              ·
                refine ⟨6795718524972560211935129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 72487664266373975593974709 6795718524972560211935129)
                ·
                  refine ⟨5096788893729420158951347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6795718524972560211935129 5096788893729420158951347)
                  ·
                    refine ⟨7645183340594130238427021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5096788893729420158951347 7645183340594130238427021)
                    ·
                      refine ⟨2866943752722798839410133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7645183340594130238427021 2866943752722798839410133)
                      ·
                        rfl

theorem cell23_5583353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 5, 2, 1, 3].length) (baseStart_5583353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5583353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5583353 prefixEnd_5583353 := by exact prefixLift 5583353
  have htrace : WordTrace (prefixWord ++ tailWord_5583353) baseStart_5583353 baseEnd_5583353 := by
    simpa [prefixWord, tailWord_5583353, baseEnd_5583353] using wordTrace_append hprefix tailTrace_5583353
  have hstable : (prefixWord ++ tailWord_5583353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5583353).length < 2 ^ (prefixWord ++ tailWord_5583353).sum := by decide
  have hdescent : baseEnd_5583353 < baseStart_5583353 := by decide
  rcases family_descends (prefixWord ++ tailWord_5583353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5583369 : List Nat := [1, 2, 1, 1, 3, 1, 2, 2, 4, 6]
def baseStart_5583369 : Nat := 118140960795 + 5583369 * 2 ^ 59
def prefixEnd_5583369 : Nat := 4983230072969 + 3 ^ 40 * 5583369 * 2
def baseEnd_5583369 : Nat := 955650656137756925603353

theorem tailTrace_5583369 : CollatzResearch.WordTrace tailWord_5583369 prefixEnd_5583369 955650656137756925603353 := by
  unfold tailWord_5583369
  simp only [CollatzResearch.WordTrace]
  refine ⟨203642197309415151353241161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135761464872943434235494107 203642197309415151353241161)
  ·
    refine ⟨152731647982061363514930871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203642197309415151353241161 152731647982061363514930871)
    ·
      refine ⟨229097471973092045272396307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152731647982061363514930871 229097471973092045272396307)
      ·
        refine ⟨343646207959638067908594461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229097471973092045272396307 343646207959638067908594461)
        ·
          refine ⟨128867327984864275465722923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 343646207959638067908594461 128867327984864275465722923)
          ·
            refine ⟨193300991977296413198584385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128867327984864275465722923 193300991977296413198584385)
            ·
              refine ⟨144975743982972309898938289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 193300991977296413198584385 144975743982972309898938289)
              ·
                refine ⟨108731807987229232424203717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 144975743982972309898938289 108731807987229232424203717)
                ·
                  refine ⟨20387213997605481079538197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 108731807987229232424203717 20387213997605481079538197)
                  ·
                    refine ⟨955650656137756925603353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20387213997605481079538197 955650656137756925603353)
                    ·
                      rfl

theorem cell23_5583369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 4, 6].length) (baseStart_5583369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5583369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5583369 prefixEnd_5583369 := by exact prefixLift 5583369
  have htrace : WordTrace (prefixWord ++ tailWord_5583369) baseStart_5583369 baseEnd_5583369 := by
    simpa [prefixWord, tailWord_5583369, baseEnd_5583369] using wordTrace_append hprefix tailTrace_5583369
  have hstable : (prefixWord ++ tailWord_5583369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5583369).length < 2 ^ (prefixWord ++ tailWord_5583369).sum := by decide
  have hdescent : baseEnd_5583369 < baseStart_5583369 := by decide
  rcases family_descends (prefixWord ++ tailWord_5583369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5583414 : List Nat := [5, 1, 2, 1, 2, 3, 1, 2, 1, 3, 2]
def baseStart_5583414 : Nat := 118140960795 + 5583414 * 2 ^ 59
def prefixEnd_5583414 : Nat := 4983230072969 + 3 ^ 40 * 5583414 * 2
def baseEnd_5583414 : Nat := 2866975075042723100747353

theorem tailTrace_5583414 : CollatzResearch.WordTrace tailWord_5583414 prefixEnd_5583414 2866975075042723100747353 := by
  unfold tailWord_5583414
  simp only [CollatzResearch.WordTrace]
  refine ⟨12727739912140757752414331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 135762559062834749359086197 12727739912140757752414331)
  ·
    refine ⟨19091609868211136628621497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12727739912140757752414331 19091609868211136628621497)
    ·
      refine ⟨14318707401158352471466123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19091609868211136628621497 14318707401158352471466123)
      ·
        refine ⟨21478061101737528707199185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14318707401158352471466123 21478061101737528707199185)
        ·
          refine ⟨16108545826303146530399389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21478061101737528707199185 16108545826303146530399389)
          ·
            refine ⟨6040704684863679948899771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16108545826303146530399389 6040704684863679948899771)
            ·
              refine ⟨9061057027295519923349657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6040704684863679948899771 9061057027295519923349657)
              ·
                refine ⟨6795792770471639942512243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9061057027295519923349657 6795792770471639942512243)
                ·
                  refine ⟨10193689155707459913768365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6795792770471639942512243 10193689155707459913768365)
                  ·
                    refine ⟨3822633433390297467663137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10193689155707459913768365 3822633433390297467663137)
                    ·
                      refine ⟨2866975075042723100747353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3822633433390297467663137 2866975075042723100747353)
                      ·
                        rfl

theorem cell23_5583414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 2, 1, 3, 2].length) (baseStart_5583414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5583414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5583414 prefixEnd_5583414 := by exact prefixLift 5583414
  have htrace : WordTrace (prefixWord ++ tailWord_5583414) baseStart_5583414 baseEnd_5583414 := by
    simpa [prefixWord, tailWord_5583414, baseEnd_5583414] using wordTrace_append hprefix tailTrace_5583414
  have hstable : (prefixWord ++ tailWord_5583414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5583414).length < 2 ^ (prefixWord ++ tailWord_5583414).sum := by decide
  have hdescent : baseEnd_5583414 < baseStart_5583414 := by decide
  rcases family_descends (prefixWord ++ tailWord_5583414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5583430 : List Nat := [6, 1, 1, 1, 2, 1, 2, 1, 2, 1, 5]
def baseStart_5583430 : Nat := 118140960795 + 5583430 * 2 ^ 59
def prefixEnd_5583430 : Nat := 4983230072969 + 3 ^ 40 * 5583430 * 2
def baseEnd_5583430 : Nat := 2866983290733195038147279

theorem tailTrace_5583430 : CollatzResearch.WordTrace tailWord_5583430 prefixEnd_5583430 2866983290733195038147279 := by
  unfold tailWord_5583430
  simp only [CollatzResearch.WordTrace]
  refine ⟨6363888192568567461600367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 135762948108129439180807829 6363888192568567461600367)
  ·
    refine ⟨9545832288852851192400551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6363888192568567461600367 9545832288852851192400551)
    ·
      refine ⟨14318748433279276788600827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9545832288852851192400551 14318748433279276788600827)
      ·
        refine ⟨21478122649918915182901241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14318748433279276788600827 21478122649918915182901241)
        ·
          refine ⟨16108591987439186387175931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21478122649918915182901241 16108591987439186387175931)
          ·
            refine ⟨24162887981158779580763897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16108591987439186387175931 24162887981158779580763897)
            ·
              refine ⟨18122165985869084685572923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24162887981158779580763897 18122165985869084685572923)
              ·
                refine ⟨27183248978803627028359385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18122165985869084685572923 27183248978803627028359385)
                ·
                  refine ⟨20387436734102720271269539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27183248978803627028359385 20387436734102720271269539)
                  ·
                    refine ⟨30581155101154080406904309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20387436734102720271269539 30581155101154080406904309)
                    ·
                      refine ⟨2866983290733195038147279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30581155101154080406904309 2866983290733195038147279)
                      ·
                        rfl

theorem cell23_5583430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_5583430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5583430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5583430 prefixEnd_5583430 := by exact prefixLift 5583430
  have htrace : WordTrace (prefixWord ++ tailWord_5583430) baseStart_5583430 baseEnd_5583430 := by
    simpa [prefixWord, tailWord_5583430, baseEnd_5583430] using wordTrace_append hprefix tailTrace_5583430
  have hstable : (prefixWord ++ tailWord_5583430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5583430).length < 2 ^ (prefixWord ++ tailWord_5583430).sum := by decide
  have hdescent : baseEnd_5583430 < baseStart_5583430 := by decide
  rcases family_descends (prefixWord ++ tailWord_5583430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5583456 : List Nat := [2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 5]
def baseStart_5583456 : Nat := 118140960795 + 5583456 * 2 ^ 59
def prefixEnd_5583456 : Nat := 4983230072969 + 3 ^ 40 * 5583456 * 2
def baseEnd_5583456 : Nat := 2866996641230211936422159

theorem tailTrace_5583456 : CollatzResearch.WordTrace tailWord_5583456 prefixEnd_5583456 2866996641230211936422159 := by
  unfold tailWord_5583456
  simp only [CollatzResearch.WordTrace]
  refine ⟨101822685230049982605829111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135763580306733310141105481 101822685230049982605829111)
  ·
    refine ⟨152734027845074973908743667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101822685230049982605829111 152734027845074973908743667)
    ·
      refine ⟨229101041767612460863115501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152734027845074973908743667 229101041767612460863115501)
      ·
        refine ⟨85912890662854672823668313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 229101041767612460863115501 85912890662854672823668313)
        ·
          refine ⟨64434667997141004617751235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85912890662854672823668313 64434667997141004617751235)
          ·
            refine ⟨96652001995711506926626853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64434667997141004617751235 96652001995711506926626853)
            ·
              refine ⟨18122250374195907548742535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 96652001995711506926626853 18122250374195907548742535)
              ·
                refine ⟨27183375561293861323113803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18122250374195907548742535 27183375561293861323113803)
                ·
                  refine ⟨40775063341940791984670705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27183375561293861323113803 40775063341940791984670705)
                  ·
                    refine ⟨30581297506455593988503029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40775063341940791984670705 30581297506455593988503029)
                    ·
                      refine ⟨2866996641230211936422159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30581297506455593988503029 2866996641230211936422159)
                      ·
                        rfl

theorem cell23_5583456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 5].length) (baseStart_5583456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5583456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5583456 prefixEnd_5583456 := by exact prefixLift 5583456
  have htrace : WordTrace (prefixWord ++ tailWord_5583456) baseStart_5583456 baseEnd_5583456 := by
    simpa [prefixWord, tailWord_5583456, baseEnd_5583456] using wordTrace_append hprefix tailTrace_5583456
  have hstable : (prefixWord ++ tailWord_5583456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5583456).length < 2 ^ (prefixWord ++ tailWord_5583456).sum := by decide
  have hdescent : baseEnd_5583456 < baseStart_5583456 := by decide
  rcases family_descends (prefixWord ++ tailWord_5583456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5583560 : List Nat := [2, 1, 3, 1, 2, 3, 1, 1, 4, 3, 2]
def baseStart_5583560 : Nat := 118140960795 + 5583560 * 2 ^ 59
def prefixEnd_5583560 : Nat := 4983230072969 + 3 ^ 40 * 5583560 * 2
def baseEnd_5583560 : Nat := 2867050043218279529521681

theorem tailTrace_5583560 : CollatzResearch.WordTrace tailWord_5583560 prefixEnd_5583560 2867050043218279529521681 := by
  unfold tailWord_5583560
  simp only [CollatzResearch.WordTrace]
  refine ⟨101824581825861595486722067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135766109101148793982296089 101824581825861595486722067)
  ·
    refine ⟨152736872738792393230083101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101824581825861595486722067 152736872738792393230083101)
    ·
      refine ⟨57276327277047147461281163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152736872738792393230083101 57276327277047147461281163)
      ·
        refine ⟨85914490915570721191921745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57276327277047147461281163 85914490915570721191921745)
        ·
          refine ⟨64435868186678040893941309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85914490915570721191921745 64435868186678040893941309)
          ·
            refine ⟨24163450570004265335227991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64435868186678040893941309 24163450570004265335227991)
            ·
              refine ⟨36245175855006398002841987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24163450570004265335227991 36245175855006398002841987)
              ·
                refine ⟨54367763782509597004262981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36245175855006398002841987 54367763782509597004262981)
                ·
                  refine ⟨10193955709220549438299309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54367763782509597004262981 10193955709220549438299309)
                  ·
                    refine ⟨3822733390957706039362241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10193955709220549438299309 3822733390957706039362241)
                    ·
                      refine ⟨2867050043218279529521681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3822733390957706039362241 2867050043218279529521681)
                      ·
                        rfl

theorem cell23_5583560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 1, 4, 3, 2].length) (baseStart_5583560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5583560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5583560 prefixEnd_5583560 := by exact prefixLift 5583560
  have htrace : WordTrace (prefixWord ++ tailWord_5583560) baseStart_5583560 baseEnd_5583560 := by
    simpa [prefixWord, tailWord_5583560, baseEnd_5583560] using wordTrace_append hprefix tailTrace_5583560
  have hstable : (prefixWord ++ tailWord_5583560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5583560).length < 2 ^ (prefixWord ++ tailWord_5583560).sum := by decide
  have hdescent : baseEnd_5583560 < baseStart_5583560 := by decide
  rcases family_descends (prefixWord ++ tailWord_5583560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5583587 : List Nat := [1, 1, 1, 7, 1, 3, 1, 2, 1, 5]
def baseStart_5583587 : Nat := 118140960795 + 5583587 * 2 ^ 59
def prefixEnd_5583587 : Nat := 4983230072969 + 3 ^ 40 * 5583587 * 2
def baseEnd_5583587 : Nat := 955687969065316974628019

theorem tailTrace_5583587 : CollatzResearch.WordTrace tailWord_5583587 prefixEnd_5583587 955687969065316974628019 := by
  unfold tailWord_5583587
  simp only [CollatzResearch.WordTrace]
  refine ⟨203650148422625374584677015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135766765615083583056451343 203650148422625374584677015)
  ·
    refine ⟨305475222633938061877015523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203650148422625374584677015 305475222633938061877015523)
    ·
      refine ⟨458212833950907092815523285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305475222633938061877015523 458212833950907092815523285)
      ·
        refine ⟨10739363295724384987863827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 458212833950907092815523285 10739363295724384987863827)
        ·
          refine ⟨16109044943586577481795741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10739363295724384987863827 16109044943586577481795741)
          ·
            refine ⟨6040891853844966555673403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16109044943586577481795741 6040891853844966555673403)
            ·
              refine ⟨9061337780767449833510105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6040891853844966555673403 9061337780767449833510105)
              ·
                refine ⟨6796003335575587375132579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9061337780767449833510105 6796003335575587375132579)
                ·
                  refine ⟨10194005003363381062698869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6796003335575587375132579 10194005003363381062698869)
                  ·
                    refine ⟨955687969065316974628019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10194005003363381062698869 955687969065316974628019)
                    ·
                      rfl

theorem cell23_5583587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 2, 1, 5].length) (baseStart_5583587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5583587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5583587 prefixEnd_5583587 := by exact prefixLift 5583587
  have htrace : WordTrace (prefixWord ++ tailWord_5583587) baseStart_5583587 baseEnd_5583587 := by
    simpa [prefixWord, tailWord_5583587, baseEnd_5583587] using wordTrace_append hprefix tailTrace_5583587
  have hstable : (prefixWord ++ tailWord_5583587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5583587).length < 2 ^ (prefixWord ++ tailWord_5583587).sum := by decide
  have hdescent : baseEnd_5583587 < baseStart_5583587 := by decide
  rcases family_descends (prefixWord ++ tailWord_5583587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5583610 : List Nat := [3, 1, 1, 1, 1, 3, 2, 5, 1, 2, 3]
def baseStart_5583610 : Nat := 118140960795 + 5583610 * 2 ^ 59
def prefixEnd_5583610 : Nat := 4983230072969 + 3 ^ 40 * 5583610 * 2
def baseEnd_5583610 : Nat := 2867075717251004333896451

theorem tailTrace_5583610 : CollatzResearch.WordTrace tailWord_5583610 prefixEnd_5583610 2867075717251004333896451 := by
  unfold tailWord_5583610
  simp only [CollatzResearch.WordTrace]
  refine ⟨50912746825385512378191071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135767324867694699675176189 50912746825385512378191071)
  ·
    refine ⟨76369120238078268567286607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50912746825385512378191071 76369120238078268567286607)
    ·
      refine ⟨114553680357117402850929911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76369120238078268567286607 114553680357117402850929911)
      ·
        refine ⟨171830520535676104276394867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114553680357117402850929911 171830520535676104276394867)
        ·
          refine ⟨257745780803514156414592301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171830520535676104276394867 257745780803514156414592301)
          ·
            refine ⟨96654667801317808655472113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 257745780803514156414592301 96654667801317808655472113)
            ·
              refine ⟨72491000850988356491604085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96654667801317808655472113 72491000850988356491604085)
              ·
                refine ⟨6796031329780158421087883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 72491000850988356491604085 6796031329780158421087883)
                ·
                  refine ⟨10194046994670237631631825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6796031329780158421087883 10194046994670237631631825)
                  ·
                    refine ⟨7645535246002678223723869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10194046994670237631631825 7645535246002678223723869)
                    ·
                      refine ⟨2867075717251004333896451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7645535246002678223723869 2867075717251004333896451)
                      ·
                        rfl

theorem cell23_5583610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 5, 1, 2, 3].length) (baseStart_5583610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5583610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5583610 prefixEnd_5583610 := by exact prefixLift 5583610
  have htrace : WordTrace (prefixWord ++ tailWord_5583610) baseStart_5583610 baseEnd_5583610 := by
    simpa [prefixWord, tailWord_5583610, baseEnd_5583610] using wordTrace_append hprefix tailTrace_5583610
  have hstable : (prefixWord ++ tailWord_5583610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5583610).length < 2 ^ (prefixWord ++ tailWord_5583610).sum := by decide
  have hdescent : baseEnd_5583610 < baseStart_5583610 := by decide
  rcases family_descends (prefixWord ++ tailWord_5583610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5583618 : List Nat := [3, 4, 1, 1, 1, 4, 2, 2, 1, 1, 3]
def baseStart_5583618 : Nat := 118140960795 + 5583618 * 2 ^ 59
def prefixEnd_5583618 : Nat := 4983230072969 + 3 ^ 40 * 5583618 * 2
def baseEnd_5583618 : Nat := 2867079825096240302596415

theorem tailTrace_5583618 : CollatzResearch.WordTrace tailWord_5583618 prefixEnd_5583618 2867079825096240302596415 := by
  unfold tailWord_5583618
  simp only [CollatzResearch.WordTrace]
  refine ⟨50912819771378266719763877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135767519390342044586037005 50912819771378266719763877)
  ·
    refine ⟨9546153707133425009955727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50912819771378266719763877 9546153707133425009955727)
    ·
      refine ⟨14319230560700137514933591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9546153707133425009955727 14319230560700137514933591)
      ·
        refine ⟨21478845841050206272400387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14319230560700137514933591 21478845841050206272400387)
        ·
          refine ⟨32218268761575309408600581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21478845841050206272400387 32218268761575309408600581)
          ·
            refine ⟨6040925392795370514112609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32218268761575309408600581 6040925392795370514112609)
            ·
              refine ⟨4530694044596527885584457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6040925392795370514112609 4530694044596527885584457)
              ·
                refine ⟨3398020533447395914188343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4530694044596527885584457 3398020533447395914188343)
                ·
                  refine ⟨5097030800171093871282515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3398020533447395914188343 5097030800171093871282515)
                  ·
                    refine ⟨7645546200256640806923773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5097030800171093871282515 7645546200256640806923773)
                    ·
                      refine ⟨2867079825096240302596415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7645546200256640806923773 2867079825096240302596415)
                      ·
                        rfl

theorem cell23_5583618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 2, 2, 1, 1, 3].length) (baseStart_5583618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5583618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5583618 prefixEnd_5583618 := by exact prefixLift 5583618
  have htrace : WordTrace (prefixWord ++ tailWord_5583618) baseStart_5583618 baseEnd_5583618 := by
    simpa [prefixWord, tailWord_5583618, baseEnd_5583618] using wordTrace_append hprefix tailTrace_5583618
  have hstable : (prefixWord ++ tailWord_5583618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5583618).length < 2 ^ (prefixWord ++ tailWord_5583618).sum := by decide
  have hdescent : baseEnd_5583618 < baseStart_5583618 := by decide
  rcases family_descends (prefixWord ++ tailWord_5583618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5583640 : List Nat := [2, 1, 2, 3, 1, 1, 1, 2, 6, 1, 3]
def baseStart_5583640 : Nat := 118140960795 + 5583640 * 2 ^ 59
def prefixEnd_5583640 : Nat := 4983230072969 + 3 ^ 40 * 5583640 * 2
def baseEnd_5583640 : Nat := 2867091121670639216521313

theorem tailTrace_5583640 : CollatzResearch.WordTrace tailWord_5583640 prefixEnd_5583640 2867091121670639216521313 := by
  unfold tailWord_5583640
  simp only [CollatzResearch.WordTrace]
  refine ⟨101826040745716682318178187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135768054327622243090904249 101826040745716682318178187)
  ·
    refine ⟨152739061118575023477267281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101826040745716682318178187 152739061118575023477267281)
    ·
      refine ⟨114554295838931267607950461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152739061118575023477267281 114554295838931267607950461)
      ·
        refine ⟨42957860939599225352981423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114554295838931267607950461 42957860939599225352981423)
        ·
          refine ⟨64436791409398838029472135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42957860939599225352981423 64436791409398838029472135)
          ·
            refine ⟨96655187114098257044208203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64436791409398838029472135 96655187114098257044208203)
            ·
              refine ⟨144982780671147385566312305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96655187114098257044208203 144982780671147385566312305)
              ·
                refine ⟨108737085503360539174734229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 144982780671147385566312305 108737085503360539174734229)
                ·
                  refine ⟨5097050882970025273815667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 108737085503360539174734229 5097050882970025273815667)
                  ·
                    refine ⟨7645576324455037910723501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5097050882970025273815667 7645576324455037910723501)
                    ·
                      refine ⟨2867091121670639216521313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7645576324455037910723501 2867091121670639216521313)
                      ·
                        rfl

theorem cell23_5583640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 6, 1, 3].length) (baseStart_5583640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5583640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5583640 prefixEnd_5583640 := by exact prefixLift 5583640
  have htrace : WordTrace (prefixWord ++ tailWord_5583640) baseStart_5583640 baseEnd_5583640 := by
    simpa [prefixWord, tailWord_5583640, baseEnd_5583640] using wordTrace_append hprefix tailTrace_5583640
  have hstable : (prefixWord ++ tailWord_5583640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5583640).length < 2 ^ (prefixWord ++ tailWord_5583640).sum := by decide
  have hdescent : baseEnd_5583640 < baseStart_5583640 := by decide
  rcases family_descends (prefixWord ++ tailWord_5583640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5583653 : List Nat := [1, 3, 1, 2, 3, 1, 2, 1, 2, 2, 5]
def baseStart_5583653 : Nat := 118140960795 + 5583653 * 2 ^ 59
def prefixEnd_5583653 : Nat := 4983230072969 + 3 ^ 40 * 5583653 * 2
def baseEnd_5583653 : Nat := 2867097796919147665658753

theorem tailTrace_5583653 : CollatzResearch.WordTrace tailWord_5583653 prefixEnd_5583653 2867097796919147665658753 := by
  unfold tailWord_5583653
  simp only [CollatzResearch.WordTrace]
  refine ⟨203652555640386267856579613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135768370426924178571053075 203652555640386267856579613)
  ·
    refine ⟨76369708365144850446217355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 203652555640386267856579613 76369708365144850446217355)
    ·
      refine ⟨114554562547717275669326033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76369708365144850446217355 114554562547717275669326033)
      ·
        refine ⟨85915921910787956751994525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114554562547717275669326033 85915921910787956751994525)
        ·
          refine ⟨32218470716545483781997947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85915921910787956751994525 32218470716545483781997947)
          ·
            refine ⟨48327706074818225672996921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32218470716545483781997947 48327706074818225672996921)
            ·
              refine ⟨36245779556113669254747691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48327706074818225672996921 36245779556113669254747691)
              ·
                refine ⟨54368669334170503882121537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36245779556113669254747691 54368669334170503882121537)
                ·
                  refine ⟨40776502000627877911591153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54368669334170503882121537 40776502000627877911591153)
                  ·
                    refine ⟨30582376500470908433693365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40776502000627877911591153 30582376500470908433693365)
                    ·
                      refine ⟨2867097796919147665658753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30582376500470908433693365 2867097796919147665658753)
                      ·
                        rfl

theorem cell23_5583653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 1, 2, 2, 5].length) (baseStart_5583653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5583653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5583653 prefixEnd_5583653 := by exact prefixLift 5583653
  have htrace : WordTrace (prefixWord ++ tailWord_5583653) baseStart_5583653 baseEnd_5583653 := by
    simpa [prefixWord, tailWord_5583653, baseEnd_5583653] using wordTrace_append hprefix tailTrace_5583653
  have hstable : (prefixWord ++ tailWord_5583653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5583653).length < 2 ^ (prefixWord ++ tailWord_5583653).sum := by decide
  have hdescent : baseEnd_5583653 < baseStart_5583653 := by decide
  rcases family_descends (prefixWord ++ tailWord_5583653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5583658 : List Nat := [3, 1, 4, 3, 2, 1, 2, 1, 1, 1, 4]
def baseStart_5583658 : Nat := 118140960795 + 5583658 * 2 ^ 59
def prefixEnd_5583658 : Nat := 4983230072969 + 3 ^ 40 * 5583658 * 2
def baseEnd_5583658 : Nat := 2867100364322420146096231

theorem tailTrace_5583658 : CollatzResearch.WordTrace tailWord_5583658 prefixEnd_5583658 2867100364322420146096231 := by
  unfold tailWord_5583658
  simp only [CollatzResearch.WordTrace]
  refine ⟨50913184501342038427627907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135768492003578769140341085 50913184501342038427627907)
  ·
    refine ⟨76369776752013057641441861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50913184501342038427627907 76369776752013057641441861)
    ·
      refine ⟨14319333141002448307770349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76369776752013057641441861 14319333141002448307770349)
      ·
        refine ⟨5369749927875918115413881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14319333141002448307770349 5369749927875918115413881)
        ·
          refine ⟨4027312445906938586560411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5369749927875918115413881 4027312445906938586560411)
          ·
            refine ⟨6040968668860407879840617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4027312445906938586560411 6040968668860407879840617)
            ·
              refine ⟨4530726501645305909880463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6040968668860407879840617 4530726501645305909880463)
              ·
                refine ⟨6796089752467958864820695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4530726501645305909880463 6796089752467958864820695)
                ·
                  refine ⟨10194134628701938297231043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6796089752467958864820695 10194134628701938297231043)
                  ·
                    refine ⟨15291201943052907445846565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10194134628701938297231043 15291201943052907445846565)
                    ·
                      refine ⟨2867100364322420146096231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15291201943052907445846565 2867100364322420146096231)
                      ·
                        rfl

theorem cell23_5583658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_5583658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5583658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5583658 prefixEnd_5583658 := by exact prefixLift 5583658
  have htrace : WordTrace (prefixWord ++ tailWord_5583658) baseStart_5583658 baseEnd_5583658 := by
    simpa [prefixWord, tailWord_5583658, baseEnd_5583658] using wordTrace_append hprefix tailTrace_5583658
  have hstable : (prefixWord ++ tailWord_5583658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5583658).length < 2 ^ (prefixWord ++ tailWord_5583658).sum := by decide
  have hdescent : baseEnd_5583658 < baseStart_5583658 := by decide
  rcases family_descends (prefixWord ++ tailWord_5583658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5583661 : List Nat := [1, 5, 3, 2, 1, 1, 1, 3, 1, 2, 3]
def baseStart_5583661 : Nat := 118140960795 + 5583661 * 2 ^ 59
def prefixEnd_5583661 : Nat := 4983230072969 + 3 ^ 40 * 5583661 * 2
def baseEnd_5583661 : Nat := 2867101904764383634358717

theorem tailTrace_5583661 : CollatzResearch.WordTrace tailWord_5583661 prefixEnd_5583661 2867101904764383634358717 := by
  unfold tailWord_5583661
  simp only [CollatzResearch.WordTrace]
  refine ⟨203652847424357285222870837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135768564949571523481913891 203652847424357285222870837)
  ·
    refine ⟨19092454446033495489644141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 203652847424357285222870837 19092454446033495489644141)
    ·
      refine ⟨7159670417262560808616553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19092454446033495489644141 7159670417262560808616553)
      ·
        refine ⟨5369752812946920606462415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7159670417262560808616553 5369752812946920606462415)
        ·
          refine ⟨8054629219420380909693623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5369752812946920606462415 8054629219420380909693623)
          ·
            refine ⟨12081943829130571364540435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8054629219420380909693623 12081943829130571364540435)
            ·
              refine ⟨18122915743695857046810653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12081943829130571364540435 18122915743695857046810653)
              ·
                refine ⟨6796093403885946392553995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18122915743695857046810653 6796093403885946392553995)
                ·
                  refine ⟨10194140105828919588830993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6796093403885946392553995 10194140105828919588830993)
                  ·
                    refine ⟨7645605079371689691623245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10194140105828919588830993 7645605079371689691623245)
                    ·
                      refine ⟨2867101904764383634358717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7645605079371689691623245 2867101904764383634358717)
                      ·
                        rfl

theorem cell23_5583661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_5583661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5583661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5583661 prefixEnd_5583661 := by exact prefixLift 5583661
  have htrace : WordTrace (prefixWord ++ tailWord_5583661) baseStart_5583661 baseEnd_5583661 := by
    simpa [prefixWord, tailWord_5583661, baseEnd_5583661] using wordTrace_append hprefix tailTrace_5583661
  have hstable : (prefixWord ++ tailWord_5583661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5583661).length < 2 ^ (prefixWord ++ tailWord_5583661).sum := by decide
  have hdescent : baseEnd_5583661 < baseStart_5583661 := by decide
  rcases family_descends (prefixWord ++ tailWord_5583661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5583680 : List Nat := [2, 1, 1, 2, 2, 1, 1, 4, 3, 4, 2]
def baseStart_5583680 : Nat := 118140960795 + 5583680 * 2 ^ 59
def prefixEnd_5583680 : Nat := 4983230072969 + 3 ^ 40 * 5583680 * 2
def baseEnd_5583680 : Nat := 2867111660896819060021129

theorem tailTrace_5583680 : CollatzResearch.WordTrace tailWord_5583680 prefixEnd_5583680 2867111660896819060021129 := by
  unfold tailWord_5583680
  simp only [CollatzResearch.WordTrace]
  refine ⟨101826770205644225733906247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135769026940858967645208329 101826770205644225733906247)
  ·
    refine ⟨152740155308466338600859371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101826770205644225733906247 152740155308466338600859371)
    ·
      refine ⟨229110232962699507901289057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152740155308466338600859371 229110232962699507901289057)
      ·
        refine ⟨171832674722024630925966793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 229110232962699507901289057 171832674722024630925966793)
        ·
          refine ⟨128874506041518473194475095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171832674722024630925966793 128874506041518473194475095)
          ·
            refine ⟨193311759062277709791712643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128874506041518473194475095 193311759062277709791712643)
            ·
              refine ⟨289967638593416564687568965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 193311759062277709791712643 289967638593416564687568965)
              ·
                refine ⟨54368932236265605878919181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 289967638593416564687568965 54368932236265605878919181)
                ·
                  refine ⟨20388349588599602204594693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54368932236265605878919181 20388349588599602204594693)
                  ·
                    refine ⟨3822815547862425413361505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20388349588599602204594693 3822815547862425413361505)
                    ·
                      refine ⟨2867111660896819060021129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3822815547862425413361505 2867111660896819060021129)
                      ·
                        rfl

theorem cell23_5583680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 4, 3, 4, 2].length) (baseStart_5583680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5583680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5583680 prefixEnd_5583680 := by exact prefixLift 5583680
  have htrace : WordTrace (prefixWord ++ tailWord_5583680) baseStart_5583680 baseEnd_5583680 := by
    simpa [prefixWord, tailWord_5583680, baseEnd_5583680] using wordTrace_append hprefix tailTrace_5583680
  have hstable : (prefixWord ++ tailWord_5583680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5583680).length < 2 ^ (prefixWord ++ tailWord_5583680).sum := by decide
  have hdescent : baseEnd_5583680 < baseStart_5583680 := by decide
  rcases family_descends (prefixWord ++ tailWord_5583680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5583730 : List Nat := [3, 2, 1, 2, 1, 1, 2, 1, 4, 3, 3]
def baseStart_5583730 : Nat := 118140960795 + 5583730 * 2 ^ 59
def prefixEnd_5583730 : Nat := 4983230072969 + 3 ^ 40 * 5583730 * 2
def baseEnd_5583730 : Nat := 2867137334929543864395899

theorem tailTrace_5583730 : CollatzResearch.WordTrace tailWord_5583730 prefixEnd_5583730 2867137334929543864395899 := by
  unfold tailWord_5583730
  simp only [CollatzResearch.WordTrace]
  refine ⟨50913841015276827501783161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135770242707404873338088429 50913841015276827501783161)
  ·
    refine ⟨38185380761457620626337371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50913841015276827501783161 38185380761457620626337371)
    ·
      refine ⟨57278071142186430939506057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38185380761457620626337371 57278071142186430939506057)
      ·
        refine ⟨42958553356639823204629543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57278071142186430939506057 42958553356639823204629543)
        ·
          refine ⟨64437830034959734806944315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42958553356639823204629543 64437830034959734806944315)
          ·
            refine ⟨96656745052439602210416473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64437830034959734806944315 96656745052439602210416473)
            ·
              refine ⟨72492558789329701657812355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96656745052439602210416473 72492558789329701657812355)
              ·
                refine ⟨108738838183994552486718533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72492558789329701657812355 108738838183994552486718533)
                ·
                  refine ⟨20388532159498978591259725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 108738838183994552486718533 20388532159498978591259725)
                  ·
                    refine ⟨7645699559812116971722397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20388532159498978591259725 7645699559812116971722397)
                    ·
                      refine ⟨2867137334929543864395899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7645699559812116971722397 2867137334929543864395899)
                      ·
                        rfl

theorem cell23_5583730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 4, 3, 3].length) (baseStart_5583730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5583730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5583730 prefixEnd_5583730 := by exact prefixLift 5583730
  have htrace : WordTrace (prefixWord ++ tailWord_5583730) baseStart_5583730 baseEnd_5583730 := by
    simpa [prefixWord, tailWord_5583730, baseEnd_5583730] using wordTrace_append hprefix tailTrace_5583730
  have hstable : (prefixWord ++ tailWord_5583730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5583730).length < 2 ^ (prefixWord ++ tailWord_5583730).sum := by decide
  have hdescent : baseEnd_5583730 < baseStart_5583730 := by decide
  rcases family_descends (prefixWord ++ tailWord_5583730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5583743 : List Nat := [1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 7]
def baseStart_5583743 : Nat := 118140960795 + 5583743 * 2 ^ 59
def prefixEnd_5583743 : Nat := 4983230072969 + 3 ^ 40 * 5583743 * 2
def baseEnd_5583743 : Nat := 2867144010178052313533339

theorem tailTrace_5583743 : CollatzResearch.WordTrace tailWord_5583743 prefixEnd_5583743 2867144010178052313533339 := by
  unfold tailWord_5583743
  simp only [CollatzResearch.WordTrace]
  refine ⟨203655838210060213227355883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135770558806706808818237255 203655838210060213227355883)
  ·
    refine ⟨305483757315090319841033825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203655838210060213227355883 305483757315090319841033825)
    ·
      refine ⟨229112817986317739880775369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 305483757315090319841033825 229112817986317739880775369)
      ·
        refine ⟨171834613489738304910581527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 229112817986317739880775369 171834613489738304910581527)
        ·
          refine ⟨257751920234607457365872291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171834613489738304910581527 257751920234607457365872291)
          ·
            refine ⟨386627880351911186048808437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 257751920234607457365872291 386627880351911186048808437)
            ·
              refine ⟨36246363782991673692075791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 386627880351911186048808437 36246363782991673692075791)
              ·
                refine ⟨54369545674487510538113687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36246363782991673692075791 54369545674487510538113687)
                ·
                  refine ⟨81554318511731265807170531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54369545674487510538113687 81554318511731265807170531)
                  ·
                    refine ⟨122331477767596898710755797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 81554318511731265807170531 122331477767596898710755797)
                    ·
                      refine ⟨2867144010178052313533339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 122331477767596898710755797 2867144010178052313533339)
                      ·
                        rfl

theorem cell23_5583743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 7].length) (baseStart_5583743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5583743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5583743 prefixEnd_5583743 := by exact prefixLift 5583743
  have htrace : WordTrace (prefixWord ++ tailWord_5583743) baseStart_5583743 baseEnd_5583743 := by
    simpa [prefixWord, tailWord_5583743, baseEnd_5583743] using wordTrace_append hprefix tailTrace_5583743
  have hstable : (prefixWord ++ tailWord_5583743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5583743).length < 2 ^ (prefixWord ++ tailWord_5583743).sum := by decide
  have hdescent : baseEnd_5583743 < baseStart_5583743 := by decide
  rcases family_descends (prefixWord ++ tailWord_5583743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5583797 : List Nat := [1, 3, 3, 2, 1, 1, 2, 3, 3, 4]
def baseStart_5583797 : Nat := 118140960795 + 5583797 * 2 ^ 59
def prefixEnd_5583797 : Nat := 4983230072969 + 3 ^ 40 * 5583797 * 2
def baseEnd_5583797 : Nat := 955723912711131700752697

theorem tailTrace_5583797 : CollatzResearch.WordTrace tailWord_5583797 prefixEnd_5583797 955723912711131700752697 := by
  unfold tailWord_5583797
  simp only [CollatzResearch.WordTrace]
  refine ⟨203657807751864580449821645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135771871834576386966547763 203657807751864580449821645)
  ·
    refine ⟨76371677906949217668683117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 203657807751864580449821645 76371677906949217668683117)
    ·
      refine ⟨28639379215105956625756169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76371677906949217668683117 28639379215105956625756169)
      ·
        refine ⟨21479534411329467469317127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28639379215105956625756169 21479534411329467469317127)
        ·
          refine ⟨32219301616994201203975691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21479534411329467469317127 32219301616994201203975691)
          ·
            refine ⟨48328952425491301805963537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32219301616994201203975691 48328952425491301805963537)
            ·
              refine ⟨36246714319118476354472653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48328952425491301805963537 36246714319118476354472653)
              ·
                refine ⟨13592517869669428632927245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36246714319118476354472653 13592517869669428632927245)
                ·
                  refine ⟨5097194201126035737347717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13592517869669428632927245 5097194201126035737347717)
                  ·
                    refine ⟨955723912711131700752697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5097194201126035737347717 955723912711131700752697)
                    ·
                      rfl

theorem cell23_5583797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 3, 3, 4].length) (baseStart_5583797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5583797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5583797 prefixEnd_5583797 := by exact prefixLift 5583797
  have htrace : WordTrace (prefixWord ++ tailWord_5583797) baseStart_5583797 baseEnd_5583797 := by
    simpa [prefixWord, tailWord_5583797, baseEnd_5583797] using wordTrace_append hprefix tailTrace_5583797
  have hstable : (prefixWord ++ tailWord_5583797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5583797).length < 2 ^ (prefixWord ++ tailWord_5583797).sum := by decide
  have hdescent : baseEnd_5583797 < baseStart_5583797 := by decide
  rcases family_descends (prefixWord ++ tailWord_5583797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5583798 : List Nat := [5, 1, 4, 1, 1, 1, 1, 1, 2, 3, 3]
def baseStart_5583798 : Nat := 118140960795 + 5583798 * 2 ^ 59
def prefixEnd_5583798 : Nat := 4983230072969 + 3 ^ 40 * 5583798 * 2
def baseEnd_5583798 : Nat := 2867172251614049598345587

theorem tailTrace_5583798 : CollatzResearch.WordTrace tailWord_5583798 prefixEnd_5583798 2867172251614049598345587 := by
  unfold tailWord_5583798
  simp only [CollatzResearch.WordTrace]
  refine ⟨12728615264053809851288003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 135771896149907305080405365 12728615264053809851288003)
  ·
    refine ⟨19092922896080714776932005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12728615264053809851288003 19092922896080714776932005)
    ·
      refine ⟨3579923043015134020674751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19092922896080714776932005 3579923043015134020674751)
      ·
        refine ⟨5369884564522701031012127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3579923043015134020674751 5369884564522701031012127)
        ·
          refine ⟨8054826846784051546518191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5369884564522701031012127 8054826846784051546518191)
          ·
            refine ⟨12082240270176077319777287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8054826846784051546518191 12082240270176077319777287)
            ·
              refine ⟨18123360405264115979665931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12082240270176077319777287 18123360405264115979665931)
              ·
                refine ⟨27185040607896173969498897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18123360405264115979665931 27185040607896173969498897)
                ·
                  refine ⟨20388780455922130477124173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27185040607896173969498897 20388780455922130477124173)
                  ·
                    refine ⟨7645792670970798928921565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20388780455922130477124173 7645792670970798928921565)
                    ·
                      refine ⟨2867172251614049598345587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7645792670970798928921565 2867172251614049598345587)
                      ·
                        rfl

theorem cell23_5583798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_5583798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5583798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5583798 prefixEnd_5583798 := by exact prefixLift 5583798
  have htrace : WordTrace (prefixWord ++ tailWord_5583798) baseStart_5583798 baseEnd_5583798 := by
    simpa [prefixWord, tailWord_5583798, baseEnd_5583798] using wordTrace_append hprefix tailTrace_5583798
  have hstable : (prefixWord ++ tailWord_5583798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5583798).length < 2 ^ (prefixWord ++ tailWord_5583798).sum := by decide
  have hdescent : baseEnd_5583798 < baseStart_5583798 := by decide
  rcases family_descends (prefixWord ++ tailWord_5583798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5583803 : List Nat := [1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 9]
def baseStart_5583803 : Nat := 118140960795 + 5583803 * 2 ^ 59
def prefixEnd_5583803 : Nat := 4983230072969 + 3 ^ 40 * 5583803 * 2
def baseEnd_5583803 : Nat := 2867174819017322078783063

theorem tailTrace_5583803 : CollatzResearch.WordTrace tailWord_5583803 prefixEnd_5583803 2867174819017322078783063 := by
  unfold tailWord_5583803
  simp only [CollatzResearch.WordTrace]
  refine ⟨203658026589842843474540063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135772017726561895649693375 203658026589842843474540063)
  ·
    refine ⟨305487039884764265211810095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203658026589842843474540063 305487039884764265211810095)
    ·
      refine ⟨458230559827146397817715143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305487039884764265211810095 458230559827146397817715143)
      ·
        refine ⟨687345839740719596726572715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 458230559827146397817715143 687345839740719596726572715)
        ·
          refine ⟨1031018759611079395089859073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 687345839740719596726572715 1031018759611079395089859073)
          ·
            refine ⟨773264069708309546317394305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1031018759611079395089859073 773264069708309546317394305)
            ·
              refine ⟨579948052281232159738045729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 773264069708309546317394305 579948052281232159738045729)
              ·
                refine ⟨434961039210924119803534297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 579948052281232159738045729 434961039210924119803534297)
                ·
                  refine ⟨326220779408193089852650723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 434961039210924119803534297 326220779408193089852650723)
                  ·
                    refine ⟨489331169112289634778976085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 326220779408193089852650723 489331169112289634778976085)
                    ·
                      refine ⟨2867174819017322078783063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 489331169112289634778976085 2867174819017322078783063)
                      ·
                        rfl

theorem cell23_5583803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 9].length) (baseStart_5583803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5583803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5583803 prefixEnd_5583803 := by exact prefixLift 5583803
  have htrace : WordTrace (prefixWord ++ tailWord_5583803) baseStart_5583803 baseEnd_5583803 := by
    simpa [prefixWord, tailWord_5583803, baseEnd_5583803] using wordTrace_append hprefix tailTrace_5583803
  have hstable : (prefixWord ++ tailWord_5583803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5583803).length < 2 ^ (prefixWord ++ tailWord_5583803).sum := by decide
  have hdescent : baseEnd_5583803 < baseStart_5583803 := by decide
  rcases family_descends (prefixWord ++ tailWord_5583803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5583877 : List Nat := [1, 3, 1, 1, 2, 3, 1, 1, 2, 6, 2]
def baseStart_5583877 : Nat := 118140960795 + 5583877 * 2 ^ 59
def prefixEnd_5583877 : Nat := 4983230072969 + 3 ^ 40 * 5583877 * 2
def baseEnd_5583877 : Nat := 2867212816585754789257723

theorem tailTrace_5583877 : CollatzResearch.WordTrace tailWord_5583877 prefixEnd_5583877 2867212816585754789257723 := by
  unfold tailWord_5583877
  simp only [CollatzResearch.WordTrace]
  refine ⟨203660725591574754112733885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135773817061049836075155923 203660725591574754112733885)
  ·
    refine ⟨76372772096840532792275207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 203660725591574754112733885 76372772096840532792275207)
    ·
      refine ⟨114559158145260799188412811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76372772096840532792275207 114559158145260799188412811)
      ·
        refine ⟨171838737217891198782619217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114559158145260799188412811 171838737217891198782619217)
        ·
          refine ⟨128879052913418399086964413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171838737217891198782619217 128879052913418399086964413)
          ·
            refine ⟨48329644842531899657611655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 128879052913418399086964413 48329644842531899657611655)
            ·
              refine ⟨72494467263797849486417483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48329644842531899657611655 72494467263797849486417483)
              ·
                refine ⟨108741700895696774229626225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72494467263797849486417483 108741700895696774229626225)
                ·
                  refine ⟨81556275671772580672219669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 108741700895696774229626225 81556275671772580672219669)
                  ·
                    refine ⟨3822950422114339719010297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 81556275671772580672219669 3822950422114339719010297)
                    ·
                      refine ⟨2867212816585754789257723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3822950422114339719010297 2867212816585754789257723)
                      ·
                        rfl

theorem cell23_5583877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 2, 6, 2].length) (baseStart_5583877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5583877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5583877 prefixEnd_5583877 := by exact prefixLift 5583877
  have htrace : WordTrace (prefixWord ++ tailWord_5583877) baseStart_5583877 baseEnd_5583877 := by
    simpa [prefixWord, tailWord_5583877, baseEnd_5583877] using wordTrace_append hprefix tailTrace_5583877
  have hstable : (prefixWord ++ tailWord_5583877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5583877).length < 2 ^ (prefixWord ++ tailWord_5583877).sum := by decide
  have hdescent : baseEnd_5583877 < baseStart_5583877 := by decide
  rcases family_descends (prefixWord ++ tailWord_5583877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5583920 : List Nat := [2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 6]
def baseStart_5583920 : Nat := 118140960795 + 5583920 * 2 ^ 59
def prefixEnd_5583920 : Nat := 4983230072969 + 3 ^ 40 * 5583920 * 2
def baseEnd_5583920 : Nat := 2867234896253898121020025

theorem tailTrace_5583920 : CollatzResearch.WordTrace tailWord_5583920 prefixEnd_5583920 2867234896253898121020025 := by
  unfold tailWord_5583920
  simp only [CollatzResearch.WordTrace]
  refine ⟨101831146965209486228274607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135774862620279314971032809 101831146965209486228274607)
  ·
    refine ⟨152746720447814229342411911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101831146965209486228274607 152746720447814229342411911)
    ·
      refine ⟨229120080671721344013617867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152746720447814229342411911 229120080671721344013617867)
      ·
        refine ⟨343680121007582016020426801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229120080671721344013617867 343680121007582016020426801)
        ·
          refine ⟨257760090755686512015320101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 343680121007582016020426801 257760090755686512015320101)
          ·
            refine ⟨48330017016691221002872519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 257760090755686512015320101 48330017016691221002872519)
            ·
              refine ⟨72495025525036831504308779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48330017016691221002872519 72495025525036831504308779)
              ·
                refine ⟨108742538287555247256463169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72495025525036831504308779 108742538287555247256463169)
                ·
                  refine ⟨81556903715666435442347377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 108742538287555247256463169 81556903715666435442347377)
                  ·
                    refine ⟨61167677786749826581760533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 81556903715666435442347377 61167677786749826581760533)
                    ·
                      refine ⟨2867234896253898121020025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61167677786749826581760533 2867234896253898121020025)
                      ·
                        rfl

theorem cell23_5583920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 6].length) (baseStart_5583920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5583920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5583920 prefixEnd_5583920 := by exact prefixLift 5583920
  have htrace : WordTrace (prefixWord ++ tailWord_5583920) baseStart_5583920 baseEnd_5583920 := by
    simpa [prefixWord, tailWord_5583920, baseEnd_5583920] using wordTrace_append hprefix tailTrace_5583920
  have hstable : (prefixWord ++ tailWord_5583920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5583920).length < 2 ^ (prefixWord ++ tailWord_5583920).sum := by decide
  have hdescent : baseEnd_5583920 < baseStart_5583920 := by decide
  rcases family_descends (prefixWord ++ tailWord_5583920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5583924 : List Nat := [2, 5, 1, 2, 1, 1, 2, 1, 1, 1, 6]
def baseStart_5583924 : Nat := 118140960795 + 5583924 * 2 ^ 59
def prefixEnd_5583924 : Nat := 4983230072969 + 3 ^ 40 * 5583924 * 2
def baseEnd_5583924 : Nat := 2867236950176516105370007

theorem tailTrace_5583924 : CollatzResearch.WordTrace tailWord_5583924 prefixEnd_5583924 2867236950176516105370007 := by
  unfold tailWord_5583924
  simp only [CollatzResearch.WordTrace]
  refine ⟨101831219911202240569847413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135774959881602987426463217 101831219911202240569847413)
  ·
    refine ⟨9546676866675210053423195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 101831219911202240569847413 9546676866675210053423195)
    ·
      refine ⟨14320015300012815080134793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9546676866675210053423195 14320015300012815080134793)
      ·
        refine ⟨10740011475009611310101095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14320015300012815080134793 10740011475009611310101095)
        ·
          refine ⟨16110017212514416965151643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10740011475009611310101095 16110017212514416965151643)
          ·
            refine ⟨24165025818771625447727465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16110017212514416965151643 24165025818771625447727465)
            ·
              refine ⟨18123769364078719085795599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24165025818771625447727465 18123769364078719085795599)
              ·
                refine ⟨27185654046118078628693399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18123769364078719085795599 27185654046118078628693399)
                ·
                  refine ⟨40778481069177117943040099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27185654046118078628693399 40778481069177117943040099)
                  ·
                    refine ⟨61167721603765676914560149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40778481069177117943040099 61167721603765676914560149)
                    ·
                      refine ⟨2867236950176516105370007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61167721603765676914560149 2867236950176516105370007)
                      ·
                        rfl

theorem cell23_5583924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_5583924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5583924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5583924 prefixEnd_5583924 := by exact prefixLift 5583924
  have htrace : WordTrace (prefixWord ++ tailWord_5583924) baseStart_5583924 baseEnd_5583924 := by
    simpa [prefixWord, tailWord_5583924, baseEnd_5583924] using wordTrace_append hprefix tailTrace_5583924
  have hstable : (prefixWord ++ tailWord_5583924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5583924).length < 2 ^ (prefixWord ++ tailWord_5583924).sum := by decide
  have hdescent : baseEnd_5583924 < baseStart_5583924 := by decide
  rcases family_descends (prefixWord ++ tailWord_5583924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5583927 : List Nat := [1, 1, 3, 1, 2, 2, 1, 5, 1, 3, 3]
def baseStart_5583927 : Nat := 118140960795 + 5583927 * 2 ^ 59
def prefixEnd_5583927 : Nat := 4983230072969 + 3 ^ 40 * 5583927 * 2
def baseEnd_5583927 : Nat := 2867238490618479593632493

theorem tailTrace_5583927 : CollatzResearch.WordTrace tailWord_5583927 prefixEnd_5583927 2867238490618479593632493 := by
  unfold tailWord_5583927
  simp only [CollatzResearch.WordTrace]
  refine ⟨203662549241393612652054035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135775032827595741768036023 203662549241393612652054035)
  ·
    refine ⟨305493823862090418978081053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203662549241393612652054035 305493823862090418978081053)
    ·
      refine ⟨114560183948283907116780395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 305493823862090418978081053 114560183948283907116780395)
      ·
        refine ⟨171840275922425860675170593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114560183948283907116780395 171840275922425860675170593)
        ·
          refine ⟨128880206941819395506377945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171840275922425860675170593 128880206941819395506377945)
          ·
            refine ⟨96660155206364546629783459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128880206941819395506377945 96660155206364546629783459)
            ·
              refine ⟨144990232809546819944675189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96660155206364546629783459 144990232809546819944675189)
              ·
                refine ⟨13592834325895014369813299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 144990232809546819944675189 13592834325895014369813299)
                ·
                  refine ⟨20389251488842521554719949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13592834325895014369813299 20389251488842521554719949)
                  ·
                    refine ⟨7645969308315945583019981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20389251488842521554719949 7645969308315945583019981)
                    ·
                      refine ⟨2867238490618479593632493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7645969308315945583019981 2867238490618479593632493)
                      ·
                        rfl

theorem cell23_5583927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 5, 1, 3, 3].length) (baseStart_5583927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5583927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5583927 prefixEnd_5583927 := by exact prefixLift 5583927
  have htrace : WordTrace (prefixWord ++ tailWord_5583927) baseStart_5583927 baseEnd_5583927 := by
    simpa [prefixWord, tailWord_5583927, baseEnd_5583927] using wordTrace_append hprefix tailTrace_5583927
  have hstable : (prefixWord ++ tailWord_5583927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5583927).length < 2 ^ (prefixWord ++ tailWord_5583927).sum := by decide
  have hdescent : baseEnd_5583927 < baseStart_5583927 := by decide
  rcases family_descends (prefixWord ++ tailWord_5583927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5583977 : List Nat := [1, 2, 1, 1, 1, 7, 1, 1, 2, 6]
def baseStart_5583977 : Nat := 118140960795 + 5583977 * 2 ^ 59
def prefixEnd_5583977 : Nat := 4983230072969 + 3 ^ 40 * 5583977 * 2
def baseEnd_5583977 : Nat := 955754721550401466002421

theorem tailTrace_5583977 : CollatzResearch.WordTrace tailWord_5583977 prefixEnd_5583977 955754721550401466002421 := by
  unfold tailWord_5583977
  simp only [CollatzResearch.WordTrace]
  refine ⟨203664372891212471191374185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135776248594141647460916123 203664372891212471191374185)
  ·
    refine ⟨152748279668409353393530639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203664372891212471191374185 152748279668409353393530639)
    ·
      refine ⟨229122419502614030090295959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152748279668409353393530639 229122419502614030090295959)
      ·
        refine ⟨343683629253921045135443939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229122419502614030090295959 343683629253921045135443939)
        ·
          refine ⟨515525443880881567703165909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 343683629253921045135443939 515525443880881567703165909)
          ·
            refine ⟨12082627590958161743042951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 515525443880881567703165909 12082627590958161743042951)
            ·
              refine ⟨18123941386437242614564427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12082627590958161743042951 18123941386437242614564427)
              ·
                refine ⟨27185912079655863921846641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18123941386437242614564427 27185912079655863921846641)
                ·
                  refine ⟨20389434059741897941384981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27185912079655863921846641 20389434059741897941384981)
                  ·
                    refine ⟨955754721550401466002421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20389434059741897941384981 955754721550401466002421)
                    ·
                      rfl

theorem cell23_5583977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 1, 2, 6].length) (baseStart_5583977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5583977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5583977 prefixEnd_5583977 := by exact prefixLift 5583977
  have htrace : WordTrace (prefixWord ++ tailWord_5583977) baseStart_5583977 baseEnd_5583977 := by
    simpa [prefixWord, tailWord_5583977, baseEnd_5583977] using wordTrace_append hprefix tailTrace_5583977
  have hstable : (prefixWord ++ tailWord_5583977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5583977).length < 2 ^ (prefixWord ++ tailWord_5583977).sum := by decide
  have hdescent : baseEnd_5583977 < baseStart_5583977 := by decide
  rcases family_descends (prefixWord ++ tailWord_5583977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5583997 : List Nat := [1, 4, 1, 1, 3, 1, 1, 2, 1, 4, 4]
def baseStart_5583997 : Nat := 118140960795 + 5583997 * 2 ^ 59
def prefixEnd_5583997 : Nat := 4983230072969 + 3 ^ 40 * 5583997 * 2
def baseEnd_5583997 : Nat := 2867274434264294319757171

theorem tailTrace_5583997 : CollatzResearch.WordTrace tailWord_5583997 prefixEnd_5583997 2867274434264294319757171 := by
  unfold tailWord_5583997
  simp only [CollatzResearch.WordTrace]
  refine ⟨203665102351140014607102245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135776734900760009738068163 203665102351140014607102245)
  ·
    refine ⟨38187206690838752738831671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 203665102351140014607102245 38187206690838752738831671)
    ·
      refine ⟨57280810036258129108247507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38187206690838752738831671 57280810036258129108247507)
      ·
        refine ⟨85921215054387193662371261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57280810036258129108247507 85921215054387193662371261)
        ·
          refine ⟨32220455645395197623389223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85921215054387193662371261 32220455645395197623389223)
          ·
            refine ⟨48330683468092796435083835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32220455645395197623389223 48330683468092796435083835)
            ·
              refine ⟨72496025202139194652625753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48330683468092796435083835 72496025202139194652625753)
              ·
                refine ⟨54372018901604395989469315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72496025202139194652625753 54372018901604395989469315)
                ·
                  refine ⟨81558028352406593984203973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54372018901604395989469315 81558028352406593984203973)
                  ·
                    refine ⟨15292130316076236372038245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 81558028352406593984203973 15292130316076236372038245)
                    ·
                      refine ⟨2867274434264294319757171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15292130316076236372038245 2867274434264294319757171)
                      ·
                        rfl

theorem cell23_5583997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 2, 1, 4, 4].length) (baseStart_5583997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5583997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5583997 prefixEnd_5583997 := by exact prefixLift 5583997
  have htrace : WordTrace (prefixWord ++ tailWord_5583997) baseStart_5583997 baseEnd_5583997 := by
    simpa [prefixWord, tailWord_5583997, baseEnd_5583997] using wordTrace_append hprefix tailTrace_5583997
  have hstable : (prefixWord ++ tailWord_5583997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5583997).length < 2 ^ (prefixWord ++ tailWord_5583997).sum := by decide
  have hdescent : baseEnd_5583997 < baseStart_5583997 := by decide
  rcases family_descends (prefixWord ++ tailWord_5583997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5584001 : List Nat := [1, 2, 4, 2, 2, 1, 2, 2, 1, 4, 2]
def baseStart_5584001 : Nat := 118140960795 + 5584001 * 2 ^ 59
def prefixEnd_5584001 : Nat := 4983230072969 + 3 ^ 40 * 5584001 * 2
def baseEnd_5584001 : Nat := 2867276488186912304107153

theorem tailTrace_5584001 : CollatzResearch.WordTrace tailWord_5584001 prefixEnd_5584001 2867276488186912304107153 := by
  unfold tailWord_5584001
  simp only [CollatzResearch.WordTrace]
  refine ⟨203665248243125523290247857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135776832162083682193498571 203665248243125523290247857)
  ·
    refine ⟨152748936182344142467685893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203665248243125523290247857 152748936182344142467685893)
    ·
      refine ⟨28640425534189526712691105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 152748936182344142467685893 28640425534189526712691105)
      ·
        refine ⟨21480319150642145034518329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28640425534189526712691105 21480319150642145034518329)
        ·
          refine ⟨16110239362981608775888747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21480319150642145034518329 16110239362981608775888747)
          ·
            refine ⟨24165359044472413163833121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16110239362981608775888747 24165359044472413163833121)
            ·
              refine ⟨18124019283354309872874841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24165359044472413163833121 18124019283354309872874841)
              ·
                refine ⟨13593014462515732404656131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18124019283354309872874841 13593014462515732404656131)
                ·
                  refine ⟨20389521693773598606984197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13593014462515732404656131 20389521693773598606984197)
                  ·
                    refine ⟨3823035317582549738809537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20389521693773598606984197 3823035317582549738809537)
                    ·
                      refine ⟨2867276488186912304107153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3823035317582549738809537 2867276488186912304107153)
                      ·
                        rfl

theorem cell23_5584001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 2, 1, 4, 2].length) (baseStart_5584001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5584001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5584001 prefixEnd_5584001 := by exact prefixLift 5584001
  have htrace : WordTrace (prefixWord ++ tailWord_5584001) baseStart_5584001 baseEnd_5584001 := by
    simpa [prefixWord, tailWord_5584001, baseEnd_5584001] using wordTrace_append hprefix tailTrace_5584001
  have hstable : (prefixWord ++ tailWord_5584001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5584001).length < 2 ^ (prefixWord ++ tailWord_5584001).sum := by decide
  have hdescent : baseEnd_5584001 < baseStart_5584001 := by decide
  rcases family_descends (prefixWord ++ tailWord_5584001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5584005 : List Nat := [1, 3, 1, 1, 6, 2, 2, 1, 1, 3, 2]
def baseStart_5584005 : Nat := 118140960795 + 5584005 * 2 ^ 59
def prefixEnd_5584005 : Nat := 4983230072969 + 3 ^ 40 * 5584005 * 2
def baseEnd_5584005 : Nat := 2867278542109530288457135

theorem tailTrace_5584005 : CollatzResearch.WordTrace tailWord_5584005 prefixEnd_5584005 2867278542109530288457135 := by
  unfold tailWord_5584005
  simp only [CollatzResearch.WordTrace]
  refine ⟨203665394135111031973393469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135776929423407354648928979 203665394135111031973393469)
  ·
    refine ⟨76374522800666636990022551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 203665394135111031973393469 76374522800666636990022551)
    ·
      refine ⟨114561784200999955485033827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76374522800666636990022551 114561784200999955485033827)
      ·
        refine ⟨171842676301499933227550741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114561784200999955485033827 171842676301499933227550741)
        ·
          refine ⟨8055125451632809370041441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 171842676301499933227550741 8055125451632809370041441)
          ·
            refine ⟨6041344088724607027531081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8055125451632809370041441 6041344088724607027531081)
            ·
              refine ⟨4531008066543455270648311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6041344088724607027531081 4531008066543455270648311)
              ·
                refine ⟨6796512099815182905972467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4531008066543455270648311 6796512099815182905972467)
                ·
                  refine ⟨10194768149722774358958701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6796512099815182905972467 10194768149722774358958701)
                  ·
                    refine ⟨3823038056146040384609513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10194768149722774358958701 3823038056146040384609513)
                    ·
                      refine ⟨2867278542109530288457135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3823038056146040384609513 2867278542109530288457135)
                      ·
                        rfl

theorem cell23_5584005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 2, 1, 1, 3, 2].length) (baseStart_5584005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5584005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5584005 prefixEnd_5584005 := by exact prefixLift 5584005
  have htrace : WordTrace (prefixWord ++ tailWord_5584005) baseStart_5584005 baseEnd_5584005 := by
    simpa [prefixWord, tailWord_5584005, baseEnd_5584005] using wordTrace_append hprefix tailTrace_5584005
  have hstable : (prefixWord ++ tailWord_5584005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5584005).length < 2 ^ (prefixWord ++ tailWord_5584005).sum := by decide
  have hdescent : baseEnd_5584005 < baseStart_5584005 := by decide
  rcases family_descends (prefixWord ++ tailWord_5584005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5584014 : List Nat := [4, 1, 1, 3, 2, 1, 1, 2, 2, 2, 4]
def baseStart_5584014 : Nat := 118140960795 + 5584014 * 2 ^ 59
def prefixEnd_5584014 : Nat := 4983230072969 + 3 ^ 40 * 5584014 * 2
def baseEnd_5584014 : Nat := 2867283163435420753244593

theorem tailTrace_5584014 : CollatzResearch.WordTrace tailWord_5584014 prefixEnd_5584014 2867283163435420753244593 := by
  unfold tailWord_5584014
  simp only [CollatzResearch.WordTrace]
  refine ⟨25458215299009803313808887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135777148261385617673647397 25458215299009803313808887)
  ·
    refine ⟨38187322948514704970713331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25458215299009803313808887 38187322948514704970713331)
    ·
      refine ⟨57280984422772057456069997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38187322948514704970713331 57280984422772057456069997)
      ·
        refine ⟨21480369158539521546026249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57280984422772057456069997 21480369158539521546026249)
        ·
          refine ⟨16110276868904641159519687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21480369158539521546026249 16110276868904641159519687)
          ·
            refine ⟨24165415303356961739279531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16110276868904641159519687 24165415303356961739279531)
            ·
              refine ⟨36248122955035442608919297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24165415303356961739279531 36248122955035442608919297)
              ·
                refine ⟨27186092216276581956689473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36248122955035442608919297 27186092216276581956689473)
                ·
                  refine ⟨20389569162207436467517105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27186092216276581956689473 20389569162207436467517105)
                  ·
                    refine ⟨15292176871655577350637829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20389569162207436467517105 15292176871655577350637829)
                    ·
                      refine ⟨2867283163435420753244593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15292176871655577350637829 2867283163435420753244593)
                      ·
                        rfl

theorem cell23_5584014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_5584014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5584014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5584014 prefixEnd_5584014 := by exact prefixLift 5584014
  have htrace : WordTrace (prefixWord ++ tailWord_5584014) baseStart_5584014 baseEnd_5584014 := by
    simpa [prefixWord, tailWord_5584014, baseEnd_5584014] using wordTrace_append hprefix tailTrace_5584014
  have hstable : (prefixWord ++ tailWord_5584014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5584014).length < 2 ^ (prefixWord ++ tailWord_5584014).sum := by decide
  have hdescent : baseEnd_5584014 < baseStart_5584014 := by decide
  rcases family_descends (prefixWord ++ tailWord_5584014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5584018 : List Nat := [3, 2, 3, 1, 1, 3, 1, 1, 4, 2, 2]
def baseStart_5584018 : Nat := 118140960795 + 5584018 * 2 ^ 59
def prefixEnd_5584018 : Nat := 4983230072969 + 3 ^ 40 * 5584018 * 2
def baseEnd_5584018 : Nat := 2867285217358038737594575

theorem tailTrace_5584018 : CollatzResearch.WordTrace tailWord_5584018 prefixEnd_5584018 2867285217358038737594575 := by
  unfold tailWord_5584018
  simp only [CollatzResearch.WordTrace]
  refine ⟨50916467071015983798404177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135777245522709290129077805 50916467071015983798404177)
  ·
    refine ⟨38187350303261987848803133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50916467071015983798404177 38187350303261987848803133)
    ·
      refine ⟨14320256363723245443301175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38187350303261987848803133 14320256363723245443301175)
      ·
        refine ⟨21480384545584868164951763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14320256363723245443301175 21480384545584868164951763)
        ·
          refine ⟨32220576818377302247427645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21480384545584868164951763 32220576818377302247427645)
          ·
            refine ⟨12082716306891488342785367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32220576818377302247427645 12082716306891488342785367)
            ·
              refine ⟨18124074460337232514178051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12082716306891488342785367 18124074460337232514178051)
              ·
                refine ⟨27186111690505848771267077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18124074460337232514178051 27186111690505848771267077)
                ·
                  refine ⟨5097395941969846644612577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27186111690505848771267077 5097395941969846644612577)
                  ·
                    refine ⟨3823046956477384983459433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5097395941969846644612577 3823046956477384983459433)
                    ·
                      refine ⟨2867285217358038737594575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3823046956477384983459433 2867285217358038737594575)
                      ·
                        rfl

theorem cell23_5584018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 1, 4, 2, 2].length) (baseStart_5584018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5584018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5584018 prefixEnd_5584018 := by exact prefixLift 5584018
  have htrace : WordTrace (prefixWord ++ tailWord_5584018) baseStart_5584018 baseEnd_5584018 := by
    simpa [prefixWord, tailWord_5584018, baseEnd_5584018] using wordTrace_append hprefix tailTrace_5584018
  have hstable : (prefixWord ++ tailWord_5584018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5584018).length < 2 ^ (prefixWord ++ tailWord_5584018).sum := by decide
  have hdescent : baseEnd_5584018 < baseStart_5584018 := by decide
  rcases family_descends (prefixWord ++ tailWord_5584018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5584024 : List Nat := [2, 1, 2, 4, 2, 2, 2, 1, 7]
def baseStart_5584024 : Nat := 118140960795 + 5584024 * 2 ^ 59
def prefixEnd_5584024 : Nat := 4983230072969 + 3 ^ 40 * 5584024 * 2
def baseEnd_5584024 : Nat := 318587588693551746013283

theorem tailTrace_5584024 : CollatzResearch.WordTrace tailWord_5584024 prefixEnd_5584024 318587588693551746013283 := by
  unfold tailWord_5584024
  simp only [CollatzResearch.WordTrace]
  refine ⟨101833043561021099109167563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135777391414694798812223417 101833043561021099109167563)
  ·
    refine ⟨152749565341531648663751345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101833043561021099109167563 152749565341531648663751345)
    ·
      refine ⟨114562174006148736497813509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152749565341531648663751345 114562174006148736497813509)
      ·
        refine ⟨21480407626152888093340033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 114562174006148736497813509 21480407626152888093340033)
        ·
          refine ⟨16110305719614666070005025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21480407626152888093340033 16110305719614666070005025)
          ·
            refine ⟨12082729289710999552503769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16110305719614666070005025 12082729289710999552503769)
            ·
              refine ⟨9062046967283249664377827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12082729289710999552503769 9062046967283249664377827)
              ·
                refine ⟨13593070450924874496566741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9062046967283249664377827 13593070450924874496566741)
                ·
                  refine ⟨318587588693551746013283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13593070450924874496566741 318587588693551746013283)
                  ·
                    rfl

theorem cell23_5584024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 1, 7].length) (baseStart_5584024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5584024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5584024 prefixEnd_5584024 := by exact prefixLift 5584024
  have htrace : WordTrace (prefixWord ++ tailWord_5584024) baseStart_5584024 baseEnd_5584024 := by
    simpa [prefixWord, tailWord_5584024, baseEnd_5584024] using wordTrace_append hprefix tailTrace_5584024
  have hstable : (prefixWord ++ tailWord_5584024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5584024).length < 2 ^ (prefixWord ++ tailWord_5584024).sum := by decide
  have hdescent : baseEnd_5584024 < baseStart_5584024 := by decide
  rcases family_descends (prefixWord ++ tailWord_5584024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5584037 : List Nat := [1, 3, 1, 2, 1, 4, 1, 2, 1, 7]
def baseStart_5584037 : Nat := 118140960795 + 5584037 * 2 ^ 59
def prefixEnd_5584037 : Nat := 4983230072969 + 3 ^ 40 * 5584037 * 2
def baseEnd_5584037 : Nat := 955764991163491387752329

theorem tailTrace_5584037 : CollatzResearch.WordTrace tailWord_5584037 prefixEnd_5584037 955764991163491387752329 := by
  unfold tailWord_5584037
  simp only [CollatzResearch.WordTrace]
  refine ⟨203666561270995101438558365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135777707513996734292372243 203666561270995101438558365)
  ·
    refine ⟨76374960476623163039459387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 203666561270995101438558365 76374960476623163039459387)
    ·
      refine ⟨114562440714934744559189081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76374960476623163039459387 114562440714934744559189081)
      ·
        refine ⟨85921830536201058419391811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114562440714934744559189081 85921830536201058419391811)
        ·
          refine ⟨128882745804301587629087717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85921830536201058419391811 128882745804301587629087717)
          ·
            refine ⟨24165514838306547680453947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 128882745804301587629087717 24165514838306547680453947)
            ·
              refine ⟨36248272257459821520680921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24165514838306547680453947 36248272257459821520680921)
              ·
                refine ⟨27186204193094866140510691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36248272257459821520680921 27186204193094866140510691)
                ·
                  refine ⟨40779306289642299210766037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27186204193094866140510691 40779306289642299210766037)
                  ·
                    refine ⟨955764991163491387752329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40779306289642299210766037 955764991163491387752329)
                    ·
                      rfl

theorem cell23_5584037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 2, 1, 7].length) (baseStart_5584037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5584037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5584037 prefixEnd_5584037 := by exact prefixLift 5584037
  have htrace : WordTrace (prefixWord ++ tailWord_5584037) baseStart_5584037 baseEnd_5584037 := by
    simpa [prefixWord, tailWord_5584037, baseEnd_5584037] using wordTrace_append hprefix tailTrace_5584037
  have hstable : (prefixWord ++ tailWord_5584037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5584037).length < 2 ^ (prefixWord ++ tailWord_5584037).sum := by decide
  have hdescent : baseEnd_5584037 < baseStart_5584037 := by decide
  rcases family_descends (prefixWord ++ tailWord_5584037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5584074 : List Nat := [3, 1, 2, 1, 3, 2, 1, 1, 4, 1, 4]
def baseStart_5584074 : Nat := 118140960795 + 5584074 * 2 ^ 59
def prefixEnd_5584074 : Nat := 4983230072969 + 3 ^ 40 * 5584074 * 2
def baseEnd_5584074 : Nat := 2867313972274690518494317

theorem tailTrace_5584074 : CollatzResearch.WordTrace tailWord_5584074 prefixEnd_5584074 2867313972274690518494317 := by
  unfold tailWord_5584074
  simp only [CollatzResearch.WordTrace]
  refine ⟨50916977692965264189413819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135778607181240704505103517 50916977692965264189413819)
  ·
    refine ⟨76375466539447896284120729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50916977692965264189413819 76375466539447896284120729)
    ·
      refine ⟨57281599904585922213090547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76375466539447896284120729 57281599904585922213090547)
      ·
        refine ⟨85922399856878883319635821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57281599904585922213090547 85922399856878883319635821)
        ·
          refine ⟨32220899946329581244863433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85922399856878883319635821 32220899946329581244863433)
          ·
            refine ⟨24165674959747185933647575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32220899946329581244863433 24165674959747185933647575)
            ·
              refine ⟨36248512439620778900471363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24165674959747185933647575 36248512439620778900471363)
              ·
                refine ⟨54372768659431168350707045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36248512439620778900471363 54372768659431168350707045)
                ·
                  refine ⟨10194894123643344065757571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54372768659431168350707045 10194894123643344065757571)
                  ·
                    refine ⟨15292341185465016098636357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10194894123643344065757571 15292341185465016098636357)
                    ·
                      refine ⟨2867313972274690518494317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15292341185465016098636357 2867313972274690518494317)
                      ·
                        rfl

theorem cell23_5584074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 1, 4, 1, 4].length) (baseStart_5584074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5584074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5584074 prefixEnd_5584074 := by exact prefixLift 5584074
  have htrace : WordTrace (prefixWord ++ tailWord_5584074) baseStart_5584074 baseEnd_5584074 := by
    simpa [prefixWord, tailWord_5584074, baseEnd_5584074] using wordTrace_append hprefix tailTrace_5584074
  have hstable : (prefixWord ++ tailWord_5584074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5584074).length < 2 ^ (prefixWord ++ tailWord_5584074).sum := by decide
  have hdescent : baseEnd_5584074 < baseStart_5584074 := by decide
  rcases family_descends (prefixWord ++ tailWord_5584074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5584086 : List Nat := [5, 2, 1, 2, 3, 1, 2, 1, 2, 2, 2]
def baseStart_5584086 : Nat := 118140960795 + 5584086 * 2 ^ 59
def prefixEnd_5584086 : Nat := 4983230072969 + 3 ^ 40 * 5584086 * 2
def baseEnd_5584086 : Nat := 2867320134042544471544263

theorem tailTrace_5584086 : CollatzResearch.WordTrace tailWord_5584086 prefixEnd_5584086 2867320134042544471544263 := by
  unfold tailWord_5584086
  simp only [CollatzResearch.WordTrace]
  refine ⟨12729271777988598925443257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 135778898965211721871394741 12729271777988598925443257)
  ·
    refine ⟨9546953833491449194082443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12729271777988598925443257 9546953833491449194082443)
    ·
      refine ⟨14320430750237173791123665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9546953833491449194082443 14320430750237173791123665)
      ·
        refine ⟨10740323062677880343342749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14320430750237173791123665 10740323062677880343342749)
        ·
          refine ⟨4027621148504205128753531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10740323062677880343342749 4027621148504205128753531)
          ·
            refine ⟨6041431722756307693130297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4027621148504205128753531 6041431722756307693130297)
            ·
              refine ⟨4531073792067230769847723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6041431722756307693130297 4531073792067230769847723)
              ·
                refine ⟨6796610688100846154771585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4531073792067230769847723 6796610688100846154771585)
                ·
                  refine ⟨5097458016075634616078689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6796610688100846154771585 5097458016075634616078689)
                  ·
                    refine ⟨3823093512056725962059017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5097458016075634616078689 3823093512056725962059017)
                    ·
                      refine ⟨2867320134042544471544263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3823093512056725962059017 2867320134042544471544263)
                      ·
                        rfl

theorem cell23_5584086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 2, 1, 2, 2, 2].length) (baseStart_5584086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5584086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5584086 prefixEnd_5584086 := by exact prefixLift 5584086
  have htrace : WordTrace (prefixWord ++ tailWord_5584086) baseStart_5584086 baseEnd_5584086 := by
    simpa [prefixWord, tailWord_5584086, baseEnd_5584086] using wordTrace_append hprefix tailTrace_5584086
  have hstable : (prefixWord ++ tailWord_5584086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5584086).length < 2 ^ (prefixWord ++ tailWord_5584086).sum := by decide
  have hdescent : baseEnd_5584086 < baseStart_5584086 := by decide
  rcases family_descends (prefixWord ++ tailWord_5584086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5584087 : List Nat := [1, 1, 3, 2, 1, 2, 2, 2, 2, 1, 6]
def baseStart_5584087 : Nat := 118140960795 + 5584087 * 2 ^ 59
def prefixEnd_5584087 : Nat := 4983230072969 + 3 ^ 40 * 5584087 * 2
def baseEnd_5584087 : Nat := 2867320647523198967631757

theorem tailTrace_5584087 : CollatzResearch.WordTrace tailWord_5584087 prefixEnd_5584087 2867320647523198967631757 := by
  unfold tailWord_5584087
  simp only [CollatzResearch.WordTrace]
  refine ⟨203668384920813959977878515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135778923280542639985252343 203668384920813959977878515)
  ·
    refine ⟨305502577381220939966817773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203668384920813959977878515 305502577381220939966817773)
    ·
      refine ⟨114563466517957852487556665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 305502577381220939966817773 114563466517957852487556665)
      ·
        refine ⟨85922599888468389365667499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114563466517957852487556665 85922599888468389365667499)
        ·
          refine ⟨128883899832702584048501249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85922599888468389365667499 128883899832702584048501249)
          ·
            refine ⟨96662924874526938036375937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128883899832702584048501249 96662924874526938036375937)
            ·
              refine ⟨72497193655895203527281953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96662924874526938036375937 72497193655895203527281953)
              ·
                refine ⟨54372895241921402645461465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72497193655895203527281953 54372895241921402645461465)
                ·
                  refine ⟨40779671431441051984096099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54372895241921402645461465 40779671431441051984096099)
                  ·
                    refine ⟨61169507147161577976144149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40779671431441051984096099 61169507147161577976144149)
                    ·
                      refine ⟨2867320647523198967631757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61169507147161577976144149 2867320647523198967631757)
                      ·
                        rfl

theorem cell23_5584087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 2, 2, 1, 6].length) (baseStart_5584087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5584087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5584087 prefixEnd_5584087 := by exact prefixLift 5584087
  have htrace : WordTrace (prefixWord ++ tailWord_5584087) baseStart_5584087 baseEnd_5584087 := by
    simpa [prefixWord, tailWord_5584087, baseEnd_5584087] using wordTrace_append hprefix tailTrace_5584087
  have hstable : (prefixWord ++ tailWord_5584087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5584087).length < 2 ^ (prefixWord ++ tailWord_5584087).sum := by decide
  have hdescent : baseEnd_5584087 < baseStart_5584087 := by decide
  rcases family_descends (prefixWord ++ tailWord_5584087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5584118 : List Nat := [5, 1, 1, 1, 1, 1, 1, 7, 1, 4]
def baseStart_5584118 : Nat := 118140960795 + 5584118 * 2 ^ 59
def prefixEnd_5584118 : Nat := 4983230072969 + 3 ^ 40 * 5584118 * 2
def baseEnd_5584118 : Nat := 955778855141162782114705

theorem tailTrace_5584118 : CollatzResearch.WordTrace tailWord_5584118 prefixEnd_5584118 955778855141162782114705 := by
  unfold tailWord_5584118
  simp only [CollatzResearch.WordTrace]
  refine ⟨12729344723981353267016063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 135779677055801101514838005 12729344723981353267016063)
  ·
    refine ⟨19094017085972029900524095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12729344723981353267016063 19094017085972029900524095)
    ·
      refine ⟨28641025628958044850786143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19094017085972029900524095 28641025628958044850786143)
      ·
        refine ⟨42961538443437067276179215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28641025628958044850786143 42961538443437067276179215)
        ·
          refine ⟨64442307665155600914268823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42961538443437067276179215 64442307665155600914268823)
          ·
            refine ⟨96663461497733401371403235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64442307665155600914268823 96663461497733401371403235)
            ·
              refine ⟨144995192246600102057104853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96663461497733401371403235 144995192246600102057104853)
              ·
                refine ⟨3398324818279689891963395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 144995192246600102057104853 3398324818279689891963395)
                ·
                  refine ⟨5097487227419534837945093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3398324818279689891963395 5097487227419534837945093)
                  ·
                    refine ⟨955778855141162782114705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5097487227419534837945093 955778855141162782114705)
                    ·
                      rfl

theorem cell23_5584118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 7, 1, 4].length) (baseStart_5584118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5584118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5584118 prefixEnd_5584118 := by exact prefixLift 5584118
  have htrace : WordTrace (prefixWord ++ tailWord_5584118) baseStart_5584118 baseEnd_5584118 := by
    simpa [prefixWord, tailWord_5584118, baseEnd_5584118] using wordTrace_append hprefix tailTrace_5584118
  have hstable : (prefixWord ++ tailWord_5584118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5584118).length < 2 ^ (prefixWord ++ tailWord_5584118).sum := by decide
  have hdescent : baseEnd_5584118 < baseStart_5584118 := by decide
  rcases family_descends (prefixWord ++ tailWord_5584118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5584151 : List Nat := [1, 1, 3, 4, 1, 1, 2, 2, 1, 5, 2]
def baseStart_5584151 : Nat := 118140960795 + 5584151 * 2 ^ 59
def prefixEnd_5584151 : Nat := 4983230072969 + 3 ^ 40 * 5584151 * 2
def baseEnd_5584151 : Nat := 2867353510285086717231463

theorem tailTrace_5584151 : CollatzResearch.WordTrace tailWord_5584151 prefixEnd_5584151 2867353510285086717231463 := by
  unfold tailWord_5584151
  simp only [CollatzResearch.WordTrace]
  refine ⟨203670719192582098908208307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135780479461721399272138871 203670719192582098908208307)
  ·
    refine ⟨305506078788873148362312461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203670719192582098908208307 305506078788873148362312461)
    ·
      refine ⟨114564779545827430635867173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 305506078788873148362312461 114564779545827430635867173)
      ·
        refine ⟨21480896164842643244225095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 114564779545827430635867173 21480896164842643244225095)
        ·
          refine ⟨32221344247263964866337643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21480896164842643244225095 32221344247263964866337643)
          ·
            refine ⟨48332016370895947299506465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32221344247263964866337643 48332016370895947299506465)
            ·
              refine ⟨36249012278171960474629849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48332016370895947299506465 36249012278171960474629849)
              ·
                refine ⟨27186759208628970355972387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36249012278171960474629849 27186759208628970355972387)
                ·
                  refine ⟨40780138812943455533958581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27186759208628970355972387 40780138812943455533958581)
                  ·
                    refine ⟨3823138013713448956308617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40780138812943455533958581 3823138013713448956308617)
                    ·
                      refine ⟨2867353510285086717231463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3823138013713448956308617 2867353510285086717231463)
                      ·
                        rfl

theorem cell23_5584151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 2, 1, 5, 2].length) (baseStart_5584151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5584151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5584151 prefixEnd_5584151 := by exact prefixLift 5584151
  have htrace : WordTrace (prefixWord ++ tailWord_5584151) baseStart_5584151 baseEnd_5584151 := by
    simpa [prefixWord, tailWord_5584151, baseEnd_5584151] using wordTrace_append hprefix tailTrace_5584151
  have hstable : (prefixWord ++ tailWord_5584151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5584151).length < 2 ^ (prefixWord ++ tailWord_5584151).sum := by decide
  have hdescent : baseEnd_5584151 < baseStart_5584151 := by decide
  rcases family_descends (prefixWord ++ tailWord_5584151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5584168 : List Nat := [2, 1, 5, 1, 2, 2, 1, 1, 1, 5, 2]
def baseStart_5584168 : Nat := 118140960795 + 5584168 * 2 ^ 59
def prefixEnd_5584168 : Nat := 4983230072969 + 3 ^ 40 * 5584168 * 2
def baseEnd_5584168 : Nat := 2867362239456213150718885

theorem tailTrace_5584168 : CollatzResearch.WordTrace tailWord_5584168 prefixEnd_5584168 2867362239456213150718885 := by
  unfold tailWord_5584168
  simp only [CollatzResearch.WordTrace]
  refine ⟨101835669616760255405788579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135780892822347007207718105 101835669616760255405788579)
  ·
    refine ⟨152753504425140383108682869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101835669616760255405788579 152753504425140383108682869)
    ·
      refine ⟨14320641039856910916439019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 152753504425140383108682869 14320641039856910916439019)
      ·
        refine ⟨21480961559785366374658529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14320641039856910916439019 21480961559785366374658529)
        ·
          refine ⟨16110721169839024780993897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21480961559785366374658529 16110721169839024780993897)
          ·
            refine ⟨12083040877379268585745423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16110721169839024780993897 12083040877379268585745423)
            ·
              refine ⟨18124561316068902878618135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12083040877379268585745423 18124561316068902878618135)
              ·
                refine ⟨27186841974103354317927203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18124561316068902878618135 27186841974103354317927203)
                ·
                  refine ⟨40780262961155031476890805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27186841974103354317927203 40780262961155031476890805)
                  ·
                    refine ⟨3823149652608284200958513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40780262961155031476890805 3823149652608284200958513)
                    ·
                      refine ⟨2867362239456213150718885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3823149652608284200958513 2867362239456213150718885)
                      ·
                        rfl

theorem cell23_5584168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 1, 1, 5, 2].length) (baseStart_5584168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5584168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5584168 prefixEnd_5584168 := by exact prefixLift 5584168
  have htrace : WordTrace (prefixWord ++ tailWord_5584168) baseStart_5584168 baseEnd_5584168 := by
    simpa [prefixWord, tailWord_5584168, baseEnd_5584168] using wordTrace_append hprefix tailTrace_5584168
  have hstable : (prefixWord ++ tailWord_5584168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5584168).length < 2 ^ (prefixWord ++ tailWord_5584168).sum := by decide
  have hdescent : baseEnd_5584168 < baseStart_5584168 := by decide
  rcases family_descends (prefixWord ++ tailWord_5584168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5584178 : List Nat := [3, 2, 1, 1, 4, 1, 4, 1, 1, 5]
def baseStart_5584178 : Nat := 118140960795 + 5584178 * 2 ^ 59
def prefixEnd_5584178 : Nat := 4983230072969 + 3 ^ 40 * 5584178 * 2
def baseEnd_5584178 : Nat := 955789124754252703864613

theorem tailTrace_5584178 : CollatzResearch.WordTrace tailWord_5584178 prefixEnd_5584178 955789124754252703864613 := by
  unfold tailWord_5584178
  simp only [CollatzResearch.WordTrace]
  refine ⟨50917925990871070629860297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135781135975656188346294125 50917925990871070629860297)
  ·
    refine ⟨38188444493153302972395223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50917925990871070629860297 38188444493153302972395223)
    ·
      refine ⟨57282666739729954458592835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38188444493153302972395223 57282666739729954458592835)
      ·
        refine ⟨85924000109594931687889253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57282666739729954458592835 85924000109594931687889253)
        ·
          refine ⟨16110750020549049691479235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85924000109594931687889253 16110750020549049691479235)
          ·
            refine ⟨24166125030823574537218853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16110750020549049691479235 24166125030823574537218853)
            ·
              refine ⟨4531148443279420225728535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24166125030823574537218853 4531148443279420225728535)
              ·
                refine ⟨6796722664919130338592803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4531148443279420225728535 6796722664919130338592803)
                ·
                  refine ⟨10195083997378695507889205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6796722664919130338592803 10195083997378695507889205)
                  ·
                    refine ⟨955789124754252703864613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10195083997378695507889205 955789124754252703864613)
                    ·
                      rfl

theorem cell23_5584178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 4, 1, 1, 5].length) (baseStart_5584178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5584178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5584178 prefixEnd_5584178 := by exact prefixLift 5584178
  have htrace : WordTrace (prefixWord ++ tailWord_5584178) baseStart_5584178 baseEnd_5584178 := by
    simpa [prefixWord, tailWord_5584178, baseEnd_5584178] using wordTrace_append hprefix tailTrace_5584178
  have hstable : (prefixWord ++ tailWord_5584178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5584178).length < 2 ^ (prefixWord ++ tailWord_5584178).sum := by decide
  have hdescent : baseEnd_5584178 < baseStart_5584178 := by decide
  rcases family_descends (prefixWord ++ tailWord_5584178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5584182 : List Nat := [5, 1, 2, 3, 2, 1, 1, 2, 6]
def baseStart_5584182 : Nat := 118140960795 + 5584182 * 2 ^ 59
def prefixEnd_5584182 : Nat := 4983230072969 + 3 ^ 40 * 5584182 * 2
def baseEnd_5584182 : Nat := 318596603131708455104869

theorem tailTrace_5584182 : CollatzResearch.WordTrace tailWord_5584182 prefixEnd_5584182 318596603131708455104869 := by
  unfold tailWord_5584182
  simp only [CollatzResearch.WordTrace]
  refine ⟨12729490615966861950161675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 135781233236979860801724533 12729490615966861950161675)
  ·
    refine ⟨19094235923950292925242513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12729490615966861950161675 19094235923950292925242513)
    ·
      refine ⟨14320676942962719693931885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19094235923950292925242513 14320676942962719693931885)
      ·
        refine ⟨5370253853611019885224457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14320676942962719693931885 5370253853611019885224457)
        ·
          refine ⟨4027690390208264913918343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5370253853611019885224457 4027690390208264913918343)
          ·
            refine ⟨6041535585312397370877515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4027690390208264913918343 6041535585312397370877515)
            ·
              refine ⟨9062303377968596056316273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6041535585312397370877515 9062303377968596056316273)
              ·
                refine ⟨6796727533476447042237205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9062303377968596056316273 6796727533476447042237205)
                ·
                  refine ⟨318596603131708455104869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6796727533476447042237205 318596603131708455104869)
                  ·
                    rfl

theorem cell23_5584182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 2, 6].length) (baseStart_5584182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5584182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5584182 prefixEnd_5584182 := by exact prefixLift 5584182
  have htrace : WordTrace (prefixWord ++ tailWord_5584182) baseStart_5584182 baseEnd_5584182 := by
    simpa [prefixWord, tailWord_5584182, baseEnd_5584182] using wordTrace_append hprefix tailTrace_5584182
  have hstable : (prefixWord ++ tailWord_5584182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5584182).length < 2 ^ (prefixWord ++ tailWord_5584182).sum := by decide
  have hdescent : baseEnd_5584182 < baseStart_5584182 := by decide
  rcases family_descends (prefixWord ++ tailWord_5584182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5584184 : List Nat := [2, 1, 2, 1, 3, 1, 1, 5, 1, 1, 5]
def baseStart_5584184 : Nat := 118140960795 + 5584184 * 2 ^ 59
def prefixEnd_5584184 : Nat := 4983230072969 + 3 ^ 40 * 5584184 * 2
def baseEnd_5584184 : Nat := 2867370455146685088118811

theorem tailTrace_5584184 : CollatzResearch.WordTrace tailWord_5584184 prefixEnd_5584184 2867370455146685088118811 := by
  unfold tailWord_5584184
  simp only [CollatzResearch.WordTrace]
  refine ⟨101835961400731272772079803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135781281867641697029439737 101835961400731272772079803)
  ·
    refine ⟨152753942101096909158119705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101835961400731272772079803 152753942101096909158119705)
    ·
      refine ⟨114565456575822681868589779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152753942101096909158119705 114565456575822681868589779)
      ·
        refine ⟨171848184863734022802884669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114565456575822681868589779 171848184863734022802884669)
        ·
          refine ⟨64443069323900258551081751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 171848184863734022802884669 64443069323900258551081751)
          ·
            refine ⟨96664603985850387826622627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64443069323900258551081751 96664603985850387826622627)
            ·
              refine ⟨144996905978775581739933941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96664603985850387826622627 144996905978775581739933941)
              ·
                refine ⟨13593459935510210788118807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 144996905978775581739933941 13593459935510210788118807)
                ·
                  refine ⟨20390189903265316182178211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13593459935510210788118807 20390189903265316182178211)
                  ·
                    refine ⟨30585284854897974273267317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20390189903265316182178211 30585284854897974273267317)
                    ·
                      refine ⟨2867370455146685088118811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30585284854897974273267317 2867370455146685088118811)
                      ·
                        rfl

theorem cell23_5584184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 5, 1, 1, 5].length) (baseStart_5584184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5584184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5584184 prefixEnd_5584184 := by exact prefixLift 5584184
  have htrace : WordTrace (prefixWord ++ tailWord_5584184) baseStart_5584184 baseEnd_5584184 := by
    simpa [prefixWord, tailWord_5584184, baseEnd_5584184] using wordTrace_append hprefix tailTrace_5584184
  have hstable : (prefixWord ++ tailWord_5584184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5584184).length < 2 ^ (prefixWord ++ tailWord_5584184).sum := by decide
  have hdescent : baseEnd_5584184 < baseStart_5584184 := by decide
  rcases family_descends (prefixWord ++ tailWord_5584184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5584191 : List Nat := [1, 1, 2, 2, 4, 3, 1, 1, 4, 4]
def baseStart_5584191 : Nat := 118140960795 + 5584191 * 2 ^ 59
def prefixEnd_5584191 : Nat := 4983230072969 + 3 ^ 40 * 5584191 * 2
def baseEnd_5584191 : Nat := 955791349837088853577093

theorem tailTrace_5584191 : CollatzResearch.WordTrace tailWord_5584191 prefixEnd_5584191 955791349837088853577093 := by
  unfold tailWord_5584191
  simp only [CollatzResearch.WordTrace]
  refine ⟨203672178112437185739664427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135781452074958123826442951 203672178112437185739664427)
  ·
    refine ⟨305508267168655778609496641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203672178112437185739664427 305508267168655778609496641)
    ·
      refine ⟨229131200376491833957122481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 305508267168655778609496641 229131200376491833957122481)
      ·
        refine ⟨171848400282368875467841861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 229131200376491833957122481 171848400282368875467841861)
        ·
          refine ⟨32221575052944164150220349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 171848400282368875467841861 32221575052944164150220349)
          ·
            refine ⟨12083090644854061556332631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32221575052944164150220349 12083090644854061556332631)
            ·
              refine ⟨18124635967281092334498947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12083090644854061556332631 18124635967281092334498947)
              ·
                refine ⟨27186953950921638501748421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18124635967281092334498947 27186953950921638501748421)
                ·
                  refine ⟨5097553865797807219077829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27186953950921638501748421 5097553865797807219077829)
                  ·
                    refine ⟨955791349837088853577093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5097553865797807219077829 955791349837088853577093)
                    ·
                      rfl

theorem cell23_5584191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 1, 4, 4].length) (baseStart_5584191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5584191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5584191 prefixEnd_5584191 := by exact prefixLift 5584191
  have htrace : WordTrace (prefixWord ++ tailWord_5584191) baseStart_5584191 baseEnd_5584191 := by
    simpa [prefixWord, tailWord_5584191, baseEnd_5584191] using wordTrace_append hprefix tailTrace_5584191
  have hstable : (prefixWord ++ tailWord_5584191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5584191).length < 2 ^ (prefixWord ++ tailWord_5584191).sum := by decide
  have hdescent : baseEnd_5584191 < baseStart_5584191 := by decide
  rcases family_descends (prefixWord ++ tailWord_5584191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5584208 : List Nat := [2, 1, 1, 1, 1, 5, 5, 1, 2, 4]
def baseStart_5584208 : Nat := 118140960795 + 5584208 * 2 ^ 59
def prefixEnd_5584208 : Nat := 4983230072969 + 3 ^ 40 * 5584208 * 2
def baseEnd_5584208 : Nat := 955794259560797664739567

theorem tailTrace_5584208 : CollatzResearch.WordTrace tailWord_5584208 prefixEnd_5584208 955794259560797664739567 := by
  unfold tailWord_5584208
  simp only [CollatzResearch.WordTrace]
  refine ⟨101836399076687798821516639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135781865435583731762022185 101836399076687798821516639)
  ·
    refine ⟨152754598615031698232274959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101836399076687798821516639 152754598615031698232274959)
    ·
      refine ⟨229131897922547547348412439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152754598615031698232274959 229131897922547547348412439)
      ·
        refine ⟨343697846883821321022618659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229131897922547547348412439 343697846883821321022618659)
        ·
          refine ⟨515546770325731981533927989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 343697846883821321022618659 515546770325731981533927989)
          ·
            refine ⟨48332509718037373268805749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 515546770325731981533927989 48332509718037373268805749)
            ·
              refine ⟨4531172786066003743950539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48332509718037373268805749 4531172786066003743950539)
              ·
                refine ⟨6796759179099005615925809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4531172786066003743950539 6796759179099005615925809)
                ·
                  refine ⟨5097569384324254211944357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6796759179099005615925809 5097569384324254211944357)
                  ·
                    refine ⟨955794259560797664739567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5097569384324254211944357 955794259560797664739567)
                    ·
                      rfl

theorem cell23_5584208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 5, 1, 2, 4].length) (baseStart_5584208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5584208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5584208 prefixEnd_5584208 := by exact prefixLift 5584208
  have htrace : WordTrace (prefixWord ++ tailWord_5584208) baseStart_5584208 baseEnd_5584208 := by
    simpa [prefixWord, tailWord_5584208, baseEnd_5584208] using wordTrace_append hprefix tailTrace_5584208
  have hstable : (prefixWord ++ tailWord_5584208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5584208).length < 2 ^ (prefixWord ++ tailWord_5584208).sum := by decide
  have hdescent : baseEnd_5584208 < baseStart_5584208 := by decide
  rcases family_descends (prefixWord ++ tailWord_5584208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5584238 : List Nat := [4, 1, 2, 4, 1, 2, 9]
def baseStart_5584238 : Nat := 118140960795 + 5584238 * 2 ^ 59
def prefixEnd_5584238 : Nat := 4983230072969 + 3 ^ 40 * 5584238 * 2
def baseEnd_5584238 : Nat := 35399977569160837985723

theorem tailTrace_5584238 : CollatzResearch.WordTrace tailWord_5584238 prefixEnd_5584238 35399977569160837985723 := by
  unfold tailWord_5584238
  simp only [CollatzResearch.WordTrace]
  refine ⟨25459236542908364095828171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135782594895511275177750245 25459236542908364095828171)
  ·
    refine ⟨38188854814362546143742257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25459236542908364095828171 38188854814362546143742257)
    ·
      refine ⟨28641641110771909607806693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38188854814362546143742257 28641641110771909607806693)
      ·
        refine ⟨5370307708269733051463755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28641641110771909607806693 5370307708269733051463755)
        ·
          refine ⟨8055461562404599577195633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5370307708269733051463755 8055461562404599577195633)
          ·
            refine ⟨6041596171803449682896725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8055461562404599577195633 6041596171803449682896725)
            ·
              refine ⟨35399977569160837985723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6041596171803449682896725 35399977569160837985723)
              ·
                rfl

theorem cell23_5584238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 9].length) (baseStart_5584238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5584238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5584238 prefixEnd_5584238 := by exact prefixLift 5584238
  have htrace : WordTrace (prefixWord ++ tailWord_5584238) baseStart_5584238 baseEnd_5584238 := by
    simpa [prefixWord, tailWord_5584238, baseEnd_5584238] using wordTrace_append hprefix tailTrace_5584238
  have hstable : (prefixWord ++ tailWord_5584238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5584238).length < 2 ^ (prefixWord ++ tailWord_5584238).sum := by decide
  have hdescent : baseEnd_5584238 < baseStart_5584238 := by decide
  rcases family_descends (prefixWord ++ tailWord_5584238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5584265 : List Nat := [1, 2, 1, 1, 7, 1, 1, 3, 2, 1, 3]
def baseStart_5584265 : Nat := 118140960795 + 5584265 * 2 ^ 59
def prefixEnd_5584265 : Nat := 4983230072969 + 3 ^ 40 * 5584265 * 2
def baseEnd_5584265 : Nat := 2867412047079699271205939

theorem tailTrace_5584265 : CollatzResearch.WordTrace tailWord_5584265 prefixEnd_5584265 2867412047079699271205939 := by
  unfold tailWord_5584265
  simp only [CollatzResearch.WordTrace]
  refine ⟨203674877114169096377858249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135783251409446064251905499 203674877114169096377858249)
  ·
    refine ⟨152756157835626822283393687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203674877114169096377858249 152756157835626822283393687)
    ·
      refine ⟨229134236753440233425090531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152756157835626822283393687 229134236753440233425090531)
      ·
        refine ⟨343701355130160350137635797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229134236753440233425090531 343701355130160350137635797)
        ·
          refine ⟨8055500510863133206350839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 343701355130160350137635797 8055500510863133206350839)
          ·
            refine ⟨12083250766294699809526259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8055500510863133206350839 12083250766294699809526259)
            ·
              refine ⟨18124876149442049714289389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12083250766294699809526259 18124876149442049714289389)
              ·
                refine ⟨6796828556040768642858521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18124876149442049714289389 6796828556040768642858521)
                ·
                  refine ⟨5097621417030576482143891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6796828556040768642858521 5097621417030576482143891)
                  ·
                    refine ⟨7646432125545864723215837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5097621417030576482143891 7646432125545864723215837)
                    ·
                      refine ⟨2867412047079699271205939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7646432125545864723215837 2867412047079699271205939)
                      ·
                        rfl

theorem cell23_5584265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 3, 2, 1, 3].length) (baseStart_5584265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5584265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5584265 prefixEnd_5584265 := by exact prefixLift 5584265
  have htrace : WordTrace (prefixWord ++ tailWord_5584265) baseStart_5584265 baseEnd_5584265 := by
    simpa [prefixWord, tailWord_5584265, baseEnd_5584265] using wordTrace_append hprefix tailTrace_5584265
  have hstable : (prefixWord ++ tailWord_5584265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5584265).length < 2 ^ (prefixWord ++ tailWord_5584265).sum := by decide
  have hdescent : baseEnd_5584265 < baseStart_5584265 := by decide
  rcases family_descends (prefixWord ++ tailWord_5584265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5584288 : List Nat := [2, 1, 1, 4, 1, 2, 3, 2, 1, 4, 2]
def baseStart_5584288 : Nat := 118140960795 + 5584288 * 2 ^ 59
def prefixEnd_5584288 : Nat := 4983230072969 + 3 ^ 40 * 5584288 * 2
def baseEnd_5584288 : Nat := 2867423857134752681218333

theorem tailTrace_5584288 : CollatzResearch.WordTrace tailWord_5584288 prefixEnd_5584288 2867423857134752681218333 := by
  unfold tailWord_5584288
  simp only [CollatzResearch.WordTrace]
  refine ⟨101837857996542885652972759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135783810662057180870630345 101837857996542885652972759)
  ·
    refine ⟨152756786994814328479459139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101837857996542885652972759 152756786994814328479459139)
    ·
      refine ⟨229135180492221492719188709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152756786994814328479459139 229135180492221492719188709)
      ·
        refine ⟨42962846342291529884847883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 229135180492221492719188709 42962846342291529884847883)
        ·
          refine ⟨64444269513437294827271825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42962846342291529884847883 64444269513437294827271825)
          ·
            refine ⟨48333202135077971120453869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64444269513437294827271825 48333202135077971120453869)
            ·
              refine ⟨18124950800654239170170201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48333202135077971120453869 18124950800654239170170201)
              ·
                refine ⟨13593713100490679377627651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18124950800654239170170201 13593713100490679377627651)
                ·
                  refine ⟨20390569650736019066441477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13593713100490679377627651 20390569650736019066441477)
                  ·
                    refine ⟨3823231809513003574957777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20390569650736019066441477 3823231809513003574957777)
                    ·
                      refine ⟨2867423857134752681218333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3823231809513003574957777 2867423857134752681218333)
                      ·
                        rfl

theorem cell23_5584288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 2, 1, 4, 2].length) (baseStart_5584288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5584288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5584288 prefixEnd_5584288 := by exact prefixLift 5584288
  have htrace : WordTrace (prefixWord ++ tailWord_5584288) baseStart_5584288 baseEnd_5584288 := by
    simpa [prefixWord, tailWord_5584288, baseEnd_5584288] using wordTrace_append hprefix tailTrace_5584288
  have hstable : (prefixWord ++ tailWord_5584288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5584288).length < 2 ^ (prefixWord ++ tailWord_5584288).sum := by decide
  have hdescent : baseEnd_5584288 < baseStart_5584288 := by decide
  rcases family_descends (prefixWord ++ tailWord_5584288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5584314 : List Nat := [3, 1, 1, 1, 2, 1, 1, 1, 1, 3, 8]
def baseStart_5584314 : Nat := 118140960795 + 5584314 * 2 ^ 59
def prefixEnd_5584314 : Nat := 4983230072969 + 3 ^ 40 * 5584314 * 2
def baseEnd_5584314 : Nat := 2867437207631769579493213

theorem tailTrace_5584314 : CollatzResearch.WordTrace tailWord_5584314 prefixEnd_5584314 2867437207631769579493213 := by
  unfold tailWord_5584314
  simp only [CollatzResearch.WordTrace]
  refine ⟨50919166072747894436597999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135784442860661051830927997 50919166072747894436597999)
  ·
    refine ⟨76378749109121841654896999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50919166072747894436597999 76378749109121841654896999)
    ·
      refine ⟨114568123663682762482345499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76378749109121841654896999 114568123663682762482345499)
      ·
        refine ⟨171852185495524143723518249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114568123663682762482345499 171852185495524143723518249)
        ·
          refine ⟨128889139121643107792638687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171852185495524143723518249 128889139121643107792638687)
          ·
            refine ⟨193333708682464661688958031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128889139121643107792638687 193333708682464661688958031)
            ·
              refine ⟨290000563023696992533437047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 193333708682464661688958031 290000563023696992533437047)
              ·
                refine ⟨435000844535545488800155571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 290000563023696992533437047 435000844535545488800155571)
                ·
                  refine ⟨652501266803318233200233357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 435000844535545488800155571 652501266803318233200233357)
                  ·
                    refine ⟨244687975051244337450087509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 652501266803318233200233357 244687975051244337450087509)
                    ·
                      refine ⟨2867437207631769579493213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 244687975051244337450087509 2867437207631769579493213)
                      ·
                        rfl

theorem cell23_5584314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 1, 3, 8].length) (baseStart_5584314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5584314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5584314 prefixEnd_5584314 := by exact prefixLift 5584314
  have htrace : WordTrace (prefixWord ++ tailWord_5584314) baseStart_5584314 baseEnd_5584314 := by
    simpa [prefixWord, tailWord_5584314, baseEnd_5584314] using wordTrace_append hprefix tailTrace_5584314
  have hstable : (prefixWord ++ tailWord_5584314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5584314).length < 2 ^ (prefixWord ++ tailWord_5584314).sum := by decide
  have hdescent : baseEnd_5584314 < baseStart_5584314 := by decide
  rcases family_descends (prefixWord ++ tailWord_5584314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5584341 : List Nat := [1, 3, 2, 3, 1, 1, 3, 1, 1, 7]
def baseStart_5584341 : Nat := 118140960795 + 5584341 * 2 ^ 59
def prefixEnd_5584341 : Nat := 4983230072969 + 3 ^ 40 * 5584341 * 2
def baseEnd_5584341 : Nat := 955817023869813657951863

theorem tailTrace_5584341 : CollatzResearch.WordTrace tailWord_5584341 prefixEnd_5584341 955817023869813657951863 := by
  unfold tailWord_5584341
  simp only [CollatzResearch.WordTrace]
  refine ⟨203677649061893761357624877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135785099374595840905083251 203677649061893761357624877)
  ·
    refine ⟨76379118398210160509109329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 203677649061893761357624877 76379118398210160509109329)
    ·
      refine ⟨57284338798657620381831997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76379118398210160509109329 57284338798657620381831997)
      ·
        refine ⟨21481627049496607643186999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57284338798657620381831997 21481627049496607643186999)
        ·
          refine ⟨32222440574244911464780499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21481627049496607643186999 32222440574244911464780499)
          ·
            refine ⟨48333660861367367197170749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32222440574244911464780499 48333660861367367197170749)
            ·
              refine ⟨18125122823012762698939031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48333660861367367197170749 18125122823012762698939031)
              ·
                refine ⟨27187684234519144048408547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18125122823012762698939031 27187684234519144048408547)
                ·
                  refine ⟨40781526351778716072612821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27187684234519144048408547 40781526351778716072612821)
                  ·
                    refine ⟨955817023869813657951863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40781526351778716072612821 955817023869813657951863)
                    ·
                      rfl

theorem cell23_5584341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 1, 1, 7].length) (baseStart_5584341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5584341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5584341 prefixEnd_5584341 := by exact prefixLift 5584341
  have htrace : WordTrace (prefixWord ++ tailWord_5584341) baseStart_5584341 baseEnd_5584341 := by
    simpa [prefixWord, tailWord_5584341, baseEnd_5584341] using wordTrace_append hprefix tailTrace_5584341
  have hstable : (prefixWord ++ tailWord_5584341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5584341).length < 2 ^ (prefixWord ++ tailWord_5584341).sum := by decide
  have hdescent : baseEnd_5584341 < baseStart_5584341 := by decide
  rcases family_descends (prefixWord ++ tailWord_5584341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5584378 : List Nat := [3, 1, 1, 1, 1, 2, 3, 3, 2, 4, 2]
def baseStart_5584378 : Nat := 118140960795 + 5584378 * 2 ^ 59
def prefixEnd_5584378 : Nat := 4983230072969 + 3 ^ 40 * 5584378 * 2
def baseEnd_5584378 : Nat := 2867470070393657329092919

theorem tailTrace_5584378 : CollatzResearch.WordTrace tailWord_5584378 prefixEnd_5584378 2867470070393657329092919 := by
  unfold tailWord_5584378
  simp only [CollatzResearch.WordTrace]
  refine ⟨50919749640689929169180447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135785999041839811117814525 50919749640689929169180447)
  ·
    refine ⟨76379624461034893753770671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50919749640689929169180447 76379624461034893753770671)
    ·
      refine ⟨114569436691552340630656007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76379624461034893753770671 114569436691552340630656007)
      ·
        refine ⟨171854155037328510945984011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114569436691552340630656007 171854155037328510945984011)
        ·
          refine ⟨257781232555992766418976017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171854155037328510945984011 257781232555992766418976017)
          ·
            refine ⟨193335924416994574814232013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 257781232555992766418976017 193335924416994574814232013)
            ·
              refine ⟨72500971656372965555337005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 193335924416994574814232013 72500971656372965555337005)
              ·
                refine ⟨27187864371139862083251377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72500971656372965555337005 27187864371139862083251377)
                ·
                  refine ⟨20390898278354896562438533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27187864371139862083251377 20390898278354896562438533)
                  ·
                    refine ⟨3823293427191543105457225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20390898278354896562438533 3823293427191543105457225)
                    ·
                      refine ⟨2867470070393657329092919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3823293427191543105457225 2867470070393657329092919)
                      ·
                        rfl

theorem cell23_5584378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 3, 2, 4, 2].length) (baseStart_5584378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5584378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5584378 prefixEnd_5584378 := by exact prefixLift 5584378
  have htrace : WordTrace (prefixWord ++ tailWord_5584378) baseStart_5584378 baseEnd_5584378 := by
    simpa [prefixWord, tailWord_5584378, baseEnd_5584378] using wordTrace_append hprefix tailTrace_5584378
  have hstable : (prefixWord ++ tailWord_5584378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5584378).length < 2 ^ (prefixWord ++ tailWord_5584378).sum := by decide
  have hdescent : baseEnd_5584378 < baseStart_5584378 := by decide
  rcases family_descends (prefixWord ++ tailWord_5584378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5584435 : List Nat := [1, 1, 1, 2, 4, 5, 2, 1, 6]
def baseStart_5584435 : Nat := 118140960795 + 5584435 * 2 ^ 59
def prefixEnd_5584435 : Nat := 4983230072969 + 3 ^ 40 * 5584435 * 2
def baseEnd_5584435 : Nat := 318611037643440400675573

theorem tailTrace_5584435 : CollatzResearch.WordTrace tailWord_5584435 prefixEnd_5584435 318611037643440400675573 := by
  unfold tailWord_5584435
  simp only [CollatzResearch.WordTrace]
  refine ⟨203681077523553215411546759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135787385015702143607697839 203681077523553215411546759)
  ·
    refine ⟨305521616285329823117320139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203681077523553215411546759 305521616285329823117320139)
    ·
      refine ⟨458282424427994734675980209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305521616285329823117320139 458282424427994734675980209)
      ·
        refine ⟨343711818320996051006985157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 458282424427994734675980209 343711818320996051006985157)
        ·
          refine ⟨64445965935186759563809717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 343711818320996051006985157 64445965935186759563809717)
          ·
            refine ⟨6041809306423758709107161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 64445965935186759563809717 6041809306423758709107161)
            ·
              refine ⟨4531356979817819031830371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6041809306423758709107161 4531356979817819031830371)
              ·
                refine ⟨6797035469726728547745557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4531356979817819031830371 6797035469726728547745557)
                ·
                  refine ⟨318611037643440400675573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6797035469726728547745557 318611037643440400675573)
                  ·
                    rfl

theorem cell23_5584435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 2, 1, 6].length) (baseStart_5584435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5584435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5584435 prefixEnd_5584435 := by exact prefixLift 5584435
  have htrace : WordTrace (prefixWord ++ tailWord_5584435) baseStart_5584435 baseEnd_5584435 := by
    simpa [prefixWord, tailWord_5584435, baseEnd_5584435] using wordTrace_append hprefix tailTrace_5584435
  have hstable : (prefixWord ++ tailWord_5584435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5584435).length < 2 ^ (prefixWord ++ tailWord_5584435).sum := by decide
  have hdescent : baseEnd_5584435 < baseStart_5584435 := by decide
  rcases family_descends (prefixWord ++ tailWord_5584435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5584462 : List Nat := [4, 1, 1, 1, 1, 2, 1, 7, 1, 1, 3]
def baseStart_5584462 : Nat := 118140960795 + 5584462 * 2 ^ 59
def prefixEnd_5584462 : Nat := 4983230072969 + 3 ^ 40 * 5584462 * 2
def baseEnd_5584462 : Nat := 2867513202768635000442533

theorem tailTrace_5584462 : CollatzResearch.WordTrace tailWord_5584462 prefixEnd_5584462 2867513202768635000442533 := by
  unfold tailWord_5584462
  simp only [CollatzResearch.WordTrace]
  refine ⟨25460257786806924877847455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135788041529636932681853093 25460257786806924877847455)
  ·
    refine ⟨38190386680210387316771183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25460257786806924877847455 38190386680210387316771183)
    ·
      refine ⟨57285580020315580975156775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38190386680210387316771183 57285580020315580975156775)
      ·
        refine ⟨85928370030473371462735163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57285580020315580975156775 85928370030473371462735163)
        ·
          refine ⟨128892555045710057194102745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85928370030473371462735163 128892555045710057194102745)
          ·
            refine ⟨96669416284282542895577059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128892555045710057194102745 96669416284282542895577059)
            ·
              refine ⟨145004124426423814343365589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96669416284282542895577059 145004124426423814343365589)
              ·
                refine ⟨3398534166244308148672631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 145004124426423814343365589 3398534166244308148672631)
                ·
                  refine ⟨5097801249366462223008947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3398534166244308148672631 5097801249366462223008947)
                  ·
                    refine ⟨7646701874049693334513421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5097801249366462223008947 7646701874049693334513421)
                    ·
                      refine ⟨2867513202768635000442533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7646701874049693334513421 2867513202768635000442533)
                      ·
                        rfl

theorem cell23_5584462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 7, 1, 1, 3].length) (baseStart_5584462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5584462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5584462 prefixEnd_5584462 := by exact prefixLift 5584462
  have htrace : WordTrace (prefixWord ++ tailWord_5584462) baseStart_5584462 baseEnd_5584462 := by
    simpa [prefixWord, tailWord_5584462, baseEnd_5584462] using wordTrace_append hprefix tailTrace_5584462
  have hstable : (prefixWord ++ tailWord_5584462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5584462).length < 2 ^ (prefixWord ++ tailWord_5584462).sum := by decide
  have hdescent : baseEnd_5584462 < baseStart_5584462 := by decide
  rcases family_descends (prefixWord ++ tailWord_5584462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5584465 : List Nat := [1, 2, 2, 1, 3, 2, 5, 1, 1, 5]
def baseStart_5584465 : Nat := 118140960795 + 5584465 * 2 ^ 59
def prefixEnd_5584465 : Nat := 4983230072969 + 3 ^ 40 * 5584465 * 2
def baseEnd_5584465 : Nat := 955838247736866162901673

theorem tailTrace_5584465 : CollatzResearch.WordTrace tailWord_5584465 prefixEnd_5584465 955838247736866162901673 := by
  unfold tailWord_5584465
  simp only [CollatzResearch.WordTrace]
  refine ⟨203682171713444530535138849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135788114475629687023425899 203682171713444530535138849)
  ·
    refine ⟨152761628785083397901354137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203682171713444530535138849 152761628785083397901354137)
    ·
      refine ⟨114571221588812548426015603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152761628785083397901354137 114571221588812548426015603)
      ·
        refine ⟨171856832383218822639023405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114571221588812548426015603 171856832383218822639023405)
        ·
          refine ⟨64446312143707058489633777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 171856832383218822639023405 64446312143707058489633777)
          ·
            refine ⟨48334734107780293867225333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64446312143707058489633777 48334734107780293867225333)
            ·
              refine ⟨4531381322604402550052375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48334734107780293867225333 4531381322604402550052375)
              ·
                refine ⟨6797071983906603825078563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4531381322604402550052375 6797071983906603825078563)
                ·
                  refine ⟨10195607975859905737617845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6797071983906603825078563 10195607975859905737617845)
                  ·
                    refine ⟨955838247736866162901673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10195607975859905737617845 955838247736866162901673)
                    ·
                      rfl

theorem cell23_5584465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 5, 1, 1, 5].length) (baseStart_5584465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5584465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5584465 prefixEnd_5584465 := by exact prefixLift 5584465
  have htrace : WordTrace (prefixWord ++ tailWord_5584465) baseStart_5584465 baseEnd_5584465 := by
    simpa [prefixWord, tailWord_5584465, baseEnd_5584465] using wordTrace_append hprefix tailTrace_5584465
  have hstable : (prefixWord ++ tailWord_5584465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5584465).length < 2 ^ (prefixWord ++ tailWord_5584465).sum := by decide
  have hdescent : baseEnd_5584465 < baseStart_5584465 := by decide
  rcases family_descends (prefixWord ++ tailWord_5584465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5584505 : List Nat := [1, 2, 1, 3, 3, 1, 2, 4, 1, 2, 3]
def baseStart_5584505 : Nat := 118140960795 + 5584505 * 2 ^ 59
def prefixEnd_5584505 : Nat := 4983230072969 + 3 ^ 40 * 5584505 * 2
def baseEnd_5584505 : Nat := 2867535282436778332204835

theorem tailTrace_5584505 : CollatzResearch.WordTrace tailWord_5584505 prefixEnd_5584505 2867535282436778332204835 := by
  unfold tailWord_5584505
  simp only [CollatzResearch.WordTrace]
  refine ⟨203683630633299617366594969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135789087088866411577729979 203683630633299617366594969)
  ·
    refine ⟨152762722974974713024946227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203683630633299617366594969 152762722974974713024946227)
    ·
      refine ⟨229144084462462069537419341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152762722974974713024946227 229144084462462069537419341)
      ·
        refine ⟨85929031673423276076532253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 229144084462462069537419341 85929031673423276076532253)
        ·
          refine ⟨32223386877533728528699595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85929031673423276076532253 32223386877533728528699595)
          ·
            refine ⟨48335080316300592793049393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32223386877533728528699595 48335080316300592793049393)
            ·
              refine ⟨36251310237225444594787045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48335080316300592793049393 36251310237225444594787045)
              ·
                refine ⟨6797120669479770861522571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36251310237225444594787045 6797120669479770861522571)
                ·
                  refine ⟨10195681004219656292283857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6797120669479770861522571 10195681004219656292283857)
                  ·
                    refine ⟨7646760753164742219212893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10195681004219656292283857 7646760753164742219212893)
                    ·
                      refine ⟨2867535282436778332204835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7646760753164742219212893 2867535282436778332204835)
                      ·
                        rfl

theorem cell23_5584505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 4, 1, 2, 3].length) (baseStart_5584505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5584505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5584505 prefixEnd_5584505 := by exact prefixLift 5584505
  have htrace : WordTrace (prefixWord ++ tailWord_5584505) baseStart_5584505 baseEnd_5584505 := by
    simpa [prefixWord, tailWord_5584505, baseEnd_5584505] using wordTrace_append hprefix tailTrace_5584505
  have hstable : (prefixWord ++ tailWord_5584505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5584505).length < 2 ^ (prefixWord ++ tailWord_5584505).sum := by decide
  have hdescent : baseEnd_5584505 < baseStart_5584505 := by decide
  rcases family_descends (prefixWord ++ tailWord_5584505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5584511 : List Nat := [1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 6]
def baseStart_5584511 : Nat := 118140960795 + 5584511 * 2 ^ 59
def prefixEnd_5584511 : Nat := 4983230072969 + 3 ^ 40 * 5584511 * 2
def baseEnd_5584511 : Nat := 2867538363320705308729807

theorem tailTrace_5584511 : CollatzResearch.WordTrace tailWord_5584511 prefixEnd_5584511 2867538363320705308729807 := by
  unfold tailWord_5584511
  simp only [CollatzResearch.WordTrace]
  refine ⟨203683849471277880391313387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135789232980851920260875591 203683849471277880391313387)
  ·
    refine ⟨305525774206916820586970081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203683849471277880391313387 305525774206916820586970081)
    ·
      refine ⟨229144330655187615440227561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 305525774206916820586970081 229144330655187615440227561)
      ·
        refine ⟨171858247991390711580170671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 229144330655187615440227561 171858247991390711580170671)
        ·
          refine ⟨257787371987086067370256007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171858247991390711580170671 257787371987086067370256007)
          ·
            refine ⟨386681057980629101055384011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 257787371987086067370256007 386681057980629101055384011)
            ·
              refine ⟨580021586970943651583076017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 386681057980629101055384011 580021586970943651583076017)
              ·
                refine ⟨435016190228207738687307013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 580021586970943651583076017 435016190228207738687307013)
                ·
                  refine ⟨81565535667788951003870065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 435016190228207738687307013 81565535667788951003870065)
                  ·
                    refine ⟨61174151750841713252902549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 81565535667788951003870065 61174151750841713252902549)
                    ·
                      refine ⟨2867538363320705308729807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61174151750841713252902549 2867538363320705308729807)
                      ·
                        rfl

theorem cell23_5584511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 6].length) (baseStart_5584511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5584511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5584511 prefixEnd_5584511 := by exact prefixLift 5584511
  have htrace : WordTrace (prefixWord ++ tailWord_5584511) baseStart_5584511 baseEnd_5584511 := by
    simpa [prefixWord, tailWord_5584511, baseEnd_5584511] using wordTrace_append hprefix tailTrace_5584511
  have hstable : (prefixWord ++ tailWord_5584511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5584511).length < 2 ^ (prefixWord ++ tailWord_5584511).sum := by decide
  have hdescent : baseEnd_5584511 < baseStart_5584511 := by decide
  rcases family_descends (prefixWord ++ tailWord_5584511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5584519 : List Nat := [1, 1, 4, 2, 1, 3, 1, 5, 1, 2, 2]
def baseStart_5584519 : Nat := 118140960795 + 5584519 * 2 ^ 59
def prefixEnd_5584519 : Nat := 4983230072969 + 3 ^ 40 * 5584519 * 2
def baseEnd_5584519 : Nat := 2867542471165941277429771

theorem tailTrace_5584519 : CollatzResearch.WordTrace tailWord_5584519 prefixEnd_5584519 2867542471165941277429771 := by
  unfold tailWord_5584519
  simp only [CollatzResearch.WordTrace]
  refine ⟨203684141255248897757604611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135789427503499265171736407 203684141255248897757604611)
  ·
    refine ⟨305526211882873346636406917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203684141255248897757604611 305526211882873346636406917)
    ·
      refine ⟨57286164728038752494326297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 305526211882873346636406917 57286164728038752494326297)
      ·
        refine ⟨42964623546029064370744723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57286164728038752494326297 42964623546029064370744723)
        ·
          refine ⟨64446935319043596556117085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42964623546029064370744723 64446935319043596556117085)
          ·
            refine ⟨24167600744641348708543907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64446935319043596556117085 24167600744641348708543907)
            ·
              refine ⟨36251401116962023062815861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24167600744641348708543907 36251401116962023062815861)
              ·
                refine ⟨3398568854715189662138987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36251401116962023062815861 3398568854715189662138987)
                ·
                  refine ⟨5097853282072784493208481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3398568854715189662138987 5097853282072784493208481)
                  ·
                    refine ⟨3823389961554588369906361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5097853282072784493208481 3823389961554588369906361)
                    ·
                      refine ⟨2867542471165941277429771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3823389961554588369906361 2867542471165941277429771)
                      ·
                        rfl

theorem cell23_5584519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 5, 1, 2, 2].length) (baseStart_5584519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5584519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5584519 prefixEnd_5584519 := by exact prefixLift 5584519
  have htrace : WordTrace (prefixWord ++ tailWord_5584519) baseStart_5584519 baseEnd_5584519 := by
    simpa [prefixWord, tailWord_5584519, baseEnd_5584519] using wordTrace_append hprefix tailTrace_5584519
  have hstable : (prefixWord ++ tailWord_5584519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5584519).length < 2 ^ (prefixWord ++ tailWord_5584519).sum := by decide
  have hdescent : baseEnd_5584519 < baseStart_5584519 := by decide
  rcases family_descends (prefixWord ++ tailWord_5584519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5584522 : List Nat := [3, 1, 2, 3, 2, 2, 1, 3, 1, 2, 3]
def baseStart_5584522 : Nat := 118140960795 + 5584522 * 2 ^ 59
def prefixEnd_5584522 : Nat := 4983230072969 + 3 ^ 40 * 5584522 * 2
def baseEnd_5584522 : Nat := 2867544011607904765692257

theorem tailTrace_5584522 : CollatzResearch.WordTrace tailWord_5584522 prefixEnd_5584522 2867544011607904765692257 := by
  unfold tailWord_5584522
  simp only [CollatzResearch.WordTrace]
  refine ⟨50921062668559507317490955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135789500449492019513309213 50921062668559507317490955)
  ·
    refine ⟨76381594002839260976236433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50921062668559507317490955 76381594002839260976236433)
    ·
      refine ⟨57286195502129445732177325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76381594002839260976236433 57286195502129445732177325)
      ·
        refine ⟨21482323313298542149566497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57286195502129445732177325 21482323313298542149566497)
        ·
          refine ⟨16111742484973906612174873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21482323313298542149566497 16111742484973906612174873)
          ·
            refine ⟨12083806863730429959131155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16111742484973906612174873 12083806863730429959131155)
            ·
              refine ⟨18125710295595644938696733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12083806863730429959131155 18125710295595644938696733)
              ·
                refine ⟨6797141360848366852011275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18125710295595644938696733 6797141360848366852011275)
                ·
                  refine ⟨10195712041272550278016913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6797141360848366852011275 10195712041272550278016913)
                  ·
                    refine ⟨7646784030954412708512685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10195712041272550278016913 7646784030954412708512685)
                    ·
                      refine ⟨2867544011607904765692257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7646784030954412708512685 2867544011607904765692257)
                      ·
                        rfl

theorem cell23_5584522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 3, 1, 2, 3].length) (baseStart_5584522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5584522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5584522 prefixEnd_5584522 := by exact prefixLift 5584522
  have htrace : WordTrace (prefixWord ++ tailWord_5584522) baseStart_5584522 baseEnd_5584522 := by
    simpa [prefixWord, tailWord_5584522, baseEnd_5584522] using wordTrace_append hprefix tailTrace_5584522
  have hstable : (prefixWord ++ tailWord_5584522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5584522).length < 2 ^ (prefixWord ++ tailWord_5584522).sum := by decide
  have hdescent : baseEnd_5584522 < baseStart_5584522 := by decide
  rcases family_descends (prefixWord ++ tailWord_5584522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5584531 : List Nat := [1, 1, 1, 2, 1, 2, 2, 1, 2, 3, 7]
def baseStart_5584531 : Nat := 118140960795 + 5584531 * 2 ^ 59
def prefixEnd_5584531 : Nat := 4983230072969 + 3 ^ 40 * 5584531 * 2
def baseEnd_5584531 : Nat := 2867548632933795230479715

theorem tailTrace_5584531 : CollatzResearch.WordTrace tailWord_5584531 prefixEnd_5584531 2867548632933795230479715 := by
  unfold tailWord_5584531
  simp only [CollatzResearch.WordTrace]
  refine ⟨203684578931205423807041447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135789719287470282538027631 203684578931205423807041447)
  ·
    refine ⟨305526868396808135710562171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203684578931205423807041447 305526868396808135710562171)
    ·
      refine ⟨458290302595212203565843257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305526868396808135710562171 458290302595212203565843257)
      ·
        refine ⟨343717726946409152674382443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 458290302595212203565843257 343717726946409152674382443)
        ·
          refine ⟨515576590419613729011573665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 343717726946409152674382443 515576590419613729011573665)
          ·
            refine ⟨386682442814710296758680249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 515576590419613729011573665 386682442814710296758680249)
            ·
              refine ⟨290011832111032722569010187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 386682442814710296758680249 290011832111032722569010187)
              ·
                refine ⟨435017748166549083853515281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 290011832111032722569010187 435017748166549083853515281)
                ·
                  refine ⟨326263311124911812890136461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 435017748166549083853515281 326263311124911812890136461)
                  ·
                    refine ⟨122348741671841929833801173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 326263311124911812890136461 122348741671841929833801173)
                    ·
                      refine ⟨2867548632933795230479715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 122348741671841929833801173 2867548632933795230479715)
                      ·
                        rfl

theorem cell23_5584531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 3, 7].length) (baseStart_5584531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5584531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5584531 prefixEnd_5584531 := by exact prefixLift 5584531
  have htrace : WordTrace (prefixWord ++ tailWord_5584531) baseStart_5584531 baseEnd_5584531 := by
    simpa [prefixWord, tailWord_5584531, baseEnd_5584531] using wordTrace_append hprefix tailTrace_5584531
  have hstable : (prefixWord ++ tailWord_5584531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5584531).length < 2 ^ (prefixWord ++ tailWord_5584531).sum := by decide
  have hdescent : baseEnd_5584531 < baseStart_5584531 := by decide
  rcases family_descends (prefixWord ++ tailWord_5584531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5584546 : List Nat := [3, 3, 1, 4, 1, 1, 3, 1, 2, 4]
def baseStart_5584546 : Nat := 118140960795 + 5584546 * 2 ^ 59
def prefixEnd_5584546 : Nat := 4983230072969 + 3 ^ 40 * 5584546 * 2
def baseEnd_5584546 : Nat := 955852111714537557264049

theorem tailTrace_5584546 : CollatzResearch.WordTrace tailWord_5584546 prefixEnd_5584546 955852111714537557264049 := by
  unfold tailWord_5584546
  simp only [CollatzResearch.WordTrace]
  refine ⟨50921281506537770342209373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135790084017434054245891661 50921281506537770342209373)
  ·
    refine ⟨19095480564951663878328515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50921281506537770342209373 19095480564951663878328515)
    ·
      refine ⟨28643220847427495817492773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19095480564951663878328515 28643220847427495817492773)
      ·
        refine ⟨5370603908892655465779895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28643220847427495817492773 5370603908892655465779895)
        ·
          refine ⟨8055905863338983198669843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5370603908892655465779895 8055905863338983198669843)
          ·
            refine ⟨12083858795008474798004765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8055905863338983198669843 12083858795008474798004765)
            ·
              refine ⟨4531447048128178049251787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12083858795008474798004765 4531447048128178049251787)
              ·
                refine ⟨6797170572192267073877681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4531447048128178049251787 6797170572192267073877681)
                ·
                  refine ⟨5097877929144200305408261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6797170572192267073877681 5097877929144200305408261)
                  ·
                    refine ⟨955852111714537557264049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5097877929144200305408261 955852111714537557264049)
                    ·
                      rfl

theorem cell23_5584546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 3, 1, 2, 4].length) (baseStart_5584546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5584546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5584546 prefixEnd_5584546 := by exact prefixLift 5584546
  have htrace : WordTrace (prefixWord ++ tailWord_5584546) baseStart_5584546 baseEnd_5584546 := by
    simpa [prefixWord, tailWord_5584546, baseEnd_5584546] using wordTrace_append hprefix tailTrace_5584546
  have hstable : (prefixWord ++ tailWord_5584546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5584546).length < 2 ^ (prefixWord ++ tailWord_5584546).sum := by decide
  have hdescent : baseEnd_5584546 < baseStart_5584546 := by decide
  rcases family_descends (prefixWord ++ tailWord_5584546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5584562 : List Nat := [3, 2, 1, 1, 1, 2, 3, 4, 1, 3, 2]
def baseStart_5584562 : Nat := 118140960795 + 5584562 * 2 ^ 59
def prefixEnd_5584562 : Nat := 4983230072969 + 3 ^ 40 * 5584562 * 2
def baseEnd_5584562 : Nat := 2867564550834084609192073

theorem tailTrace_5584562 : CollatzResearch.WordTrace tailWord_5584562 prefixEnd_5584562 2867564550834084609192073 := by
  unfold tailWord_5584562
  simp only [CollatzResearch.WordTrace]
  refine ⟨50921427398523279025354985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135790473062728744067613293 50921427398523279025354985)
  ·
    refine ⟨38191070548892459269016239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50921427398523279025354985 38191070548892459269016239)
    ·
      refine ⟨57286605823338688903524359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38191070548892459269016239 57286605823338688903524359)
      ·
        refine ⟨85929908735008033355286539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57286605823338688903524359 85929908735008033355286539)
        ·
          refine ⟨128894863102512050032929809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85929908735008033355286539 128894863102512050032929809)
          ·
            refine ⟨96671147326884037524697357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128894863102512050032929809 96671147326884037524697357)
            ·
              refine ⟨36251680247581514071761509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96671147326884037524697357 36251680247581514071761509)
              ·
                refine ⟨6797190046421533888455283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36251680247581514071761509 6797190046421533888455283)
                ·
                  refine ⟨10195785069632300832682925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6797190046421533888455283 10195785069632300832682925)
                  ·
                    refine ⟨3823419401112112812256097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10195785069632300832682925 3823419401112112812256097)
                    ·
                      refine ⟨2867564550834084609192073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3823419401112112812256097 2867564550834084609192073)
                      ·
                        rfl

theorem cell23_5584562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 4, 1, 3, 2].length) (baseStart_5584562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5584562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5584562 prefixEnd_5584562 := by exact prefixLift 5584562
  have htrace : WordTrace (prefixWord ++ tailWord_5584562) baseStart_5584562 baseEnd_5584562 := by
    simpa [prefixWord, tailWord_5584562, baseEnd_5584562] using wordTrace_append hprefix tailTrace_5584562
  have hstable : (prefixWord ++ tailWord_5584562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5584562).length < 2 ^ (prefixWord ++ tailWord_5584562).sum := by decide
  have hdescent : baseEnd_5584562 < baseStart_5584562 := by decide
  rcases family_descends (prefixWord ++ tailWord_5584562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5584575 : List Nat := [1, 1, 2, 2, 2, 3, 2, 1, 3, 4, 2]
def baseStart_5584575 : Nat := 118140960795 + 5584575 * 2 ^ 59
def prefixEnd_5584575 : Nat := 4983230072969 + 3 ^ 40 * 5584575 * 2
def baseEnd_5584575 : Nat := 2867571226082593058329513

theorem tailTrace_5584575 : CollatzResearch.WordTrace tailWord_5584575 prefixEnd_5584575 2867571226082593058329513 := by
  unfold tailWord_5584575
  simp only [CollatzResearch.WordTrace]
  refine ⟨203686183743046019321643179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135790789162030679547762119 203686183743046019321643179)
  ·
    refine ⟨305529275614569028982464769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203686183743046019321643179 305529275614569028982464769)
    ·
      refine ⟨229146956710926771736848577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 305529275614569028982464769 229146956710926771736848577)
      ·
        refine ⟨171860217533195078802636433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 229146956710926771736848577 171860217533195078802636433)
        ·
          refine ⟨128895163149896309101977325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171860217533195078802636433 128895163149896309101977325)
          ·
            refine ⟨48335686181211115913241497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 128895163149896309101977325 48335686181211115913241497)
            ·
              refine ⟨36251764635908336934931123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48335686181211115913241497 36251764635908336934931123)
              ·
                refine ⟨54377646953862505402396685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36251764635908336934931123 54377646953862505402396685)
                ·
                  refine ⟨20391617607698439525898757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54377646953862505402396685 20391617607698439525898757)
                  ·
                    refine ⟨3823428301443457411106017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20391617607698439525898757 3823428301443457411106017)
                    ·
                      refine ⟨2867571226082593058329513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3823428301443457411106017 2867571226082593058329513)
                      ·
                        rfl

theorem cell23_5584575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 1, 3, 4, 2].length) (baseStart_5584575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5584575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5584575 prefixEnd_5584575 := by exact prefixLift 5584575
  have htrace : WordTrace (prefixWord ++ tailWord_5584575) baseStart_5584575 baseEnd_5584575 := by
    simpa [prefixWord, tailWord_5584575, baseEnd_5584575] using wordTrace_append hprefix tailTrace_5584575
  have hstable : (prefixWord ++ tailWord_5584575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5584575).length < 2 ^ (prefixWord ++ tailWord_5584575).sum := by decide
  have hdescent : baseEnd_5584575 < baseStart_5584575 := by decide
  rcases family_descends (prefixWord ++ tailWord_5584575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5584642 : List Nat := [3, 4, 1, 1, 1, 1, 2, 2, 2, 3, 3]
def baseStart_5584642 : Nat := 118140960795 + 5584642 * 2 ^ 59
def prefixEnd_5584642 : Nat := 4983230072969 + 3 ^ 40 * 5584642 * 2
def baseEnd_5584642 : Nat := 2867605629286444296191705

theorem tailTrace_5584642 : CollatzResearch.WordTrace tailWord_5584642 prefixEnd_5584642 2867605629286444296191705 := by
  unfold tailWord_5584642
  simp only [CollatzResearch.WordTrace]
  refine ⟨50922156858450822441083045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135792418289202193176221453 50922156858450822441083045)
  ·
    refine ⟨9547904410959529207703071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50922156858450822441083045 9547904410959529207703071)
    ·
      refine ⟨14321856616439293811554607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9547904410959529207703071 14321856616439293811554607)
      ·
        refine ⟨21482784924658940717331911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14321856616439293811554607 21482784924658940717331911)
        ·
          refine ⟨32224177386988411075997867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21482784924658940717331911 32224177386988411075997867)
          ·
            refine ⟨48336266080482616613996801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32224177386988411075997867 48336266080482616613996801)
            ·
              refine ⟨36252199560361962460497601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48336266080482616613996801 36252199560361962460497601)
              ·
                refine ⟨27189149670271471845373201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36252199560361962460497601 27189149670271471845373201)
                ·
                  refine ⟨20391862252703603884029901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27189149670271471845373201 20391862252703603884029901)
                  ·
                    refine ⟨7646948344763851456511213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20391862252703603884029901 7646948344763851456511213)
                    ·
                      refine ⟨2867605629286444296191705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7646948344763851456511213 2867605629286444296191705)
                      ·
                        rfl

theorem cell23_5584642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 2, 2, 3, 3].length) (baseStart_5584642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5584642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5584642 prefixEnd_5584642 := by exact prefixLift 5584642
  have htrace : WordTrace (prefixWord ++ tailWord_5584642) baseStart_5584642 baseEnd_5584642 := by
    simpa [prefixWord, tailWord_5584642, baseEnd_5584642] using wordTrace_append hprefix tailTrace_5584642
  have hstable : (prefixWord ++ tailWord_5584642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5584642).length < 2 ^ (prefixWord ++ tailWord_5584642).sum := by decide
  have hdescent : baseEnd_5584642 < baseStart_5584642 := by decide
  rcases family_descends (prefixWord ++ tailWord_5584642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5584675 : List Nat := [1, 1, 1, 4, 2, 1, 3, 1, 5, 4]
def baseStart_5584675 : Nat := 118140960795 + 5584675 * 2 ^ 59
def prefixEnd_5584675 : Nat := 4983230072969 + 3 ^ 40 * 5584675 * 2
def baseEnd_5584675 : Nat := 955874191382680889026351

theorem tailTrace_5584675 : CollatzResearch.WordTrace tailWord_5584675 prefixEnd_5584675 955874191382680889026351 := by
  unfold tailWord_5584675
  simp only [CollatzResearch.WordTrace]
  refine ⟨203689831042683736400283479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135793220695122490933522319 203689831042683736400283479)
  ·
    refine ⟨305534746564025604600425219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203689831042683736400283479 305534746564025604600425219)
    ·
      refine ⟨458302119846038406900637829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305534746564025604600425219 458302119846038406900637829)
      ·
        refine ⟨85931647471132201293869593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 458302119846038406900637829 85931647471132201293869593)
        ·
          refine ⟨64448735603349150970402195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85931647471132201293869593 64448735603349150970402195)
          ·
            refine ⟨96673103405023726455603293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64448735603349150970402195 96673103405023726455603293)
            ·
              refine ⟨36252413776883897420851235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96673103405023726455603293 36252413776883897420851235)
              ·
                refine ⟨54378620665325846131276853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36252413776883897420851235 54378620665325846131276853)
                ·
                  refine ⟨5097995687374298074807205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54378620665325846131276853 5097995687374298074807205)
                  ·
                    refine ⟨955874191382680889026351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5097995687374298074807205 955874191382680889026351)
                    ·
                      rfl

theorem cell23_5584675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 1, 5, 4].length) (baseStart_5584675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5584675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5584675 prefixEnd_5584675 := by exact prefixLift 5584675
  have htrace : WordTrace (prefixWord ++ tailWord_5584675) baseStart_5584675 baseEnd_5584675 := by
    simpa [prefixWord, tailWord_5584675, baseEnd_5584675] using wordTrace_append hprefix tailTrace_5584675
  have hstable : (prefixWord ++ tailWord_5584675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5584675).length < 2 ^ (prefixWord ++ tailWord_5584675).sum := by decide
  have hdescent : baseEnd_5584675 < baseStart_5584675 := by decide
  rcases family_descends (prefixWord ++ tailWord_5584675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5584755 : List Nat := [1, 1, 1, 2, 2, 1, 3, 2, 5, 1, 4]
def baseStart_5584755 : Nat := 118140960795 + 5584755 * 2 ^ 59
def prefixEnd_5584755 : Nat := 4983230072969 + 3 ^ 40 * 5584755 * 2
def baseEnd_5584755 : Nat := 2867663652600402354078685

theorem tailTrace_5584755 : CollatzResearch.WordTrace tailWord_5584755 prefixEnd_5584755 2867663652600402354078685 := by
  unfold tailWord_5584755
  simp only [CollatzResearch.WordTrace]
  refine ⟨203692748882393910063195719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135795165921595940042130479 203692748882393910063195719)
  ·
    refine ⟨305539123323590865094793579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203692748882393910063195719 305539123323590865094793579)
    ·
      refine ⟨458308684985386297642190369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305539123323590865094793579 458308684985386297642190369)
      ·
        refine ⟨343731513739039723231642777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 458308684985386297642190369 343731513739039723231642777)
        ·
          refine ⟨257798635304279792423732083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 343731513739039723231642777 257798635304279792423732083)
          ·
            refine ⟨386697952956419688635598125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 257798635304279792423732083 386697952956419688635598125)
            ·
              refine ⟨145011732358657383238349297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 386697952956419688635598125 145011732358657383238349297)
              ·
                refine ⟨108758799268993037428761973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 145011732358657383238349297 108758799268993037428761973)
                ·
                  refine ⟨10196137431468097258946435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 108758799268993037428761973 10196137431468097258946435)
                  ·
                    refine ⟨15294206147202145888419653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10196137431468097258946435 15294206147202145888419653)
                    ·
                      refine ⟨2867663652600402354078685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15294206147202145888419653 2867663652600402354078685)
                      ·
                        rfl

theorem cell23_5584755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 5, 1, 4].length) (baseStart_5584755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5584755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5584755 prefixEnd_5584755 := by exact prefixLift 5584755
  have htrace : WordTrace (prefixWord ++ tailWord_5584755) baseStart_5584755 baseEnd_5584755 := by
    simpa [prefixWord, tailWord_5584755, baseEnd_5584755] using wordTrace_append hprefix tailTrace_5584755
  have hstable : (prefixWord ++ tailWord_5584755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5584755).length < 2 ^ (prefixWord ++ tailWord_5584755).sum := by decide
  have hdescent : baseEnd_5584755 < baseStart_5584755 := by decide
  rcases family_descends (prefixWord ++ tailWord_5584755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5584785 : List Nat := [1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 6]
def baseStart_5584785 : Nat := 118140960795 + 5584785 * 2 ^ 59
def prefixEnd_5584785 : Nat := 4983230072969 + 3 ^ 40 * 5584785 * 2
def baseEnd_5584785 : Nat := 2867679057020037236703547

theorem tailTrace_5584785 : CollatzResearch.WordTrace tailWord_5584785 prefixEnd_5584785 2867679057020037236703547 := by
  unfold tailWord_5584785
  simp only [CollatzResearch.WordTrace]
  refine ⟨203693843072285225186787809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135795895381523483457858539 203693843072285225186787809)
  ·
    refine ⟨152770382304213918890090857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203693843072285225186787809 152770382304213918890090857)
    ·
      refine ⟨114577786728160439167568143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152770382304213918890090857 114577786728160439167568143)
      ·
        refine ⟨171866680092240658751352215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114577786728160439167568143 171866680092240658751352215)
        ·
          refine ⟨257800020138360988127028323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171866680092240658751352215 257800020138360988127028323)
          ·
            refine ⟨386700030207541482190542485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 257800020138360988127028323 386700030207541482190542485)
            ·
              refine ⟨18126563915978506977681679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 386700030207541482190542485 18126563915978506977681679)
              ·
                refine ⟨27189845873967760466522519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18126563915978506977681679 27189845873967760466522519)
                ·
                  refine ⟨40784768810951640699783779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27189845873967760466522519 40784768810951640699783779)
                  ·
                    refine ⟨61177153216427461049675669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40784768810951640699783779 61177153216427461049675669)
                    ·
                      refine ⟨2867679057020037236703547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61177153216427461049675669 2867679057020037236703547)
                      ·
                        rfl

theorem cell23_5584785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 6].length) (baseStart_5584785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5584785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5584785 prefixEnd_5584785 := by exact prefixLift 5584785
  have htrace : WordTrace (prefixWord ++ tailWord_5584785) baseStart_5584785 baseEnd_5584785 := by
    simpa [prefixWord, tailWord_5584785, baseEnd_5584785] using wordTrace_append hprefix tailTrace_5584785
  have hstable : (prefixWord ++ tailWord_5584785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5584785).length < 2 ^ (prefixWord ++ tailWord_5584785).sum := by decide
  have hdescent : baseEnd_5584785 < baseStart_5584785 := by decide
  rcases family_descends (prefixWord ++ tailWord_5584785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5584786 : List Nat := [3, 2, 3, 2, 1, 3, 1, 2, 1, 5]
def baseStart_5584786 : Nat := 118140960795 + 5584786 * 2 ^ 59
def prefixEnd_5584786 : Nat := 4983230072969 + 3 ^ 40 * 5584786 * 2
def baseEnd_5584786 : Nat := 955893190166897244263681

theorem tailTrace_5584786 : CollatzResearch.WordTrace tailWord_5584786 prefixEnd_5584786 955893190166897244263681 := by
  unfold tailWord_5584786
  simp only [CollatzResearch.WordTrace]
  refine ⟨50923469886320400589393553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135795919696854401571716141 50923469886320400589393553)
  ·
    refine ⟨38192602414740300442045165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50923469886320400589393553 38192602414740300442045165)
    ·
      refine ⟨14322225905527612665766937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38192602414740300442045165 14322225905527612665766937)
      ·
        refine ⟨10741669429145709499325203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14322225905527612665766937 10741669429145709499325203)
        ·
          refine ⟨16112504143718564248987805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10741669429145709499325203 16112504143718564248987805)
          ·
            refine ⟨6042189053894461593370427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16112504143718564248987805 6042189053894461593370427)
            ·
              refine ⟨9063283580841692390055641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6042189053894461593370427 9063283580841692390055641)
              ·
                refine ⟨6797462685631269292541731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9063283580841692390055641 6797462685631269292541731)
                ·
                  refine ⟨10196194028446903938812597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6797462685631269292541731 10196194028446903938812597)
                  ·
                    refine ⟨955893190166897244263681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10196194028446903938812597 955893190166897244263681)
                    ·
                      rfl

theorem cell23_5584786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 2, 1, 5].length) (baseStart_5584786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5584786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5584786 prefixEnd_5584786 := by exact prefixLift 5584786
  have htrace : WordTrace (prefixWord ++ tailWord_5584786) baseStart_5584786 baseEnd_5584786 := by
    simpa [prefixWord, tailWord_5584786, baseEnd_5584786] using wordTrace_append hprefix tailTrace_5584786
  have hstable : (prefixWord ++ tailWord_5584786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5584786).length < 2 ^ (prefixWord ++ tailWord_5584786).sum := by decide
  have hdescent : baseEnd_5584786 < baseStart_5584786 := by decide
  rcases family_descends (prefixWord ++ tailWord_5584786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5584789 : List Nat := [1, 3, 2, 1, 1, 3, 2, 1, 5, 2, 2]
def baseStart_5584789 : Nat := 118140960795 + 5584789 * 2 ^ 59
def prefixEnd_5584789 : Nat := 4983230072969 + 3 ^ 40 * 5584789 * 2
def baseEnd_5584789 : Nat := 2867681110942655221053529

theorem tailTrace_5584789 : CollatzResearch.WordTrace tailWord_5584789 prefixEnd_5584789 2867681110942655221053529 := by
  unfold tailWord_5584789
  simp only [CollatzResearch.WordTrace]
  refine ⟨203693988964270733869933421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135795992642847155913288947 203693988964270733869933421)
  ·
    refine ⟨76385245861601525201225033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 203693988964270733869933421 76385245861601525201225033)
    ·
      refine ⟨57288934396201143900918775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76385245861601525201225033 57288934396201143900918775)
      ·
        refine ⟨85933401594301715851378163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57288934396201143900918775 85933401594301715851378163)
        ·
          refine ⟨128900102391452573777067245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85933401594301715851378163 128900102391452573777067245)
          ·
            refine ⟨48337538396794715166400217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 128900102391452573777067245 48337538396794715166400217)
            ·
              refine ⟨36253153797596036374800163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48337538396794715166400217 36253153797596036374800163)
              ·
                refine ⟨54379730696394054562200245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36253153797596036374800163 54379730696394054562200245)
                ·
                  refine ⟨5098099752786942615206273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54379730696394054562200245 5098099752786942615206273)
                  ·
                    refine ⟨3823574814590206961404705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5098099752786942615206273 3823574814590206961404705)
                    ·
                      refine ⟨2867681110942655221053529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3823574814590206961404705 2867681110942655221053529)
                      ·
                        rfl

theorem cell23_5584789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 1, 5, 2, 2].length) (baseStart_5584789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5584789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5584789 prefixEnd_5584789 := by exact prefixLift 5584789
  have htrace : WordTrace (prefixWord ++ tailWord_5584789) baseStart_5584789 baseEnd_5584789 := by
    simpa [prefixWord, tailWord_5584789, baseEnd_5584789] using wordTrace_append hprefix tailTrace_5584789
  have hstable : (prefixWord ++ tailWord_5584789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5584789).length < 2 ^ (prefixWord ++ tailWord_5584789).sum := by decide
  have hdescent : baseEnd_5584789 < baseStart_5584789 := by decide
  rcases family_descends (prefixWord ++ tailWord_5584789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5584825 : List Nat := [1, 2, 1, 4, 2, 1, 1, 1, 1, 9]
def baseStart_5584825 : Nat := 118140960795 + 5584825 * 2 ^ 59
def prefixEnd_5584825 : Nat := 4983230072969 + 3 ^ 40 * 5584825 * 2
def baseEnd_5584825 : Nat := 955899865415405693401121

theorem tailTrace_5584825 : CollatzResearch.WordTrace tailWord_5584825 prefixEnd_5584825 955899865415405693401121 := by
  unfold tailWord_5584825
  simp only [CollatzResearch.WordTrace]
  refine ⟨203695301992140312018243929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135796867994760208012162619 203695301992140312018243929)
  ·
    refine ⟨152771476494105234013682947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203695301992140312018243929 152771476494105234013682947)
    ·
      refine ⟨229157214741157851020524421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152771476494105234013682947 229157214741157851020524421)
      ·
        refine ⟨42966977763967097066348329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 229157214741157851020524421 42966977763967097066348329)
        ·
          refine ⟨32225233322975322799761247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42966977763967097066348329 32225233322975322799761247)
          ·
            refine ⟨48337849984462984199641871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32225233322975322799761247 48337849984462984199641871)
            ·
              refine ⟨72506774976694476299462807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48337849984462984199641871 72506774976694476299462807)
              ·
                refine ⟨108760162465041714449194211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72506774976694476299462807 108760162465041714449194211)
                ·
                  refine ⟨163140243697562571673791317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 108760162465041714449194211 163140243697562571673791317)
                  ·
                    refine ⟨955899865415405693401121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 163140243697562571673791317 955899865415405693401121)
                    ·
                      rfl

theorem cell23_5584825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 9].length) (baseStart_5584825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5584825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5584825 prefixEnd_5584825 := by exact prefixLift 5584825
  have htrace : WordTrace (prefixWord ++ tailWord_5584825) baseStart_5584825 baseEnd_5584825 := by
    simpa [prefixWord, tailWord_5584825, baseEnd_5584825] using wordTrace_append hprefix tailTrace_5584825
  have hstable : (prefixWord ++ tailWord_5584825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5584825).length < 2 ^ (prefixWord ++ tailWord_5584825).sum := by decide
  have hdescent : baseEnd_5584825 < baseStart_5584825 := by decide
  rcases family_descends (prefixWord ++ tailWord_5584825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5584852 : List Nat := [2, 4, 1, 2, 1, 1, 2, 1, 2, 2, 5]
def baseStart_5584852 : Nat := 118140960795 + 5584852 * 2 ^ 59
def prefixEnd_5584852 : Nat := 4983230072969 + 3 ^ 40 * 5584852 * 2
def baseEnd_5584852 : Nat := 2867713460223888474565739

theorem tailTrace_5584852 : CollatzResearch.WordTrace tailWord_5584852 prefixEnd_5584852 2867713460223888474565739 := by
  unfold tailWord_5584852
  simp only [CollatzResearch.WordTrace]
  refine ⟨101848143381521247814738405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135797524508694997086317873 101848143381521247814738405)
  ·
    refine ⟨19096526884035233965263451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101848143381521247814738405 19096526884035233965263451)
    ·
      refine ⟨28644790326052850947895177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19096526884035233965263451 28644790326052850947895177)
      ·
        refine ⟨21483592744539638210921383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28644790326052850947895177 21483592744539638210921383)
        ·
          refine ⟨32225389116809457316382075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21483592744539638210921383 32225389116809457316382075)
          ·
            refine ⟨48338083675214185974573113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32225389116809457316382075 48338083675214185974573113)
            ·
              refine ⟨36253562756410639480929835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48338083675214185974573113 36253562756410639480929835)
              ·
                refine ⟨54380344134615959221394753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36253562756410639480929835 54380344134615959221394753)
                ·
                  refine ⟨40785258100961969416046065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54380344134615959221394753 40785258100961969416046065)
                  ·
                    refine ⟨30588943575721477062034549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40785258100961969416046065 30588943575721477062034549)
                    ·
                      refine ⟨2867713460223888474565739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30588943575721477062034549 2867713460223888474565739)
                      ·
                        rfl

theorem cell23_5584852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_5584852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5584852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5584852 prefixEnd_5584852 := by exact prefixLift 5584852
  have htrace : WordTrace (prefixWord ++ tailWord_5584852) baseStart_5584852 baseEnd_5584852 := by
    simpa [prefixWord, tailWord_5584852, baseEnd_5584852] using wordTrace_append hprefix tailTrace_5584852
  have hstable : (prefixWord ++ tailWord_5584852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5584852).length < 2 ^ (prefixWord ++ tailWord_5584852).sum := by decide
  have hdescent : baseEnd_5584852 < baseStart_5584852 := by decide
  rcases family_descends (prefixWord ++ tailWord_5584852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5584855 : List Nat := [1, 1, 3, 2, 1, 1, 3, 2, 1, 8]
def baseStart_5584855 : Nat := 118140960795 + 5584855 * 2 ^ 59
def prefixEnd_5584855 : Nat := 4983230072969 + 3 ^ 40 * 5584855 * 2
def baseEnd_5584855 : Nat := 955905000221950654276075

theorem tailTrace_5584855 : CollatzResearch.WordTrace tailWord_5584855 prefixEnd_5584855 955905000221950654276075 := by
  unfold tailWord_5584855
  simp only [CollatzResearch.WordTrace]
  refine ⟨203696396182031627141836019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135797597454687751427890679 203696396182031627141836019)
  ·
    refine ⟨305544594273047440712754029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203696396182031627141836019 305544594273047440712754029)
    ·
      refine ⟨114579222852392790267282761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 305544594273047440712754029 114579222852392790267282761)
      ·
        refine ⟨85934417139294592700462071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114579222852392790267282761 85934417139294592700462071)
        ·
          refine ⟨128901625708941889050693107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85934417139294592700462071 128901625708941889050693107)
          ·
            refine ⟨193352438563412833576039661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128901625708941889050693107 193352438563412833576039661)
            ·
              refine ⟨72507164461279812591014873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 193352438563412833576039661 72507164461279812591014873)
              ·
                refine ⟨54380373345959859443261155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72507164461279812591014873 54380373345959859443261155)
                ·
                  refine ⟨81570560018939789164891733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54380373345959859443261155 81570560018939789164891733)
                  ·
                    refine ⟨955905000221950654276075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 81570560018939789164891733 955905000221950654276075)
                    ·
                      rfl

theorem cell23_5584855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 2, 1, 8].length) (baseStart_5584855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5584855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5584855 prefixEnd_5584855 := by exact prefixLift 5584855
  have htrace : WordTrace (prefixWord ++ tailWord_5584855) baseStart_5584855 baseEnd_5584855 := by
    simpa [prefixWord, tailWord_5584855, baseEnd_5584855] using wordTrace_append hprefix tailTrace_5584855
  have hstable : (prefixWord ++ tailWord_5584855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5584855).length < 2 ^ (prefixWord ++ tailWord_5584855).sum := by decide
  have hdescent : baseEnd_5584855 < baseStart_5584855 := by decide
  rcases family_descends (prefixWord ++ tailWord_5584855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5584860 : List Nat := [2, 2, 6, 1, 1, 1, 1, 3, 1, 2, 3]
def baseStart_5584860 : Nat := 118140960795 + 5584860 * 2 ^ 59
def prefixEnd_5584860 : Nat := 4983230072969 + 3 ^ 40 * 5584860 * 2
def baseEnd_5584860 : Nat := 2867717568069124443265703

theorem tailTrace_5584860 : CollatzResearch.WordTrace tailWord_5584860 prefixEnd_5584860 2867717568069124443265703 := by
  unfold tailWord_5584860
  simp only [CollatzResearch.WordTrace]
  refine ⟨101848289273506756497884017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135797719031342341997178689 101848289273506756497884017)
  ·
    refine ⟨76386216955130067373413013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101848289273506756497884017 76386216955130067373413013)
    ·
      refine ⟨3580603919771721908128735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 76386216955130067373413013 3580603919771721908128735)
      ·
        refine ⟨5370905879657582862193103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3580603919771721908128735 5370905879657582862193103)
        ·
          refine ⟨8056358819486374293289655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5370905879657582862193103 8056358819486374293289655)
          ·
            refine ⟨12084538229229561439934483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8056358819486374293289655 12084538229229561439934483)
            ·
              refine ⟨18126807343844342159901725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12084538229229561439934483 18126807343844342159901725)
              ·
                refine ⟨6797552753941628309963147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18126807343844342159901725 6797552753941628309963147)
                ·
                  refine ⟨10196329130912442464944721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6797552753941628309963147 10196329130912442464944721)
                  ·
                    refine ⟨7647246848184331848708541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10196329130912442464944721 7647246848184331848708541)
                    ·
                      refine ⟨2867717568069124443265703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7647246848184331848708541 2867717568069124443265703)
                      ·
                        rfl

theorem cell23_5584860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_5584860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5584860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5584860 prefixEnd_5584860 := by exact prefixLift 5584860
  have htrace : WordTrace (prefixWord ++ tailWord_5584860) baseStart_5584860 baseEnd_5584860 := by
    simpa [prefixWord, tailWord_5584860, baseEnd_5584860] using wordTrace_append hprefix tailTrace_5584860
  have hstable : (prefixWord ++ tailWord_5584860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5584860).length < 2 ^ (prefixWord ++ tailWord_5584860).sum := by decide
  have hdescent : baseEnd_5584860 < baseStart_5584860 := by decide
  rcases family_descends (prefixWord ++ tailWord_5584860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5584892 : List Nat := [2, 2, 2, 1, 2, 2, 1, 3, 2, 2, 4]
def baseStart_5584892 : Nat := 118140960795 + 5584892 * 2 ^ 59
def prefixEnd_5584892 : Nat := 4983230072969 + 3 ^ 40 * 5584892 * 2
def baseEnd_5584892 : Nat := 2867733999450068318065555

theorem tailTrace_5584892 : CollatzResearch.WordTrace tailWord_5584892 prefixEnd_5584892 2867733999450068318065555 := by
  unfold tailWord_5584892
  simp only [CollatzResearch.WordTrace]
  refine ⟨101848872841448791230466465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135798497121931721640621953 101848872841448791230466465)
  ·
    refine ⟨76386654631086593422849849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101848872841448791230466465 76386654631086593422849849)
    ·
      refine ⟨57289990973314945067137387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76386654631086593422849849 57289990973314945067137387)
      ·
        refine ⟨85934986459972417600706081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57289990973314945067137387 85934986459972417600706081)
        ·
          refine ⟨64451239844979313200529561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85934986459972417600706081 64451239844979313200529561)
          ·
            refine ⟨48338429883734484900397171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64451239844979313200529561 48338429883734484900397171)
            ·
              refine ⟨72507644825601727350595757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48338429883734484900397171 72507644825601727350595757)
              ·
                refine ⟨27190366809600647756473409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72507644825601727350595757 27190366809600647756473409)
                ·
                  refine ⟨20392775107200485817355057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27190366809600647756473409 20392775107200485817355057)
                  ·
                    refine ⟨15294581330400364363016293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20392775107200485817355057 15294581330400364363016293)
                    ·
                      refine ⟨2867733999450068318065555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15294581330400364363016293 2867733999450068318065555)
                      ·
                        rfl

theorem cell23_5584892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 3, 2, 2, 4].length) (baseStart_5584892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5584892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5584892 prefixEnd_5584892 := by exact prefixLift 5584892
  have htrace : WordTrace (prefixWord ++ tailWord_5584892) baseStart_5584892 baseEnd_5584892 := by
    simpa [prefixWord, tailWord_5584892, baseEnd_5584892] using wordTrace_append hprefix tailTrace_5584892
  have hstable : (prefixWord ++ tailWord_5584892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5584892).length < 2 ^ (prefixWord ++ tailWord_5584892).sum := by decide
  have hdescent : baseEnd_5584892 < baseStart_5584892 := by decide
  rcases family_descends (prefixWord ++ tailWord_5584892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5584895 : List Nat := [1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 9]
def baseStart_5584895 : Nat := 118140960795 + 5584895 * 2 ^ 59
def prefixEnd_5584895 : Nat := 4983230072969 + 3 ^ 40 * 5584895 * 2
def baseEnd_5584895 : Nat := 2867735539892031806328041

theorem tailTrace_5584895 : CollatzResearch.WordTrace tailWord_5584895 prefixEnd_5584895 2867735539892031806328041 := by
  unfold tailWord_5584895
  simp only [CollatzResearch.WordTrace]
  refine ⟨203697855101886713973292139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135798570067924475982194759 203697855101886713973292139)
  ·
    refine ⟨305546782652830070959938209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203697855101886713973292139 305546782652830070959938209)
    ·
      refine ⟨229160086989622553219953657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 305546782652830070959938209 229160086989622553219953657)
      ·
        refine ⟨171870065242216914914965243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 229160086989622553219953657 171870065242216914914965243)
        ·
          refine ⟨257805097863325372372447865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171870065242216914914965243 257805097863325372372447865)
          ·
            refine ⟨193353823397494029279335899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 257805097863325372372447865 193353823397494029279335899)
            ·
              refine ⟨290030735096241043919003849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 193353823397494029279335899 290030735096241043919003849)
              ·
                refine ⟨217523051322180782939252887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 290030735096241043919003849 217523051322180782939252887)
                ·
                  refine ⟨326284576983271174408879331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 217523051322180782939252887 326284576983271174408879331)
                  ·
                    refine ⟨489426865474906761613318997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 326284576983271174408879331 489426865474906761613318997)
                    ·
                      refine ⟨2867735539892031806328041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 489426865474906761613318997 2867735539892031806328041)
                      ·
                        rfl

theorem cell23_5584895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 9].length) (baseStart_5584895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5584895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5584895 prefixEnd_5584895 := by exact prefixLift 5584895
  have htrace : WordTrace (prefixWord ++ tailWord_5584895) baseStart_5584895 baseEnd_5584895 := by
    simpa [prefixWord, tailWord_5584895, baseEnd_5584895] using wordTrace_append hprefix tailTrace_5584895
  have hstable : (prefixWord ++ tailWord_5584895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5584895).length < 2 ^ (prefixWord ++ tailWord_5584895).sum := by decide
  have hdescent : baseEnd_5584895 < baseStart_5584895 := by decide
  rcases family_descends (prefixWord ++ tailWord_5584895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5584900 : List Nat := [2, 3, 2, 4, 1, 1, 2, 2, 1, 3, 2]
def baseStart_5584900 : Nat := 118140960795 + 5584900 * 2 ^ 59
def prefixEnd_5584900 : Nat := 4983230072969 + 3 ^ 40 * 5584900 * 2
def baseEnd_5584900 : Nat := 2867738107295304286765519

theorem tailTrace_5584900 : CollatzResearch.WordTrace tailWord_5584900 prefixEnd_5584900 2867738107295304286765519 := by
  unfold tailWord_5584900
  simp only [CollatzResearch.WordTrace]
  refine ⟨101849018733434299913612077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135798691644579066551482769 101849018733434299913612077)
  ·
    refine ⟨38193382025037862467604529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101849018733434299913612077 38193382025037862467604529)
    ·
      refine ⟨28645036518778396850703397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38193382025037862467604529 28645036518778396850703397)
      ·
        refine ⟨5370944347270949409506887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28645036518778396850703397 5370944347270949409506887)
        ·
          refine ⟨8056416520906424114260331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5370944347270949409506887 8056416520906424114260331)
          ·
            refine ⟨12084624781359636171390497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8056416520906424114260331 12084624781359636171390497)
            ·
              refine ⟨9063468586019727128542873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12084624781359636171390497 9063468586019727128542873)
              ·
                refine ⟨6797601439514795346407155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9063468586019727128542873 6797601439514795346407155)
                ·
                  refine ⟨10196402159272193019610733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6797601439514795346407155 10196402159272193019610733)
                  ·
                    refine ⟨3823650809727072382354025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10196402159272193019610733 3823650809727072382354025)
                    ·
                      refine ⟨2867738107295304286765519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3823650809727072382354025 2867738107295304286765519)
                      ·
                        rfl

theorem cell23_5584900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_5584900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5584900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5584900 prefixEnd_5584900 := by exact prefixLift 5584900
  have htrace : WordTrace (prefixWord ++ tailWord_5584900) baseStart_5584900 baseEnd_5584900 := by
    simpa [prefixWord, tailWord_5584900, baseEnd_5584900] using wordTrace_append hprefix tailTrace_5584900
  have hstable : (prefixWord ++ tailWord_5584900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5584900).length < 2 ^ (prefixWord ++ tailWord_5584900).sum := by decide
  have hdescent : baseEnd_5584900 < baseStart_5584900 := by decide
  rcases family_descends (prefixWord ++ tailWord_5584900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5584969 : List Nat := [1, 2, 1, 1, 2, 2, 6, 1, 2, 1, 4]
def baseStart_5584969 : Nat := 118140960795 + 5584969 * 2 ^ 59
def prefixEnd_5584969 : Nat := 4983230072969 + 3 ^ 40 * 5584969 * 2
def baseEnd_5584969 : Nat := 2867773537460464516802701

theorem tailTrace_5584969 : CollatzResearch.WordTrace tailWord_5584969 prefixEnd_5584969 2867773537460464516802701 := by
  unfold tailWord_5584969
  simp only [CollatzResearch.WordTrace]
  refine ⟨203700554103618624611485961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135800369402412416407657307 203700554103618624611485961)
  ·
    refine ⟨152775415577713968458614471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203700554103618624611485961 152775415577713968458614471)
    ·
      refine ⟨229163123366570952687921707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152775415577713968458614471 229163123366570952687921707)
      ·
        refine ⟨343744685049856429031882561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229163123366570952687921707 343744685049856429031882561)
        ·
          refine ⟨257808513787392321773911921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 343744685049856429031882561 257808513787392321773911921)
          ·
            refine ⟨193356385340544241330433941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 257808513787392321773911921 193356385340544241330433941)
            ·
              refine ⟨9063580562838011312364091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 193356385340544241330433941 9063580562838011312364091)
              ·
                refine ⟨13595370844257016968546137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9063580562838011312364091 13595370844257016968546137)
                ·
                  refine ⟨10196528133192762726409603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13595370844257016968546137 10196528133192762726409603)
                  ·
                    refine ⟨15294792199789144089614405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10196528133192762726409603 15294792199789144089614405)
                    ·
                      refine ⟨2867773537460464516802701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15294792199789144089614405 2867773537460464516802701)
                      ·
                        rfl

theorem cell23_5584969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 1, 2, 1, 4].length) (baseStart_5584969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5584969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5584969 prefixEnd_5584969 := by exact prefixLift 5584969
  have htrace : WordTrace (prefixWord ++ tailWord_5584969) baseStart_5584969 baseEnd_5584969 := by
    simpa [prefixWord, tailWord_5584969, baseEnd_5584969] using wordTrace_append hprefix tailTrace_5584969
  have hstable : (prefixWord ++ tailWord_5584969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5584969).length < 2 ^ (prefixWord ++ tailWord_5584969).sum := by decide
  have hdescent : baseEnd_5584969 < baseStart_5584969 := by decide
  rcases family_descends (prefixWord ++ tailWord_5584969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5585053 : List Nat := [1, 4, 2, 1, 1, 4, 2, 1, 3, 1, 3]
def baseStart_5585053 : Nat := 118140960795 + 5585053 * 2 ^ 59
def prefixEnd_5585053 : Nat := 4983230072969 + 3 ^ 40 * 5585053 * 2
def baseEnd_5585053 : Nat := 2867816669835442188152315

theorem tailTrace_5585053 : CollatzResearch.WordTrace tailWord_5585053 prefixEnd_5585053 2867816669835442188152315 := by
  unfold tailWord_5585053
  simp only [CollatzResearch.WordTrace]
  refine ⟨203703617835314306957543813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135802411890209537971695875 203703617835314306957543813)
  ·
    refine ⟨38194428344121432554539465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 203703617835314306957543813 38194428344121432554539465)
    ·
      refine ⟨28645821258091074415904599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38194428344121432554539465 28645821258091074415904599)
      ·
        refine ⟨42968731887136611623856899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28645821258091074415904599 42968731887136611623856899)
        ·
          refine ⟨64453097830704917435785349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42968731887136611623856899 64453097830704917435785349)
          ·
            refine ⟨12084955843257172019209753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64453097830704917435785349 12084955843257172019209753)
            ·
              refine ⟨9063716882442879014407315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12084955843257172019209753 9063716882442879014407315)
              ·
                refine ⟨13595575323664318521610973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9063716882442879014407315 13595575323664318521610973)
                ·
                  refine ⟨5098340746374119445604115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13595575323664318521610973 5098340746374119445604115)
                  ·
                    refine ⟨7647511119561179168406173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5098340746374119445604115 7647511119561179168406173)
                    ·
                      refine ⟨2867816669835442188152315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7647511119561179168406173 2867816669835442188152315)
                      ·
                        rfl

theorem cell23_5585053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 1, 3, 1, 3].length) (baseStart_5585053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5585053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5585053 prefixEnd_5585053 := by exact prefixLift 5585053
  have htrace : WordTrace (prefixWord ++ tailWord_5585053) baseStart_5585053 baseEnd_5585053 := by
    simpa [prefixWord, tailWord_5585053, baseEnd_5585053] using wordTrace_append hprefix tailTrace_5585053
  have hstable : (prefixWord ++ tailWord_5585053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5585053).length < 2 ^ (prefixWord ++ tailWord_5585053).sum := by decide
  have hdescent : baseEnd_5585053 < baseStart_5585053 := by decide
  rcases family_descends (prefixWord ++ tailWord_5585053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5585073 : List Nat := [1, 2, 2, 5, 2, 1, 2, 2, 1, 5]
def baseStart_5585073 : Nat := 118140960795 + 5585073 * 2 ^ 59
def prefixEnd_5585073 : Nat := 4983230072969 + 3 ^ 40 * 5585073 * 2
def baseEnd_5585073 : Nat := 955942313149510703300741

theorem tailTrace_5585073 : CollatzResearch.WordTrace tailWord_5585073 prefixEnd_5585073 955942313149510703300741 := by
  unfold tailWord_5585073
  simp only [CollatzResearch.WordTrace]
  refine ⟨203704347295241850373271873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135802898196827900248847915 203704347295241850373271873)
  ·
    refine ⟨152778260471431387779953905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203704347295241850373271873 152778260471431387779953905)
    ·
      refine ⟨114583695353573540834965429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152778260471431387779953905 114583695353573540834965429)
      ·
        refine ⟨10742221439397519453278009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 114583695353573540834965429 10742221439397519453278009)
        ·
          refine ⟨8056666079548139589958507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10742221439397519453278009 8056666079548139589958507)
          ·
            refine ⟨12084999119322209384937761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8056666079548139589958507 12084999119322209384937761)
            ·
              refine ⟨9063749339491657038703321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12084999119322209384937761 9063749339491657038703321)
              ·
                refine ⟨6797812004618742779027491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9063749339491657038703321 6797812004618742779027491)
                ·
                  refine ⟨10196718006928114168541237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6797812004618742779027491 10196718006928114168541237)
                  ·
                    refine ⟨955942313149510703300741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10196718006928114168541237 955942313149510703300741)
                    ·
                      rfl

theorem cell23_5585073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 2, 1, 5].length) (baseStart_5585073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5585073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5585073 prefixEnd_5585073 := by exact prefixLift 5585073
  have htrace : WordTrace (prefixWord ++ tailWord_5585073) baseStart_5585073 baseEnd_5585073 := by
    simpa [prefixWord, tailWord_5585073, baseEnd_5585073] using wordTrace_append hprefix tailTrace_5585073
  have hstable : (prefixWord ++ tailWord_5585073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5585073).length < 2 ^ (prefixWord ++ tailWord_5585073).sum := by decide
  have hdescent : baseEnd_5585073 < baseStart_5585073 := by decide
  rcases family_descends (prefixWord ++ tailWord_5585073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5585090 : List Nat := [3, 5, 1, 1, 1, 1, 2, 3, 1, 5]
def baseStart_5585090 : Nat := 118140960795 + 5585090 * 2 ^ 59
def prefixEnd_5585090 : Nat := 4983230072969 + 3 ^ 40 * 5585090 * 2
def baseEnd_5585090 : Nat := 955945222873219514463215

theorem tailTrace_5585090 : CollatzResearch.WordTrace tailWord_5585090 prefixEnd_5585090 955945222873219514463215 := by
  unfold tailWord_5585090
  simp only [CollatzResearch.WordTrace]
  refine ⟨50926241834045065569160181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135803311557453508184427149 50926241834045065569160181)
  ·
    refine ⟨4774335171941724897108767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50926241834045065569160181 4774335171941724897108767)
    ·
      refine ⟨7161502757912587345663151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4774335171941724897108767 7161502757912587345663151)
      ·
        refine ⟨10742254136868881018494727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7161502757912587345663151 10742254136868881018494727)
        ·
          refine ⟨16113381205303321527742091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10742254136868881018494727 16113381205303321527742091)
          ·
            refine ⟨24170071807954982291613137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16113381205303321527742091 24170071807954982291613137)
            ·
              refine ⟨18127553855966236718709853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24170071807954982291613137 18127553855966236718709853)
              ·
                refine ⟨6797832695987338769516195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18127553855966236718709853 6797832695987338769516195)
                ·
                  refine ⟨10196749043981008154274293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6797832695987338769516195 10196749043981008154274293)
                  ·
                    refine ⟨955945222873219514463215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10196749043981008154274293 955945222873219514463215)
                    ·
                      rfl

theorem cell23_5585090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_5585090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5585090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5585090 prefixEnd_5585090 := by exact prefixLift 5585090
  have htrace : WordTrace (prefixWord ++ tailWord_5585090) baseStart_5585090 baseEnd_5585090 := by
    simpa [prefixWord, tailWord_5585090, baseEnd_5585090] using wordTrace_append hprefix tailTrace_5585090
  have hstable : (prefixWord ++ tailWord_5585090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5585090).length < 2 ^ (prefixWord ++ tailWord_5585090).sum := by decide
  have hdescent : baseEnd_5585090 < baseStart_5585090 := by decide
  rcases family_descends (prefixWord ++ tailWord_5585090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5585149 : List Nat := [1, 4, 1, 1, 1, 1, 1, 2, 4, 3, 4]
def baseStart_5585149 : Nat := 118140960795 + 5585149 * 2 ^ 59
def prefixEnd_5585149 : Nat := 4983230072969 + 3 ^ 40 * 5585149 * 2
def baseEnd_5585149 : Nat := 2867865963978273812551873

theorem tailTrace_5585149 : CollatzResearch.WordTrace tailWord_5585149 prefixEnd_5585149 2867865963978273812551873 := by
  unfold tailWord_5585149
  simp only [CollatzResearch.WordTrace]
  refine ⟨203707119242966515353038501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135804746161977676902025667 203707119242966515353038501)
  ·
    refine ⟨38195084858056221628694719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 203707119242966515353038501 38195084858056221628694719)
    ·
      refine ⟨57292627287084332443042079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38195084858056221628694719 57292627287084332443042079)
      ·
        refine ⟨85938940930626498664563119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57292627287084332443042079 85938940930626498664563119)
        ·
          refine ⟨128908411395939747996844679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85938940930626498664563119 128908411395939747996844679)
          ·
            refine ⟨193362617093909621995267019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128908411395939747996844679 193362617093909621995267019)
            ·
              refine ⟨290043925640864432992900529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 193362617093909621995267019 290043925640864432992900529)
              ·
                refine ⟨217532944230648324744675397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 290043925640864432992900529 217532944230648324744675397)
                ·
                  refine ⟨40787427043246560889626637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 217532944230648324744675397 40787427043246560889626637)
                  ·
                    refine ⟨15295285141217460333609989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40787427043246560889626637 15295285141217460333609989)
                    ·
                      refine ⟨2867865963978273812551873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15295285141217460333609989 2867865963978273812551873)
                      ·
                        rfl

theorem cell23_5585149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 4, 3, 4].length) (baseStart_5585149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5585149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5585149 prefixEnd_5585149 := by exact prefixLift 5585149
  have htrace : WordTrace (prefixWord ++ tailWord_5585149) baseStart_5585149 baseEnd_5585149 := by
    simpa [prefixWord, tailWord_5585149, baseEnd_5585149] using wordTrace_append hprefix tailTrace_5585149
  have hstable : (prefixWord ++ tailWord_5585149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5585149).length < 2 ^ (prefixWord ++ tailWord_5585149).sum := by decide
  have hdescent : baseEnd_5585149 < baseStart_5585149 := by decide
  rcases family_descends (prefixWord ++ tailWord_5585149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5585160 : List Nat := [2, 1, 3, 2, 3, 2, 2, 2, 2, 1, 3]
def baseStart_5585160 : Nat := 118140960795 + 5585160 * 2 ^ 59
def prefixEnd_5585160 : Nat := 4983230072969 + 3 ^ 40 * 5585160 * 2
def baseEnd_5585160 : Nat := 2867871612265473269514323

theorem tailTrace_5585160 : CollatzResearch.WordTrace tailWord_5585160 prefixEnd_5585160 2867871612265473269514323 := by
  unfold tailWord_5585160
  simp only [CollatzResearch.WordTrace]
  refine ⟨101853760222963332115844467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135805013630617776154459289 101853760222963332115844467)
  ·
    refine ⟨152780640334444998173766701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101853760222963332115844467 152780640334444998173766701)
    ·
      refine ⟨57292740125416874315162513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152780640334444998173766701 57292740125416874315162513)
      ·
        refine ⟨42969555094062655736371885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57292740125416874315162513 42969555094062655736371885)
        ·
          refine ⟨16113583160273495901139457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42969555094062655736371885 16113583160273495901139457)
          ·
            refine ⟨12085187370205121925854593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16113583160273495901139457 12085187370205121925854593)
            ·
              refine ⟨9063890527653841444390945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12085187370205121925854593 9063890527653841444390945)
              ·
                refine ⟨6797917895740381083293209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9063890527653841444390945 6797917895740381083293209)
                ·
                  refine ⟨5098438421805285812469907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6797917895740381083293209 5098438421805285812469907)
                  ·
                    refine ⟨7647657632707928718704861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5098438421805285812469907 7647657632707928718704861)
                    ·
                      refine ⟨2867871612265473269514323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7647657632707928718704861 2867871612265473269514323)
                      ·
                        rfl

theorem cell23_5585160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 2, 2, 1, 3].length) (baseStart_5585160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5585160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5585160 prefixEnd_5585160 := by exact prefixLift 5585160
  have htrace : WordTrace (prefixWord ++ tailWord_5585160) baseStart_5585160 baseEnd_5585160 := by
    simpa [prefixWord, tailWord_5585160, baseEnd_5585160] using wordTrace_append hprefix tailTrace_5585160
  have hstable : (prefixWord ++ tailWord_5585160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5585160).length < 2 ^ (prefixWord ++ tailWord_5585160).sum := by decide
  have hdescent : baseEnd_5585160 < baseStart_5585160 := by decide
  rcases family_descends (prefixWord ++ tailWord_5585160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5585179 : List Nat := [1, 1, 1, 1, 1, 1, 7, 1, 1, 4, 4]
def baseStart_5585179 : Nat := 118140960795 + 5585179 * 2 ^ 59
def prefixEnd_5585179 : Nat := 4983230072969 + 3 ^ 40 * 5585179 * 2
def baseEnd_5585179 : Nat := 2867881368397908695176735

theorem tailTrace_5585179 : CollatzResearch.WordTrace tailWord_5585179 prefixEnd_5585179 2867881368397908695176735 := by
  unfold tailWord_5585179
  simp only [CollatzResearch.WordTrace]
  refine ⟨203708213432857830476630591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135805475621905220317753727 203708213432857830476630591)
  ·
    refine ⟨305562320149286745714945887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203708213432857830476630591 305562320149286745714945887)
    ·
      refine ⟨458343480223930118572418831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305562320149286745714945887 458343480223930118572418831)
      ·
        refine ⟨687515220335895177858628247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 458343480223930118572418831 687515220335895177858628247)
        ·
          refine ⟨1031272830503842766787942371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 687515220335895177858628247 1031272830503842766787942371)
          ·
            refine ⟨1546909245755764150181913557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1031272830503842766787942371 1546909245755764150181913557)
            ·
              refine ⟨36255685447400722269888599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1546909245755764150181913557 36255685447400722269888599)
              ·
                refine ⟨54383528171101083404832899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36255685447400722269888599 54383528171101083404832899)
                ·
                  refine ⟨81575292256651625107249349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54383528171101083404832899 81575292256651625107249349)
                  ·
                    refine ⟨15295367298122179707609253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 81575292256651625107249349 15295367298122179707609253)
                    ·
                      refine ⟨2867881368397908695176735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15295367298122179707609253 2867881368397908695176735)
                      ·
                        rfl

theorem cell23_5585179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 1, 1, 4, 4].length) (baseStart_5585179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5585179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5585179 prefixEnd_5585179 := by exact prefixLift 5585179
  have htrace : WordTrace (prefixWord ++ tailWord_5585179) baseStart_5585179 baseEnd_5585179 := by
    simpa [prefixWord, tailWord_5585179, baseEnd_5585179] using wordTrace_append hprefix tailTrace_5585179
  have hstable : (prefixWord ++ tailWord_5585179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5585179).length < 2 ^ (prefixWord ++ tailWord_5585179).sum := by decide
  have hdescent : baseEnd_5585179 < baseStart_5585179 := by decide
  rcases family_descends (prefixWord ++ tailWord_5585179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5585183 : List Nat := [1, 1, 2, 4, 3, 1, 1, 3, 1, 4, 2]
def baseStart_5585183 : Nat := 118140960795 + 5585183 * 2 ^ 59
def prefixEnd_5585183 : Nat := 4983230072969 + 3 ^ 40 * 5585183 * 2
def baseEnd_5585183 : Nat := 2867883422320526679526717

theorem tailTrace_5585183 : CollatzResearch.WordTrace tailWord_5585183 prefixEnd_5585183 2867883422320526679526717 := by
  unfold tailWord_5585183
  simp only [CollatzResearch.WordTrace]
  refine ⟨203708359324843339159776203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135805572883228892773184135 203708359324843339159776203)
  ·
    refine ⟨305562538987265008739664305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203708359324843339159776203 305562538987265008739664305)
    ·
      refine ⟨229171904240448756554748229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 305562538987265008739664305 229171904240448756554748229)
      ·
        refine ⟨42969732045084141854015293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 229171904240448756554748229 42969732045084141854015293)
        ·
          refine ⟨16113649516906553195255735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42969732045084141854015293 16113649516906553195255735)
          ·
            refine ⟨24170474275359829792883603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16113649516906553195255735 24170474275359829792883603)
            ·
              refine ⟨36255711413039744689325405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24170474275359829792883603 36255711413039744689325405)
              ·
                refine ⟨13595891779889904258497027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36255711413039744689325405 13595891779889904258497027)
                ·
                  refine ⟨20393837669834856387745541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13595891779889904258497027 20393837669834856387745541)
                  ·
                    refine ⟨3823844563094035572702289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20393837669834856387745541 3823844563094035572702289)
                    ·
                      refine ⟨2867883422320526679526717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3823844563094035572702289 2867883422320526679526717)
                      ·
                        rfl

theorem cell23_5585183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 3, 1, 4, 2].length) (baseStart_5585183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5585183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5585183 prefixEnd_5585183 := by exact prefixLift 5585183
  have htrace : WordTrace (prefixWord ++ tailWord_5585183) baseStart_5585183 baseEnd_5585183 := by
    simpa [prefixWord, tailWord_5585183, baseEnd_5585183] using wordTrace_append hprefix tailTrace_5585183
  have hstable : (prefixWord ++ tailWord_5585183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5585183).length < 2 ^ (prefixWord ++ tailWord_5585183).sum := by decide
  have hdescent : baseEnd_5585183 < baseStart_5585183 := by decide
  rcases family_descends (prefixWord ++ tailWord_5585183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5585204 : List Nat := [2, 5, 1, 1, 1, 4, 2, 1, 1, 3, 2]
def baseStart_5585204 : Nat := 118140960795 + 5585204 * 2 ^ 59
def prefixEnd_5585204 : Nat := 4983230072969 + 3 ^ 40 * 5585204 * 2
def baseEnd_5585204 : Nat := 2867894205414271097364121

theorem tailTrace_5585204 : CollatzResearch.WordTrace tailWord_5585204 prefixEnd_5585204 2867894205414271097364121 := by
  unfold tailWord_5585204
  simp only [CollatzResearch.WordTrace]
  refine ⟨101854562628883629873145333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135806083505178173164193777 101854562628883629873145333)
  ·
    refine ⟨9548865246457840300607375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 101854562628883629873145333 9548865246457840300607375)
    ·
      refine ⟨14323297869686760450911063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9548865246457840300607375 14323297869686760450911063)
      ·
        refine ⟨21484946804530140676366595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14323297869686760450911063 21484946804530140676366595)
        ·
          refine ⟨32227420206795211014549893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21484946804530140676366595 32227420206795211014549893)
          ·
            refine ⟨6042641288774102065228105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32227420206795211014549893 6042641288774102065228105)
            ·
              refine ⟨4531980966580576548921079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6042641288774102065228105 4531980966580576548921079)
              ·
                refine ⟨6797971449870864823381619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4531980966580576548921079 6797971449870864823381619)
                ·
                  refine ⟨10196957174806297235072429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6797971449870864823381619 10196957174806297235072429)
                  ·
                    refine ⟨3823858940552361463152161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10196957174806297235072429 3823858940552361463152161)
                    ·
                      refine ⟨2867894205414271097364121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3823858940552361463152161 2867894205414271097364121)
                      ·
                        rfl

theorem cell23_5585204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 2, 1, 1, 3, 2].length) (baseStart_5585204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5585204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5585204 prefixEnd_5585204 := by exact prefixLift 5585204
  have htrace : WordTrace (prefixWord ++ tailWord_5585204) baseStart_5585204 baseEnd_5585204 := by
    simpa [prefixWord, tailWord_5585204, baseEnd_5585204] using wordTrace_append hprefix tailTrace_5585204
  have hstable : (prefixWord ++ tailWord_5585204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5585204).length < 2 ^ (prefixWord ++ tailWord_5585204).sum := by decide
  have hdescent : baseEnd_5585204 < baseStart_5585204 := by decide
  rcases family_descends (prefixWord ++ tailWord_5585204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5585217 : List Nat := [1, 2, 5, 2, 2, 1, 1, 1, 4, 2, 2]
def baseStart_5585217 : Nat := 118140960795 + 5585217 * 2 ^ 59
def prefixEnd_5585217 : Nat := 4983230072969 + 3 ^ 40 * 5585217 * 2
def baseEnd_5585217 : Nat := 2867900880662779546501561

theorem tailTrace_5585217 : CollatzResearch.WordTrace tailWord_5585217 prefixEnd_5585217 2867900880662779546501561 := by
  unfold tailWord_5585217
  simp only [CollatzResearch.WordTrace]
  refine ⟨203709599406720162966513905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135806399604480108644342603 203709599406720162966513905)
  ·
    refine ⟨152782199555040122224885429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203709599406720162966513905 152782199555040122224885429)
    ·
      refine ⟨14323331208285011458583009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 152782199555040122224885429 14323331208285011458583009)
      ·
        refine ⟨10742498406213758593937257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14323331208285011458583009 10742498406213758593937257)
        ·
          refine ⟨8056873804660318945452943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10742498406213758593937257 8056873804660318945452943)
          ·
            refine ⟨12085310706990478418179415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8056873804660318945452943 12085310706990478418179415)
            ·
              refine ⟨18127966060485717627269123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12085310706990478418179415 18127966060485717627269123)
              ·
                refine ⟨27191949090728576440903685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18127966060485717627269123 27191949090728576440903685)
                ·
                  refine ⟨5098490454511608082669441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27191949090728576440903685 5098490454511608082669441)
                  ·
                    refine ⟨3823867840883706062002081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5098490454511608082669441 3823867840883706062002081)
                    ·
                      refine ⟨2867900880662779546501561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3823867840883706062002081 2867900880662779546501561)
                      ·
                        rfl

theorem cell23_5585217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 1, 4, 2, 2].length) (baseStart_5585217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5585217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5585217 prefixEnd_5585217 := by exact prefixLift 5585217
  have htrace : WordTrace (prefixWord ++ tailWord_5585217) baseStart_5585217 baseEnd_5585217 := by
    simpa [prefixWord, tailWord_5585217, baseEnd_5585217] using wordTrace_append hprefix tailTrace_5585217
  have hstable : (prefixWord ++ tailWord_5585217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5585217).length < 2 ^ (prefixWord ++ tailWord_5585217).sum := by decide
  have hdescent : baseEnd_5585217 < baseStart_5585217 := by decide
  rcases family_descends (prefixWord ++ tailWord_5585217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5585236 : List Nat := [2, 4, 1, 1, 2, 2, 1, 2, 1, 7]
def baseStart_5585236 : Nat := 118140960795 + 5585236 * 2 ^ 59
def prefixEnd_5585236 : Nat := 4983230072969 + 3 ^ 40 * 5585236 * 2
def baseEnd_5585236 : Nat := 955970212265071657387991

theorem tailTrace_5585236 : CollatzResearch.WordTrace tailWord_5585236 prefixEnd_5585236 955970212265071657387991 := by
  unfold tailWord_5585236
  simp only [CollatzResearch.WordTrace]
  refine ⟨101855146196825664605727781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135806861595767552807637041 101855146196825664605727781)
  ·
    refine ⟨19097839911904812113573959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101855146196825664605727781 19097839911904812113573959)
    ·
      refine ⟨28646759867857218170360939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19097839911904812113573959 28646759867857218170360939)
      ·
        refine ⟨42970139801785827255541409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28646759867857218170360939 42970139801785827255541409)
        ·
          refine ⟨32227604851339370441656057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42970139801785827255541409 32227604851339370441656057)
          ·
            refine ⟨24170703638504527831242043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32227604851339370441656057 24170703638504527831242043)
            ·
              refine ⟨36256055457756791746863065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24170703638504527831242043 36256055457756791746863065)
              ·
                refine ⟨27192041593317593810147299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36256055457756791746863065 27192041593317593810147299)
                ·
                  refine ⟨40788062389976390715220949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27192041593317593810147299 40788062389976390715220949)
                  ·
                    refine ⟨955970212265071657387991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40788062389976390715220949 955970212265071657387991)
                    ·
                      rfl

theorem cell23_5585236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 2, 1, 7].length) (baseStart_5585236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5585236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5585236 prefixEnd_5585236 := by exact prefixLift 5585236
  have htrace : WordTrace (prefixWord ++ tailWord_5585236) baseStart_5585236 baseEnd_5585236 := by
    simpa [prefixWord, tailWord_5585236, baseEnd_5585236] using wordTrace_append hprefix tailTrace_5585236
  have hstable : (prefixWord ++ tailWord_5585236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5585236).length < 2 ^ (prefixWord ++ tailWord_5585236).sum := by decide
  have hdescent : baseEnd_5585236 < baseStart_5585236 := by decide
  rcases family_descends (prefixWord ++ tailWord_5585236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5585276 : List Nat := [2, 2, 2, 1, 1, 1, 2, 2, 3, 4, 3]
def baseStart_5585276 : Nat := 118140960795 + 5585276 * 2 ^ 59
def prefixEnd_5585276 : Nat := 4983230072969 + 3 ^ 40 * 5585276 * 2
def baseEnd_5585276 : Nat := 2867931176021394815663789

theorem tailTrace_5585276 : CollatzResearch.WordTrace tailWord_5585276 prefixEnd_5585276 2867931176021394815663789 := by
  unfold tailWord_5585276
  simp only [CollatzResearch.WordTrace]
  refine ⟨101855875656753208021455841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135807834209004277361941121 101855875656753208021455841)
  ·
    refine ⟨76391906742564906016091881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101855875656753208021455841 76391906742564906016091881)
    ·
      refine ⟨57293930056923679512068911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76391906742564906016091881 57293930056923679512068911)
      ·
        refine ⟨85940895085385519268103367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57293930056923679512068911 85940895085385519268103367)
        ·
          refine ⟨128911342628078278902155051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85940895085385519268103367 128911342628078278902155051)
          ·
            refine ⟨193367013942117418353232577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128911342628078278902155051 193367013942117418353232577)
            ·
              refine ⟨145025260456588063764924433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 193367013942117418353232577 145025260456588063764924433)
              ·
                refine ⟨108768945342441047823693325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 145025260456588063764924433 108768945342441047823693325)
                ·
                  refine ⟨40788354503415392933884997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 108768945342441047823693325 40788354503415392933884997)
                  ·
                    refine ⟨7647816469390386175103437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40788354503415392933884997 7647816469390386175103437)
                    ·
                      refine ⟨2867931176021394815663789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7647816469390386175103437 2867931176021394815663789)
                      ·
                        rfl

theorem cell23_5585276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 3, 4, 3].length) (baseStart_5585276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5585276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5585276 prefixEnd_5585276 := by exact prefixLift 5585276
  have htrace : WordTrace (prefixWord ++ tailWord_5585276) baseStart_5585276 baseEnd_5585276 := by
    simpa [prefixWord, tailWord_5585276, baseEnd_5585276] using wordTrace_append hprefix tailTrace_5585276
  have hstable : (prefixWord ++ tailWord_5585276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5585276).length < 2 ^ (prefixWord ++ tailWord_5585276).sum := by decide
  have hdescent : baseEnd_5585276 < baseStart_5585276 := by decide
  rcases family_descends (prefixWord ++ tailWord_5585276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5585373 : List Nat := [1, 4, 3, 1, 1, 1, 1, 4, 1, 6]
def baseStart_5585373 : Nat := 118140960795 + 5585373 * 2 ^ 59
def prefixEnd_5585373 : Nat := 4983230072969 + 3 ^ 40 * 5585373 * 2
def baseEnd_5585373 : Nat := 955993661214960312050281

theorem tailTrace_5585373 : CollatzResearch.WordTrace tailWord_5585373 prefixEnd_5585373 955993661214960312050281 := by
  unfold tailWord_5585373
  simp only [CollatzResearch.WordTrace]
  refine ⟨203715289194155001609192773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135810192796103334406128515 203715289194155001609192773)
  ·
    refine ⟨38196616723904062801723645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 203715289194155001609192773 38196616723904062801723645)
    ·
      refine ⟨14323731271464023550646367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38196616723904062801723645 14323731271464023550646367)
      ·
        refine ⟨21485596907196035325969551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14323731271464023550646367 21485596907196035325969551)
        ·
          refine ⟨32228395360794052988954327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21485596907196035325969551 32228395360794052988954327)
          ·
            refine ⟨48342593041191079483431491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32228395360794052988954327 48342593041191079483431491)
            ·
              refine ⟨72513889561786619225147237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48342593041191079483431491 72513889561786619225147237)
              ·
                refine ⟨13596354292834991104715107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72513889561786619225147237 13596354292834991104715107)
                ·
                  refine ⟨20394531439252486657072661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13596354292834991104715107 20394531439252486657072661)
                  ·
                    refine ⟨955993661214960312050281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20394531439252486657072661 955993661214960312050281)
                    ·
                      rfl

theorem cell23_5585373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_5585373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5585373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5585373 prefixEnd_5585373 := by exact prefixLift 5585373
  have htrace : WordTrace (prefixWord ++ tailWord_5585373) baseStart_5585373 baseEnd_5585373 := by
    simpa [prefixWord, tailWord_5585373, baseEnd_5585373] using wordTrace_append hprefix tailTrace_5585373
  have hstable : (prefixWord ++ tailWord_5585373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5585373).length < 2 ^ (prefixWord ++ tailWord_5585373).sum := by decide
  have hdescent : baseEnd_5585373 < baseStart_5585373 := by decide
  rcases family_descends (prefixWord ++ tailWord_5585373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5585383 : List Nat := [1, 1, 5, 2, 1, 1, 2, 3, 1, 1, 5]
def baseStart_5585383 : Nat := 118140960795 + 5585383 * 2 ^ 59
def prefixEnd_5585383 : Nat := 4983230072969 + 3 ^ 40 * 5585383 * 2
def baseEnd_5585383 : Nat := 2867986118451425897025797

theorem tailTrace_5585383 : CollatzResearch.WordTrace tailWord_5585383 prefixEnd_5585383 2867986118451425897025797 := by
  unfold tailWord_5585383
  simp only [CollatzResearch.WordTrace]
  refine ⟨203715653924118773317056803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135810435949412515544704535 203715653924118773317056803)
  ·
    refine ⟨305573480886178159975585205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203715653924118773317056803 305573480886178159975585205)
    ·
      refine ⟨28647513833079202497711113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 305573480886178159975585205 28647513833079202497711113)
      ·
        refine ⟨21485635374809401873283335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28647513833079202497711113 21485635374809401873283335)
        ·
          refine ⟨32228453062214102809925003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21485635374809401873283335 32228453062214102809925003)
          ·
            refine ⟨48342679593321154214887505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32228453062214102809925003 48342679593321154214887505)
            ·
              refine ⟨36257009694990865661165629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48342679593321154214887505 36257009694990865661165629)
              ·
                refine ⟨13596378635621574622937111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36257009694990865661165629 13596378635621574622937111)
                ·
                  refine ⟨20394567953432361934405667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13596378635621574622937111 20394567953432361934405667)
                  ·
                    refine ⟨30591851930148542901608501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20394567953432361934405667 30591851930148542901608501)
                    ·
                      refine ⟨2867986118451425897025797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30591851930148542901608501 2867986118451425897025797)
                      ·
                        rfl

theorem cell23_5585383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_5585383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5585383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5585383 prefixEnd_5585383 := by exact prefixLift 5585383
  have htrace : WordTrace (prefixWord ++ tailWord_5585383) baseStart_5585383 baseEnd_5585383 := by
    simpa [prefixWord, tailWord_5585383, baseEnd_5585383] using wordTrace_append hprefix tailTrace_5585383
  have hstable : (prefixWord ++ tailWord_5585383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5585383).length < 2 ^ (prefixWord ++ tailWord_5585383).sum := by decide
  have hdescent : baseEnd_5585383 < baseStart_5585383 := by decide
  rcases family_descends (prefixWord ++ tailWord_5585383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5585390 : List Nat := [4, 1, 2, 1, 2, 3, 1, 1, 4, 4]
def baseStart_5585390 : Nat := 118140960795 + 5585390 * 2 ^ 59
def prefixEnd_5585390 : Nat := 4983230072969 + 3 ^ 40 * 5585390 * 2
def baseEnd_5585390 : Nat := 955996570938669123212755

theorem tailTrace_5585390 : CollatzResearch.WordTrace tailWord_5585390 prefixEnd_5585390 955996570938669123212755 := by
  unfold tailWord_5585390
  simp only [CollatzResearch.WordTrace]
  refine ⟨25464488654386676689070203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135810606156728942341707749 25464488654386676689070203)
  ·
    refine ⟨38196732981580015033605305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25464488654386676689070203 38196732981580015033605305)
    ·
      refine ⟨28647549736185011275203979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38196732981580015033605305 28647549736185011275203979)
      ·
        refine ⟨42971324604277516912805969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28647549736185011275203979 42971324604277516912805969)
        ·
          refine ⟨32228493453208137684604477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42971324604277516912805969 32228493453208137684604477)
          ·
            refine ⟨12085685044953051631726679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32228493453208137684604477 12085685044953051631726679)
            ·
              refine ⟨18128527567429577447590019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12085685044953051631726679 18128527567429577447590019)
              ·
                refine ⟨27192791351144366171385029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18128527567429577447590019 27192791351144366171385029)
                ·
                  refine ⟨5098648378339568657134693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27192791351144366171385029 5098648378339568657134693)
                  ·
                    refine ⟨955996570938669123212755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5098648378339568657134693 955996570938669123212755)
                    ·
                      rfl

theorem cell23_5585390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 1, 4, 4].length) (baseStart_5585390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5585390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5585390 prefixEnd_5585390 := by exact prefixLift 5585390
  have htrace : WordTrace (prefixWord ++ tailWord_5585390) baseStart_5585390 baseEnd_5585390 := by
    simpa [prefixWord, tailWord_5585390, baseEnd_5585390] using wordTrace_append hprefix tailTrace_5585390
  have hstable : (prefixWord ++ tailWord_5585390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5585390).length < 2 ^ (prefixWord ++ tailWord_5585390).sum := by decide
  have hdescent : baseEnd_5585390 < baseStart_5585390 := by decide
  rcases family_descends (prefixWord ++ tailWord_5585390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5585420 : List Nat := [2, 2, 1, 2, 4, 3, 2, 7]
def baseStart_5585420 : Nat := 118140960795 + 5585420 * 2 ^ 59
def prefixEnd_5585420 : Nat := 4983230072969 + 3 ^ 40 * 5585420 * 2
def baseEnd_5585420 : Nat := 106222411749468231565301

theorem tailTrace_5585420 : CollatzResearch.WordTrace tailWord_5585420 prefixEnd_5585420 106222411749468231565301 := by
  unfold tailWord_5585420
  simp only [CollatzResearch.WordTrace]
  refine ⟨101858501712492364318076857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135811335616656485757435809 101858501712492364318076857)
  ·
    refine ⟨76393876284369273238557643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101858501712492364318076857 76393876284369273238557643)
    ·
      refine ⟨114590814426553909857836465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76393876284369273238557643 114590814426553909857836465)
      ·
        refine ⟨85943110819915432393377349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114590814426553909857836465 85943110819915432393377349)
        ·
          refine ⟨16114333278734143573758253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85943110819915432393377349 16114333278734143573758253)
          ·
            refine ⟨6042874979525303840159345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16114333278734143573758253 6042874979525303840159345)
            ·
              refine ⟨4532156234643977880119509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6042874979525303840159345 4532156234643977880119509)
              ·
                refine ⟨106222411749468231565301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4532156234643977880119509 106222411749468231565301)
                ·
                  rfl

theorem cell23_5585420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 2, 7].length) (baseStart_5585420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5585420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5585420 prefixEnd_5585420 := by exact prefixLift 5585420
  have htrace : WordTrace (prefixWord ++ tailWord_5585420) baseStart_5585420 baseEnd_5585420 := by
    simpa [prefixWord, tailWord_5585420, baseEnd_5585420] using wordTrace_append hprefix tailTrace_5585420
  have hstable : (prefixWord ++ tailWord_5585420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5585420).length < 2 ^ (prefixWord ++ tailWord_5585420).sum := by decide
  have hdescent : baseEnd_5585420 < baseStart_5585420 := by decide
  rcases family_descends (prefixWord ++ tailWord_5585420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5585448 : List Nat := [2, 1, 5, 2, 1, 2, 3, 2, 1, 2, 2]
def baseStart_5585448 : Nat := 118140960795 + 5585448 * 2 ^ 59
def prefixEnd_5585448 : Nat := 4983230072969 + 3 ^ 40 * 5585448 * 2
def baseEnd_5585448 : Nat := 2868019494693968142712999

theorem tailTrace_5585448 : CollatzResearch.WordTrace tailWord_5585448 prefixEnd_5585448 2868019494693968142712999 := by
  unfold tailWord_5585448
  simp only [CollatzResearch.WordTrace]
  refine ⟨101859012334441644709086499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135812016445922192945448665 101859012334441644709086499)
  ·
    refine ⟨152788518501662467063629749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101859012334441644709086499 152788518501662467063629749)
    ·
      refine ⟨14323923609530856287215289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 152788518501662467063629749 14323923609530856287215289)
      ·
        refine ⟨10742942707148142215411467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14323923609530856287215289 10742942707148142215411467)
        ·
          refine ⟨16114414060722213323117201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10742942707148142215411467 16114414060722213323117201)
          ·
            refine ⟨12085810545541659992337901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16114414060722213323117201 12085810545541659992337901)
            ·
              refine ⟨4532178954578122497126713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12085810545541659992337901 4532178954578122497126713)
              ·
                refine ⟨3399134215933591872845035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4532178954578122497126713 3399134215933591872845035)
                ·
                  refine ⟨5098701323900387809267553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3399134215933591872845035 5098701323900387809267553)
                  ·
                    refine ⟨3824025992925290856950665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5098701323900387809267553 3824025992925290856950665)
                    ·
                      refine ⟨2868019494693968142712999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3824025992925290856950665 2868019494693968142712999)
                      ·
                        rfl

theorem cell23_5585448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 3, 2, 1, 2, 2].length) (baseStart_5585448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5585448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5585448 prefixEnd_5585448 := by exact prefixLift 5585448
  have htrace : WordTrace (prefixWord ++ tailWord_5585448) baseStart_5585448 baseEnd_5585448 := by
    simpa [prefixWord, tailWord_5585448, baseEnd_5585448] using wordTrace_append hprefix tailTrace_5585448
  have hstable : (prefixWord ++ tailWord_5585448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5585448).length < 2 ^ (prefixWord ++ tailWord_5585448).sum := by decide
  have hdescent : baseEnd_5585448 < baseStart_5585448 := by decide
  rcases family_descends (prefixWord ++ tailWord_5585448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5585503 : List Nat := [1, 1, 2, 3, 1, 1, 1, 2, 3, 5, 3]
def baseStart_5585503 : Nat := 118140960795 + 5585503 * 2 ^ 59
def prefixEnd_5585503 : Nat := 4983230072969 + 3 ^ 40 * 5585503 * 2
def baseEnd_5585503 : Nat := 2868047736129965427525245

theorem tailTrace_5585503 : CollatzResearch.WordTrace tailWord_5585503 prefixEnd_5585503 2868047736129965427525245 := by
  unfold tailWord_5585503
  simp only [CollatzResearch.WordTrace]
  refine ⟨203720030683684033811425163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135813353789122689207616775 203720030683684033811425163)
  ·
    refine ⟨305580046025526050717137745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203720030683684033811425163 305580046025526050717137745)
    ·
      refine ⟨229185034519144538037853309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 305580046025526050717137745 229185034519144538037853309)
      ·
        refine ⟨85944387944679201764194991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 229185034519144538037853309 85944387944679201764194991)
        ·
          refine ⟨128916581917018802646292487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85944387944679201764194991 128916581917018802646292487)
          ·
            refine ⟨193374872875528203969438731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128916581917018802646292487 193374872875528203969438731)
            ·
              refine ⟨290062309313292305954158097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 193374872875528203969438731 290062309313292305954158097)
              ·
                refine ⟨217546731984969229465618573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 290062309313292305954158097 217546731984969229465618573)
                ·
                  refine ⟨81580024494363461049606965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 217546731984969229465618573 81580024494363461049606965)
                  ·
                    refine ⟨7648127296346574473400653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 81580024494363461049606965 7648127296346574473400653)
                    ·
                      refine ⟨2868047736129965427525245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7648127296346574473400653 2868047736129965427525245)
                      ·
                        rfl

theorem cell23_5585503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 3, 5, 3].length) (baseStart_5585503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5585503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5585503 prefixEnd_5585503 := by exact prefixLift 5585503
  have htrace : WordTrace (prefixWord ++ tailWord_5585503) baseStart_5585503 baseEnd_5585503 := by
    simpa [prefixWord, tailWord_5585503, baseEnd_5585503] using wordTrace_append hprefix tailTrace_5585503
  have hstable : (prefixWord ++ tailWord_5585503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5585503).length < 2 ^ (prefixWord ++ tailWord_5585503).sum := by decide
  have hdescent : baseEnd_5585503 < baseStart_5585503 := by decide
  rcases family_descends (prefixWord ++ tailWord_5585503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5585540 : List Nat := [2, 3, 2, 1, 3, 2, 1, 1, 1, 7]
def baseStart_5585540 : Nat := 118140960795 + 5585540 * 2 ^ 59
def prefixEnd_5585540 : Nat := 4983230072969 + 3 ^ 40 * 5585540 * 2
def baseEnd_5585540 : Nat := 956022244971393927587525

theorem tailTrace_5585540 : CollatzResearch.WordTrace tailWord_5585540 prefixEnd_5585540 956022244971393927587525 := by
  unfold tailWord_5585540
  simp only [CollatzResearch.WordTrace]
  refine ⟨101860690092274994565261037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135814253456366659420348049 101860690092274994565261037)
  ·
    refine ⟨38197758784603122961972889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101860690092274994565261037 38197758784603122961972889)
    ·
      refine ⟨28648319088452342221479667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38197758784603122961972889 28648319088452342221479667)
      ·
        refine ⟨42972478632678513332219501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28648319088452342221479667 42972478632678513332219501)
        ·
          refine ⟨16114679487254442499582313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42972478632678513332219501 16114679487254442499582313)
          ·
            refine ⟨12086009615440831874686735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16114679487254442499582313 12086009615440831874686735)
            ·
              refine ⟨18129014423161247812030103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12086009615440831874686735 18129014423161247812030103)
              ·
                refine ⟨27193521634741871718045155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18129014423161247812030103 27193521634741871718045155)
                ·
                  refine ⟨40790282452112807577067733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27193521634741871718045155 40790282452112807577067733)
                  ·
                    refine ⟨956022244971393927587525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40790282452112807577067733 956022244971393927587525)
                    ·
                      rfl

theorem cell23_5585540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 1, 1, 7].length) (baseStart_5585540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5585540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5585540 prefixEnd_5585540 := by exact prefixLift 5585540
  have htrace : WordTrace (prefixWord ++ tailWord_5585540) baseStart_5585540 baseEnd_5585540 := by
    simpa [prefixWord, tailWord_5585540, baseEnd_5585540] using wordTrace_append hprefix tailTrace_5585540
  have hstable : (prefixWord ++ tailWord_5585540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5585540).length < 2 ^ (prefixWord ++ tailWord_5585540).sum := by decide
  have hdescent : baseEnd_5585540 < baseStart_5585540 := by decide
  rcases family_descends (prefixWord ++ tailWord_5585540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5585560 : List Nat := [2, 1, 2, 4, 1, 1, 2, 1, 4, 1, 4]
def baseStart_5585560 : Nat := 118140960795 + 5585560 * 2 ^ 59
def prefixEnd_5585560 : Nat := 4983230072969 + 3 ^ 40 * 5585560 * 2
def baseEnd_5585560 : Nat := 2868077004527271704512483

theorem tailTrace_5585560 : CollatzResearch.WordTrace tailWord_5585560 prefixEnd_5585560 2868077004527271704512483 := by
  unfold tailWord_5585560
  simp only [CollatzResearch.WordTrace]
  refine ⟨101861054822238766273125067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135814739762985021697500089 101861054822238766273125067)
  ·
    refine ⟨152791582233358149409687601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101861054822238766273125067 152791582233358149409687601)
    ·
      refine ⟨114593686675018612057265701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152791582233358149409687601 114593686675018612057265701)
      ·
        refine ⟨21486316251565989760737319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 114593686675018612057265701 21486316251565989760737319)
        ·
          refine ⟨32229474377348984641105979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21486316251565989760737319 32229474377348984641105979)
          ·
            refine ⟨48344211566023476961658969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32229474377348984641105979 48344211566023476961658969)
            ·
              refine ⟨36258158674517607721244227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48344211566023476961658969 36258158674517607721244227)
              ·
                refine ⟨54387238011776411581866341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36258158674517607721244227 54387238011776411581866341)
                ·
                  refine ⟨10197607127208077171599939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54387238011776411581866341 10197607127208077171599939)
                  ·
                    refine ⟨15296410690812115757399909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10197607127208077171599939 15296410690812115757399909)
                    ·
                      refine ⟨2868077004527271704512483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15296410690812115757399909 2868077004527271704512483)
                      ·
                        rfl

theorem cell23_5585560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_5585560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5585560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5585560 prefixEnd_5585560 := by exact prefixLift 5585560
  have htrace : WordTrace (prefixWord ++ tailWord_5585560) baseStart_5585560 baseEnd_5585560 := by
    simpa [prefixWord, tailWord_5585560, baseEnd_5585560] using wordTrace_append hprefix tailTrace_5585560
  have hstable : (prefixWord ++ tailWord_5585560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5585560).length < 2 ^ (prefixWord ++ tailWord_5585560).sum := by decide
  have hdescent : baseEnd_5585560 < baseStart_5585560 := by decide
  rcases family_descends (prefixWord ++ tailWord_5585560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5585573 : List Nat := [1, 3, 1, 2, 1, 2, 1, 1, 4, 1, 6]
def baseStart_5585573 : Nat := 118140960795 + 5585573 * 2 ^ 59
def prefixEnd_5585573 : Nat := 4983230072969 + 3 ^ 40 * 5585573 * 2
def baseEnd_5585573 : Nat := 2868083679775780153649923

theorem tailTrace_5585573 : CollatzResearch.WordTrace tailWord_5585573 prefixEnd_5585573 2868083679775780153649923 := by
  unfold tailWord_5585573
  simp only [CollatzResearch.WordTrace]
  refine ⟨203722583793430435766473373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135815055862286957177648915 203722583793430435766473373)
  ·
    refine ⟨76395968922536413412427515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 203722583793430435766473373 76395968922536413412427515)
    ·
      refine ⟨114593953383804620118641273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76395968922536413412427515 114593953383804620118641273)
      ·
        refine ⟨85945465037853465088980955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114593953383804620118641273 85945465037853465088980955)
        ·
          refine ⟨128918197556780197633471433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85945465037853465088980955 128918197556780197633471433)
          ·
            refine ⟨96688648167585148225103575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128918197556780197633471433 96688648167585148225103575)
            ·
              refine ⟨145032972251377722337655363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96688648167585148225103575 145032972251377722337655363)
              ·
                refine ⟨217549458377066583506483045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 145032972251377722337655363 217549458377066583506483045)
                ·
                  refine ⟨40790523445699984407465571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 217549458377066583506483045 40790523445699984407465571)
                  ·
                    refine ⟨61185785168549976611198357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40790523445699984407465571 61185785168549976611198357)
                    ·
                      refine ⟨2868083679775780153649923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61185785168549976611198357 2868083679775780153649923)
                      ·
                        rfl

theorem cell23_5585573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 4, 1, 6].length) (baseStart_5585573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5585573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5585573 prefixEnd_5585573 := by exact prefixLift 5585573
  have htrace : WordTrace (prefixWord ++ tailWord_5585573) baseStart_5585573 baseEnd_5585573 := by
    simpa [prefixWord, tailWord_5585573, baseEnd_5585573] using wordTrace_append hprefix tailTrace_5585573
  have hstable : (prefixWord ++ tailWord_5585573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5585573).length < 2 ^ (prefixWord ++ tailWord_5585573).sum := by decide
  have hdescent : baseEnd_5585573 < baseStart_5585573 := by decide
  rcases family_descends (prefixWord ++ tailWord_5585573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5585621 : List Nat := [1, 3, 2, 5, 1, 2, 1, 1, 3, 4]
def baseStart_5585621 : Nat := 118140960795 + 5585621 * 2 ^ 59
def prefixEnd_5585621 : Nat := 4983230072969 + 3 ^ 40 * 5585621 * 2
def baseEnd_5585621 : Nat := 956036108949065321949901

theorem tailTrace_5585621 : CollatzResearch.WordTrace tailWord_5585621 prefixEnd_5585621 956036108949065321949901 := by
  unfold tailWord_5585621
  simp only [CollatzResearch.WordTrace]
  refine ⟨203724334497256539964220717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135816222998171026642813811 203724334497256539964220717)
  ·
    refine ⟨76396625436471202486582769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 203724334497256539964220717 76396625436471202486582769)
    ·
      refine ⟨57297469077353401864937077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76396625436471202486582769 57297469077353401864937077)
      ·
        refine ⟨5371637726001881424837851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 57297469077353401864937077 5371637726001881424837851)
        ·
          refine ⟨8057456589002822137256777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5371637726001881424837851 8057456589002822137256777)
          ·
            refine ⟨6043092441752116602942583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8057456589002822137256777 6043092441752116602942583)
            ·
              refine ⟨9064638662628174904413875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6043092441752116602942583 9064638662628174904413875)
              ·
                refine ⟨13596957993942262356620813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9064638662628174904413875 13596957993942262356620813)
                ·
                  refine ⟨5098859247728348383732805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13596957993942262356620813 5098859247728348383732805)
                  ·
                    refine ⟨956036108949065321949901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5098859247728348383732805 956036108949065321949901)
                    ·
                      rfl

theorem cell23_5585621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 1, 3, 4].length) (baseStart_5585621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5585621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5585621 prefixEnd_5585621 := by exact prefixLift 5585621
  have htrace : WordTrace (prefixWord ++ tailWord_5585621) baseStart_5585621 baseEnd_5585621 := by
    simpa [prefixWord, tailWord_5585621, baseEnd_5585621] using wordTrace_append hprefix tailTrace_5585621
  have hstable : (prefixWord ++ tailWord_5585621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5585621).length < 2 ^ (prefixWord ++ tailWord_5585621).sum := by decide
  have hdescent : baseEnd_5585621 < baseStart_5585621 := by decide
  rcases family_descends (prefixWord ++ tailWord_5585621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5585647 : List Nat := [1, 1, 2, 1, 5, 2, 3, 2, 1, 5]
def baseStart_5585647 : Nat := 118140960795 + 5585647 * 2 ^ 59
def prefixEnd_5585647 : Nat := 4983230072969 + 3 ^ 40 * 5585647 * 2
def baseEnd_5585647 : Nat := 956040559114737621374861

theorem tailTrace_5585647 : CollatzResearch.WordTrace tailWord_5585647 prefixEnd_5585647 956040559114737621374861 := by
  unfold tailWord_5585647
  simp only [CollatzResearch.WordTrace]
  refine ⟨203725282795162346404667195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135816855196774897603111463 203725282795162346404667195)
  ·
    refine ⟨305587924192743519607000793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203725282795162346404667195 305587924192743519607000793)
    ·
      refine ⟨229190943144557639705250595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 305587924192743519607000793 229190943144557639705250595)
      ·
        refine ⟨343786414716836459557875893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229190943144557639705250595 343786414716836459557875893)
        ·
          refine ⟨32229976379703418083550865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 343786414716836459557875893 32229976379703418083550865)
          ·
            refine ⟨24172482284777563562663149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32229976379703418083550865 24172482284777563562663149)
            ·
              refine ⟨9064680856791586335998681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24172482284777563562663149 9064680856791586335998681)
              ·
                refine ⟨6798510642593689751999011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9064680856791586335998681 6798510642593689751999011)
                ·
                  refine ⟨10197765963890534627998517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6798510642593689751999011 10197765963890534627998517)
                  ·
                    refine ⟨956040559114737621374861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10197765963890534627998517 956040559114737621374861)
                    ·
                      rfl

theorem cell23_5585647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 2, 1, 5].length) (baseStart_5585647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5585647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5585647 prefixEnd_5585647 := by exact prefixLift 5585647
  have htrace : WordTrace (prefixWord ++ tailWord_5585647) baseStart_5585647 baseEnd_5585647 := by
    simpa [prefixWord, tailWord_5585647, baseEnd_5585647] using wordTrace_append hprefix tailTrace_5585647
  have hstable : (prefixWord ++ tailWord_5585647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5585647).length < 2 ^ (prefixWord ++ tailWord_5585647).sum := by decide
  have hdescent : baseEnd_5585647 < baseStart_5585647 := by decide
  rcases family_descends (prefixWord ++ tailWord_5585647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5585660 : List Nat := [2, 2, 2, 1, 3, 2, 1, 1, 3, 6]
def baseStart_5585660 : Nat := 118140960795 + 5585660 * 2 ^ 59
def prefixEnd_5585660 : Nat := 4983230072969 + 3 ^ 40 * 5585660 * 2
def baseEnd_5585660 : Nat := 956042784197573771087341

theorem tailTrace_5585660 : CollatzResearch.WordTrace tailWord_5585660 prefixEnd_5585660 956042784197573771087341 := by
  unfold tailWord_5585660
  simp only [CollatzResearch.WordTrace]
  refine ⟨101862878472057624812445217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135817171296076833083260289 101862878472057624812445217)
  ·
    refine ⟨76397158854043218609333913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101862878472057624812445217 76397158854043218609333913)
    ·
      refine ⟨57297869140532413957000435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76397158854043218609333913 57297869140532413957000435)
      ·
        refine ⟨85946803710798620935500653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57297869140532413957000435 85946803710798620935500653)
        ·
          refine ⟨32230051391549482850812745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85946803710798620935500653 32230051391549482850812745)
          ·
            refine ⟨24172538543662112138109559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32230051391549482850812745 24172538543662112138109559)
            ·
              refine ⟨36258807815493168207164339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24172538543662112138109559 36258807815493168207164339)
              ·
                refine ⟨54388211723239752310746509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36258807815493168207164339 54388211723239752310746509)
                ·
                  refine ⟨20395579396214907116529941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54388211723239752310746509 20395579396214907116529941)
                  ·
                    refine ⟨956042784197573771087341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20395579396214907116529941 956042784197573771087341)
                    ·
                      rfl

theorem cell23_5585660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 1, 3, 6].length) (baseStart_5585660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5585660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5585660 prefixEnd_5585660 := by exact prefixLift 5585660
  have htrace : WordTrace (prefixWord ++ tailWord_5585660) baseStart_5585660 baseEnd_5585660 := by
    simpa [prefixWord, tailWord_5585660, baseEnd_5585660] using wordTrace_append hprefix tailTrace_5585660
  have hstable : (prefixWord ++ tailWord_5585660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5585660).length < 2 ^ (prefixWord ++ tailWord_5585660).sum := by decide
  have hdescent : baseEnd_5585660 < baseStart_5585660 := by decide
  rcases family_descends (prefixWord ++ tailWord_5585660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5585697 : List Nat := [1, 2, 3, 2, 1, 2, 4, 1, 1, 2, 4]
def baseStart_5585697 : Nat := 118140960795 + 5585697 * 2 ^ 59
def prefixEnd_5585697 : Nat := 4983230072969 + 3 ^ 40 * 5585697 * 2
def baseEnd_5585697 : Nat := 2868147351376937668499353

theorem tailTrace_5585697 : CollatzResearch.WordTrace tailWord_5585697 prefixEnd_5585697 2868147351376937668499353 := by
  unfold tailWord_5585697
  simp only [CollatzResearch.WordTrace]
  refine ⟨203727106444981204943987345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135818070963320803295991563 203727106444981204943987345)
  ·
    refine ⟨152795329833735903707990509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203727106444981204943987345 152795329833735903707990509)
    ·
      refine ⟨57298248687650963890496441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152795329833735903707990509 57298248687650963890496441)
      ·
        refine ⟨42973686515738222917872331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57298248687650963890496441 42973686515738222917872331)
        ·
          refine ⟨64460529773607334376808497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42973686515738222917872331 64460529773607334376808497)
          ·
            refine ⟨48345397330205500782606373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64460529773607334376808497 48345397330205500782606373)
            ·
              refine ⟨9064761999413531396738695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48345397330205500782606373 9064761999413531396738695)
              ·
                refine ⟨13597142999120297095108043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9064761999413531396738695 13597142999120297095108043)
                ·
                  refine ⟨20395714498680445642662065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13597142999120297095108043 20395714498680445642662065)
                  ·
                    refine ⟨15296785874010334231996549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20395714498680445642662065 15296785874010334231996549)
                    ·
                      refine ⟨2868147351376937668499353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15296785874010334231996549 2868147351376937668499353)
                      ·
                        rfl

theorem cell23_5585697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 1, 1, 2, 4].length) (baseStart_5585697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5585697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5585697 prefixEnd_5585697 := by exact prefixLift 5585697
  have htrace : WordTrace (prefixWord ++ tailWord_5585697) baseStart_5585697 baseEnd_5585697 := by
    simpa [prefixWord, tailWord_5585697, baseEnd_5585697] using wordTrace_append hprefix tailTrace_5585697
  have hstable : (prefixWord ++ tailWord_5585697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5585697).length < 2 ^ (prefixWord ++ tailWord_5585697).sum := by decide
  have hdescent : baseEnd_5585697 < baseStart_5585697 := by decide
  rcases family_descends (prefixWord ++ tailWord_5585697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5585704 : List Nat := [2, 1, 5, 1, 1, 1, 2, 4, 1, 2, 3]
def baseStart_5585704 : Nat := 118140960795 + 5585704 * 2 ^ 59
def prefixEnd_5585704 : Nat := 4983230072969 + 3 ^ 40 * 5585704 * 2
def baseEnd_5585704 : Nat := 2868150945741519141111821

theorem tailTrace_5585704 : CollatzResearch.WordTrace tailWord_5585704 prefixEnd_5585704 2868150945741519141111821 := by
  unfold tailWord_5585704
  simp only [CollatzResearch.WordTrace]
  refine ⟨101863680877977922569746083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135818241170637230092994777 101863680877977922569746083)
  ·
    refine ⟨152795521316966883854619125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101863680877977922569746083 152795521316966883854619125)
    ·
      refine ⟨14324580123465645361370543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 152795521316966883854619125 14324580123465645361370543)
      ·
        refine ⟨21486870185198468042055815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14324580123465645361370543 21486870185198468042055815)
        ·
          refine ⟨32230305277797702063083723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21486870185198468042055815 32230305277797702063083723)
          ·
            refine ⟨48345457916696553094625585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32230305277797702063083723 48345457916696553094625585)
            ·
              refine ⟨36259093437522414820969189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48345457916696553094625585 36259093437522414820969189)
              ·
                refine ⟨6798580019535452778931723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36259093437522414820969189 6798580019535452778931723)
                ·
                  refine ⟨10197870029303179168397585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6798580019535452778931723 10197870029303179168397585)
                  ·
                    refine ⟨7648402521977384376298189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10197870029303179168397585 7648402521977384376298189)
                    ·
                      refine ⟨2868150945741519141111821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7648402521977384376298189 2868150945741519141111821)
                      ·
                        rfl

theorem cell23_5585704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 4, 1, 2, 3].length) (baseStart_5585704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5585704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5585704 prefixEnd_5585704 := by exact prefixLift 5585704
  have htrace : WordTrace (prefixWord ++ tailWord_5585704) baseStart_5585704 baseEnd_5585704 := by
    simpa [prefixWord, tailWord_5585704, baseEnd_5585704] using wordTrace_append hprefix tailTrace_5585704
  have hstable : (prefixWord ++ tailWord_5585704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5585704).length < 2 ^ (prefixWord ++ tailWord_5585704).sum := by decide
  have hdescent : baseEnd_5585704 < baseStart_5585704 := by decide
  rcases family_descends (prefixWord ++ tailWord_5585704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5585777 : List Nat := [1, 2, 2, 2, 1, 5, 1, 1, 2, 1, 5]
def baseStart_5585777 : Nat := 118140960795 + 5585777 * 2 ^ 59
def prefixEnd_5585777 : Nat := 4983230072969 + 3 ^ 40 * 5585777 * 2
def baseEnd_5585777 : Nat := 2868188429829297355498985

theorem tailTrace_5585777 : CollatzResearch.WordTrace tailWord_5585777 prefixEnd_5585777 2868188429829297355498985 := by
  unfold tailWord_5585777
  simp only [CollatzResearch.WordTrace]
  refine ⟨203730024284691378606899585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135820016189794252404599723 203730024284691378606899585)
  ·
    refine ⟨152797518213518533955174689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203730024284691378606899585 152797518213518533955174689)
    ·
      refine ⟨114598138660138900466381017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152797518213518533955174689 114598138660138900466381017)
      ·
        refine ⟨85948603995104175349785763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114598138660138900466381017 85948603995104175349785763)
        ·
          refine ⟨128922905992656263024678645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85948603995104175349785763 128922905992656263024678645)
          ·
            refine ⟨12086522436811524658563623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 128922905992656263024678645 12086522436811524658563623)
            ·
              refine ⟨18129783655217286987845435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12086522436811524658563623 18129783655217286987845435)
              ·
                refine ⟨27194675482825930481768153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18129783655217286987845435 27194675482825930481768153)
                ·
                  refine ⟨20396006612119447861326115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27194675482825930481768153 20396006612119447861326115)
                  ·
                    refine ⟨30594009918179171791989173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20396006612119447861326115 30594009918179171791989173)
                    ·
                      refine ⟨2868188429829297355498985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30594009918179171791989173 2868188429829297355498985)
                      ·
                        rfl

theorem cell23_5585777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 1, 2, 1, 5].length) (baseStart_5585777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5585777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5585777 prefixEnd_5585777 := by exact prefixLift 5585777
  have htrace : WordTrace (prefixWord ++ tailWord_5585777) baseStart_5585777 baseEnd_5585777 := by
    simpa [prefixWord, tailWord_5585777, baseEnd_5585777] using wordTrace_append hprefix tailTrace_5585777
  have hstable : (prefixWord ++ tailWord_5585777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5585777).length < 2 ^ (prefixWord ++ tailWord_5585777).sum := by decide
  have hdescent : baseEnd_5585777 < baseStart_5585777 := by decide
  rcases family_descends (prefixWord ++ tailWord_5585777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5585797 : List Nat := [1, 3, 1, 1, 3, 3, 3, 1, 7]
def baseStart_5585797 : Nat := 118140960795 + 5585797 * 2 ^ 59
def prefixEnd_5585797 : Nat := 4983230072969 + 3 ^ 40 * 5585797 * 2
def baseEnd_5585797 : Nat := 318688744382487475249877

theorem tailTrace_5585797 : CollatzResearch.WordTrace tailWord_5585797 prefixEnd_5585797 318688744382487475249877 := by
  unfold tailWord_5585797
  simp only [CollatzResearch.WordTrace]
  refine ⟨203730753744618922022627645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135820502496412614681751763 203730753744618922022627645)
  ·
    refine ⟨76399032654232095758485367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 203730753744618922022627645 76399032654232095758485367)
    ·
      refine ⟨114598548981348143637728051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76399032654232095758485367 114598548981348143637728051)
      ·
        refine ⟨171897823472022215456592077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114598548981348143637728051 171897823472022215456592077)
        ·
          refine ⟨64461683802008330796222029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 171897823472022215456592077 64461683802008330796222029)
          ·
            refine ⟨24173131425753124048583261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64461683802008330796222029 24173131425753124048583261)
            ·
              refine ⟨9064924284657421518218723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24173131425753124048583261 9064924284657421518218723)
              ·
                refine ⟨13597386426986132277328085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9064924284657421518218723 13597386426986132277328085)
                ·
                  refine ⟨318688744382487475249877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13597386426986132277328085 318688744382487475249877)
                  ·
                    rfl

theorem cell23_5585797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 1, 7].length) (baseStart_5585797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5585797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5585797 prefixEnd_5585797 := by exact prefixLift 5585797
  have htrace : WordTrace (prefixWord ++ tailWord_5585797) baseStart_5585797 baseEnd_5585797 := by
    simpa [prefixWord, tailWord_5585797, baseEnd_5585797] using wordTrace_append hprefix tailTrace_5585797
  have hstable : (prefixWord ++ tailWord_5585797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5585797).length < 2 ^ (prefixWord ++ tailWord_5585797).sum := by decide
  have hdescent : baseEnd_5585797 < baseStart_5585797 := by decide
  rcases family_descends (prefixWord ++ tailWord_5585797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5585827 : List Nat := [1, 1, 1, 4, 1, 2, 3, 3, 2, 5]
def baseStart_5585827 : Nat := 118140960795 + 5585827 * 2 ^ 59
def prefixEnd_5585827 : Nat := 4983230072969 + 3 ^ 40 * 5585827 * 2
def baseEnd_5585827 : Nat := 956071367954007386624585

theorem tailTrace_5585827 : CollatzResearch.WordTrace tailWord_5585827 prefixEnd_5585827 956071367954007386624585 := by
  unfold tailWord_5585827
  simp only [CollatzResearch.WordTrace]
  refine ⟨203731847934510237146219735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135821231956340158097479823 203731847934510237146219735)
  ·
    refine ⟨305597771901765355719329603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203731847934510237146219735 305597771901765355719329603)
    ·
      refine ⟨458396657852648033578994405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305597771901765355719329603 458396657852648033578994405)
      ·
        refine ⟨85949373347371506296061451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 458396657852648033578994405 85949373347371506296061451)
        ·
          refine ⟨128924060021057259444092177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85949373347371506296061451 128924060021057259444092177)
          ·
            refine ⟨96693045015792944583069133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128924060021057259444092177 96693045015792944583069133)
            ·
              refine ⟨36259891880922354218650925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96693045015792944583069133 36259891880922354218650925)
              ·
                refine ⟨13597459455345882831994097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36259891880922354218650925 13597459455345882831994097)
                ·
                  refine ⟨10198094591509412123995573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13597459455345882831994097 10198094591509412123995573)
                  ·
                    refine ⟨956071367954007386624585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10198094591509412123995573 956071367954007386624585)
                    ·
                      rfl

theorem cell23_5585827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 3, 2, 5].length) (baseStart_5585827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5585827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5585827 prefixEnd_5585827 := by exact prefixLift 5585827
  have htrace : WordTrace (prefixWord ++ tailWord_5585827) baseStart_5585827 baseEnd_5585827 := by
    simpa [prefixWord, tailWord_5585827, baseEnd_5585827] using wordTrace_append hprefix tailTrace_5585827
  have hstable : (prefixWord ++ tailWord_5585827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5585827).length < 2 ^ (prefixWord ++ tailWord_5585827).sum := by decide
  have hdescent : baseEnd_5585827 < baseStart_5585827 := by decide
  rcases family_descends (prefixWord ++ tailWord_5585827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5585878 : List Nat := [5, 2, 1, 1, 2, 3, 1, 1, 2, 5]
def baseStart_5585878 : Nat := 118140960795 + 5585878 * 2 ^ 59
def prefixEnd_5585878 : Nat := 4983230072969 + 3 ^ 40 * 5585878 * 2
def baseEnd_5585878 : Nat := 956080097125133820112007

theorem tailTrace_5585878 : CollatzResearch.WordTrace tailWord_5585878 prefixEnd_5585878 956080097125133820112007 := by
  unfold tailWord_5585878
  simp only [CollatzResearch.WordTrace]
  refine ⟨12733356753582842053520393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 135822472038216981904217525 12733356753582842053520393)
  ·
    refine ⟨9550017565187131540140295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12733356753582842053520393 9550017565187131540140295)
    ·
      refine ⟨14325026347780697310210443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9550017565187131540140295 14325026347780697310210443)
      ·
        refine ⟨21487539521671045965315665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14325026347780697310210443 21487539521671045965315665)
        ·
          refine ⟨16115654641253284473986749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21487539521671045965315665 16115654641253284473986749)
          ·
            refine ⟨6043370490469981677745031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16115654641253284473986749 6043370490469981677745031)
            ·
              refine ⟨9065055735704972516617547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6043370490469981677745031 9065055735704972516617547)
              ·
                refine ⟨13597583603557458774926321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9065055735704972516617547 13597583603557458774926321)
                ·
                  refine ⟨10198187702668094081194741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13597583603557458774926321 10198187702668094081194741)
                  ·
                    refine ⟨956080097125133820112007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10198187702668094081194741 956080097125133820112007)
                    ·
                      rfl

theorem cell23_5585878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 1, 2, 5].length) (baseStart_5585878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5585878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5585878 prefixEnd_5585878 := by exact prefixLift 5585878
  have htrace : WordTrace (prefixWord ++ tailWord_5585878) baseStart_5585878 baseEnd_5585878 := by
    simpa [prefixWord, tailWord_5585878, baseEnd_5585878] using wordTrace_append hprefix tailTrace_5585878
  have hstable : (prefixWord ++ tailWord_5585878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5585878).length < 2 ^ (prefixWord ++ tailWord_5585878).sum := by decide
  have hdescent : baseEnd_5585878 < baseStart_5585878 := by decide
  rcases family_descends (prefixWord ++ tailWord_5585878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5585881 : List Nat := [1, 2, 1, 2, 5, 3, 1, 1, 2, 1, 4]
def baseStart_5585881 : Nat := 118140960795 + 5585881 * 2 ^ 59
def prefixEnd_5585881 : Nat := 4983230072969 + 3 ^ 40 * 5585881 * 2
def baseEnd_5585881 : Nat := 2868241831817364948598507

theorem tailTrace_5585881 : CollatzResearch.WordTrace tailWord_5585881 prefixEnd_5585881 2868241831817364948598507 := by
  unfold tailWord_5585881
  simp only [CollatzResearch.WordTrace]
  refine ⟨203733817476314604368685497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135822544984209736245790331 203733817476314604368685497)
  ·
    refine ⟨152800363107235953276514123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203733817476314604368685497 152800363107235953276514123)
    ·
      refine ⟨229200544660853929914771185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152800363107235953276514123 229200544660853929914771185)
      ·
        refine ⟨171900408495640447436078389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 229200544660853929914771185 171900408495640447436078389)
        ·
          refine ⟨16115663296466291947132349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 171900408495640447436078389 16115663296466291947132349)
          ·
            refine ⟨6043373736174859480174631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16115663296466291947132349 6043373736174859480174631)
            ·
              refine ⟨9065060604262289220261947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6043373736174859480174631 9065060604262289220261947)
              ·
                refine ⟨13597590906393433830392921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9065060604262289220261947 13597590906393433830392921)
                ·
                  refine ⟨10198193179795075372794691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13597590906393433830392921 10198193179795075372794691)
                  ·
                    refine ⟨15297289769692613059192037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10198193179795075372794691 15297289769692613059192037)
                    ·
                      refine ⟨2868241831817364948598507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15297289769692613059192037 2868241831817364948598507)
                      ·
                        rfl

theorem cell23_5585881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 1, 2, 1, 4].length) (baseStart_5585881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5585881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5585881 prefixEnd_5585881 := by exact prefixLift 5585881
  have htrace : WordTrace (prefixWord ++ tailWord_5585881) baseStart_5585881 baseEnd_5585881 := by
    simpa [prefixWord, tailWord_5585881, baseEnd_5585881] using wordTrace_append hprefix tailTrace_5585881
  have hstable : (prefixWord ++ tailWord_5585881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5585881).length < 2 ^ (prefixWord ++ tailWord_5585881).sum := by decide
  have hdescent : baseEnd_5585881 < baseStart_5585881 := by decide
  rcases family_descends (prefixWord ++ tailWord_5585881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5585897 : List Nat := [1, 2, 1, 1, 1, 2, 1, 1, 3, 7, 3]
def baseStart_5585897 : Nat := 118140960795 + 5585897 * 2 ^ 59
def prefixEnd_5585897 : Nat := 4983230072969 + 3 ^ 40 * 5585897 * 2
def baseEnd_5585897 : Nat := 2868250047507836885998433

theorem tailTrace_5585897 : CollatzResearch.WordTrace tailWord_5585897 prefixEnd_5585897 2868250047507836885998433 := by
  unfold tailWord_5585897
  simp only [CollatzResearch.WordTrace]
  refine ⟨203734401044256639101267945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135822934029504426067511963 203734401044256639101267945)
  ·
    refine ⟨152800800783192479325950959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203734401044256639101267945 152800800783192479325950959)
    ·
      refine ⟨229201201174788718988926439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152800800783192479325950959 229201201174788718988926439)
      ·
        refine ⟨343801801762183078483389659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229201201174788718988926439 343801801762183078483389659)
        ·
          refine ⟨515702702643274617725084489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 343801801762183078483389659 515702702643274617725084489)
          ·
            refine ⟨386777026982455963293813367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 515702702643274617725084489 386777026982455963293813367)
            ·
              refine ⟨580165540473683944940720051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 386777026982455963293813367 580165540473683944940720051)
              ·
                refine ⟨870248310710525917411080077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 580165540473683944940720051 870248310710525917411080077)
                ·
                  refine ⟨326343116516447219029155029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 870248310710525917411080077 326343116516447219029155029)
                  ·
                    refine ⟨7648666793354231695995821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 326343116516447219029155029 7648666793354231695995821)
                    ·
                      refine ⟨2868250047507836885998433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7648666793354231695995821 2868250047507836885998433)
                      ·
                        rfl

theorem cell23_5585897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 7, 3].length) (baseStart_5585897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5585897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5585897 prefixEnd_5585897 := by exact prefixLift 5585897
  have htrace : WordTrace (prefixWord ++ tailWord_5585897) baseStart_5585897 baseEnd_5585897 := by
    simpa [prefixWord, tailWord_5585897, baseEnd_5585897] using wordTrace_append hprefix tailTrace_5585897
  have hstable : (prefixWord ++ tailWord_5585897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5585897).length < 2 ^ (prefixWord ++ tailWord_5585897).sum := by decide
  have hdescent : baseEnd_5585897 < baseStart_5585897 := by decide
  rcases family_descends (prefixWord ++ tailWord_5585897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5585921 : List Nat := [1, 2, 4, 1, 2, 3, 3, 1, 6]
def baseStart_5585921 : Nat := 118140960795 + 5585921 * 2 ^ 59
def prefixEnd_5585921 : Nat := 4983230072969 + 3 ^ 40 * 5585921 * 2
def baseEnd_5585921 : Nat := 318695819004838310233147

theorem tailTrace_5585921 : CollatzResearch.WordTrace tailWord_5585921 prefixEnd_5585921 318695819004838310233147 := by
  unfold tailWord_5585921
  simp only [CollatzResearch.WordTrace]
  refine ⟨203735276396169691200141617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135823517597446460800094411 203735276396169691200141617)
  ·
    refine ⟨152801457297127268400106213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203735276396169691200141617 152801457297127268400106213)
    ·
      refine ⟨28650273243211362825019915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 152801457297127268400106213 28650273243211362825019915)
      ·
        refine ⟨42975409864817044237529873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28650273243211362825019915 42975409864817044237529873)
        ·
          refine ⟨32231557398612783178147405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42975409864817044237529873 32231557398612783178147405)
          ·
            refine ⟨12086834024479793691805277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32231557398612783178147405 12086834024479793691805277)
            ·
              refine ⟨4532562759179922634426979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12086834024479793691805277 4532562759179922634426979)
              ·
                refine ⟨6798844138769883951640469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4532562759179922634426979 6798844138769883951640469)
                ·
                  refine ⟨318695819004838310233147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6798844138769883951640469 318695819004838310233147)
                  ·
                    rfl

theorem cell23_5585921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 3, 1, 6].length) (baseStart_5585921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5585921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5585921 prefixEnd_5585921 := by exact prefixLift 5585921
  have htrace : WordTrace (prefixWord ++ tailWord_5585921) baseStart_5585921 baseEnd_5585921 := by
    simpa [prefixWord, tailWord_5585921, baseEnd_5585921] using wordTrace_append hprefix tailTrace_5585921
  have hstable : (prefixWord ++ tailWord_5585921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5585921).length < 2 ^ (prefixWord ++ tailWord_5585921).sum := by decide
  have hdescent : baseEnd_5585921 < baseStart_5585921 := by decide
  rcases family_descends (prefixWord ++ tailWord_5585921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5585931 : List Nat := [1, 1, 1, 1, 6, 2, 2, 2, 3, 1, 3]
def baseStart_5585931 : Nat := 118140960795 + 5585931 * 2 ^ 59
def prefixEnd_5585931 : Nat := 4983230072969 + 3 ^ 40 * 5585931 * 2
def baseEnd_5585931 : Nat := 2868267505850089752973277

theorem tailTrace_5585931 : CollatzResearch.WordTrace tailWord_5585931 prefixEnd_5585931 2868267505850089752973277 := by
  unfold tailWord_5585931
  simp only [CollatzResearch.WordTrace]
  refine ⟨203735641126133462908005647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135823760750755641938670431 203735641126133462908005647)
  ·
    refine ⟨305603461689200194362008471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203735641126133462908005647 305603461689200194362008471)
    ·
      refine ⟨458405192533800291543012707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305603461689200194362008471 458405192533800291543012707)
      ·
        refine ⟨687607788800700437314519061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 458405192533800291543012707 687607788800700437314519061)
        ·
          refine ⟨32231615100032832999118081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 687607788800700437314519061 32231615100032832999118081)
          ·
            refine ⟨24173711325024624749338561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32231615100032832999118081 24173711325024624749338561)
            ·
              refine ⟨18130283493768468562003921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24173711325024624749338561 18130283493768468562003921)
              ·
                refine ⟨13597712620326351421502941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18130283493768468562003921 13597712620326351421502941)
                ·
                  refine ⟨5099142232622381783063603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13597712620326351421502941 5099142232622381783063603)
                  ·
                    refine ⟨7648713348933572674595405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5099142232622381783063603 7648713348933572674595405)
                    ·
                      refine ⟨2868267505850089752973277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7648713348933572674595405 2868267505850089752973277)
                      ·
                        rfl

theorem cell23_5585931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 2, 3, 1, 3].length) (baseStart_5585931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5585931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5585931 prefixEnd_5585931 := by exact prefixLift 5585931
  have htrace : WordTrace (prefixWord ++ tailWord_5585931) baseStart_5585931 baseEnd_5585931 := by
    simpa [prefixWord, tailWord_5585931, baseEnd_5585931] using wordTrace_append hprefix tailTrace_5585931
  have hstable : (prefixWord ++ tailWord_5585931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5585931).length < 2 ^ (prefixWord ++ tailWord_5585931).sum := by decide
  have hdescent : baseEnd_5585931 < baseStart_5585931 := by decide
  rcases family_descends (prefixWord ++ tailWord_5585931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5585937 : List Nat := [1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 4]
def baseStart_5585937 : Nat := 118140960795 + 5585937 * 2 ^ 59
def prefixEnd_5585937 : Nat := 4983230072969 + 3 ^ 40 * 5585937 * 2
def baseEnd_5585937 : Nat := 2868270586734016729498249

theorem tailTrace_5585937 : CollatzResearch.WordTrace tailWord_5585937 prefixEnd_5585937 2868270586734016729498249 := by
  unfold tailWord_5585937
  simp only [CollatzResearch.WordTrace]
  refine ⟨203735859964111725932724065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135823906642741150621816043 203735859964111725932724065)
  ·
    refine ⟨152801894973083794449543049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203735859964111725932724065 152801894973083794449543049)
    ·
      refine ⟨114601421229812845837157287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152801894973083794449543049 114601421229812845837157287)
      ·
        refine ⟨171902131844719268755735931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114601421229812845837157287 171902131844719268755735931)
        ·
          refine ⟨257853197767078903133603897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171902131844719268755735931 257853197767078903133603897)
          ·
            refine ⟨193389898325309177350202923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 257853197767078903133603897 193389898325309177350202923)
            ·
              refine ⟨290084847487963766025304385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 193389898325309177350202923 290084847487963766025304385)
              ·
                refine ⟨217563635615972824518978289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 290084847487963766025304385 217563635615972824518978289)
                ·
                  refine ⟨163172726711979618389233717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 217563635615972824518978289 163172726711979618389233717)
                  ·
                    refine ⟨15297443129248089223990661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 163172726711979618389233717 15297443129248089223990661)
                    ·
                      refine ⟨2868270586734016729498249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15297443129248089223990661 2868270586734016729498249)
                      ·
                        rfl

theorem cell23_5585937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 4].length) (baseStart_5585937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5585937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5585937 prefixEnd_5585937 := by exact prefixLift 5585937
  have htrace : WordTrace (prefixWord ++ tailWord_5585937) baseStart_5585937 baseEnd_5585937 := by
    simpa [prefixWord, tailWord_5585937, baseEnd_5585937] using wordTrace_append hprefix tailTrace_5585937
  have hstable : (prefixWord ++ tailWord_5585937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5585937).length < 2 ^ (prefixWord ++ tailWord_5585937).sum := by decide
  have hdescent : baseEnd_5585937 < baseStart_5585937 := by decide
  rcases family_descends (prefixWord ++ tailWord_5585937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5585941 : List Nat := [1, 3, 2, 1, 4, 1, 2, 1, 1, 5, 2]
def baseStart_5585941 : Nat := 118140960795 + 5585941 * 2 ^ 59
def prefixEnd_5585941 : Nat := 4983230072969 + 3 ^ 40 * 5585941 * 2
def baseEnd_5585941 : Nat := 2868272640656634713848231

theorem tailTrace_5585941 : CollatzResearch.WordTrace tailWord_5585941 prefixEnd_5585941 2868272640656634713848231 := by
  unfold tailWord_5585941
  simp only [CollatzResearch.WordTrace]
  refine ⟨203736005856097234615869677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135824003904064823077246451 203736005856097234615869677)
  ·
    refine ⟨76401002196036462980951129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 203736005856097234615869677 76401002196036462980951129)
    ·
      refine ⟨57300751647027347235713347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76401002196036462980951129 57300751647027347235713347)
      ·
        refine ⟨85951127470541020853570021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57300751647027347235713347 85951127470541020853570021)
        ·
          refine ⟨16115836400726441410044379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85951127470541020853570021 16115836400726441410044379)
          ·
            refine ⟨24173754601089662115066569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16115836400726441410044379 24173754601089662115066569)
            ·
              refine ⟨18130315950817246586299927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24173754601089662115066569 18130315950817246586299927)
              ·
                refine ⟨27195473926225869879449891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18130315950817246586299927 27195473926225869879449891)
                ·
                  refine ⟨40793210889338804819174837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27195473926225869879449891 40793210889338804819174837)
                  ·
                    refine ⟨3824363520875512951797641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40793210889338804819174837 3824363520875512951797641)
                    ·
                      refine ⟨2868272640656634713848231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3824363520875512951797641 2868272640656634713848231)
                      ·
                        rfl

theorem cell23_5585941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 1, 1, 5, 2].length) (baseStart_5585941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5585941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5585941 prefixEnd_5585941 := by exact prefixLift 5585941
  have htrace : WordTrace (prefixWord ++ tailWord_5585941) baseStart_5585941 baseEnd_5585941 := by
    simpa [prefixWord, tailWord_5585941, baseEnd_5585941] using wordTrace_append hprefix tailTrace_5585941
  have hstable : (prefixWord ++ tailWord_5585941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5585941).length < 2 ^ (prefixWord ++ tailWord_5585941).sum := by decide
  have hdescent : baseEnd_5585941 < baseStart_5585941 := by decide
  rcases family_descends (prefixWord ++ tailWord_5585941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5585964 : List Nat := [2, 2, 1, 1, 1, 2, 3, 3, 4, 4]
def baseStart_5585964 : Nat := 118140960795 + 5585964 * 2 ^ 59
def prefixEnd_5585964 : Nat := 4983230072969 + 3 ^ 40 * 5585964 * 2
def baseEnd_5585964 : Nat := 956094816903896041286875

theorem tailTrace_5585964 : CollatzResearch.WordTrace tailWord_5585964 prefixEnd_5585964 956094816903896041286875 := by
  unfold tailWord_5585964
  simp only [CollatzResearch.WordTrace]
  refine ⟨101868422367506954771978473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135824563156675939695971297 101868422367506954771978473)
  ·
    refine ⟨76401316775630216078983855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101868422367506954771978473 76401316775630216078983855)
    ·
      refine ⟨114601975163445324118475783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76401316775630216078983855 114601975163445324118475783)
      ·
        refine ⟨171902962745167986177713675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114601975163445324118475783 171902962745167986177713675)
        ·
          refine ⟨257854444117751979266570513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171902962745167986177713675 257854444117751979266570513)
          ·
            refine ⟨193390833088313984449927885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 257854444117751979266570513 193390833088313984449927885)
            ·
              refine ⟨72521562408117744168722957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 193390833088313984449927885 72521562408117744168722957)
              ·
                refine ⟨27195585903044154063271109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72521562408117744168722957 27195585903044154063271109)
                ·
                  refine ⟨5099172356820778886863333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27195585903044154063271109 5099172356820778886863333)
                  ·
                    refine ⟨956094816903896041286875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5099172356820778886863333 956094816903896041286875)
                    ·
                      rfl

theorem cell23_5585964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 4].length) (baseStart_5585964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5585964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5585964 prefixEnd_5585964 := by exact prefixLift 5585964
  have htrace : WordTrace (prefixWord ++ tailWord_5585964) baseStart_5585964 baseEnd_5585964 := by
    simpa [prefixWord, tailWord_5585964, baseEnd_5585964] using wordTrace_append hprefix tailTrace_5585964
  have hstable : (prefixWord ++ tailWord_5585964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5585964).length < 2 ^ (prefixWord ++ tailWord_5585964).sum := by decide
  have hdescent : baseEnd_5585964 < baseStart_5585964 := by decide
  rcases family_descends (prefixWord ++ tailWord_5585964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5585984 : List Nat := [2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 4]
def baseStart_5585984 : Nat := 118140960795 + 5585984 * 2 ^ 59
def prefixEnd_5585984 : Nat := 4983230072969 + 3 ^ 40 * 5585984 * 2
def baseEnd_5585984 : Nat := 2868294720324778045610533

theorem tailTrace_5585984 : CollatzResearch.WordTrace tailWord_5585984 prefixEnd_5585984 2868294720324778045610533 := by
  unfold tailWord_5585984
  simp only [CollatzResearch.WordTrace]
  refine ⟨101868787097470726479842503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135825049463294301973123337 101868787097470726479842503)
  ·
    refine ⟨152803180646206089719763755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101868787097470726479842503 152803180646206089719763755)
    ·
      refine ⟨229204770969309134579645633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152803180646206089719763755 229204770969309134579645633)
      ·
        refine ⟨171903578226981850934734225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 229204770969309134579645633 171903578226981850934734225)
        ·
          refine ⟨128927683670236388201050669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171903578226981850934734225 128927683670236388201050669)
          ·
            refine ⟨48347881376338645575394001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 128927683670236388201050669 48347881376338645575394001)
            ·
              refine ⟨36260911032253984181545501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48347881376338645575394001 36260911032253984181545501)
              ·
                refine ⟨13597841637095244068079563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36260911032253984181545501 13597841637095244068079563)
                ·
                  refine ⟨20396762455642866102119345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13597841637095244068079563 20396762455642866102119345)
                  ·
                    refine ⟨15297571841732149576589509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20396762455642866102119345 15297571841732149576589509)
                    ·
                      refine ⟨2868294720324778045610533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15297571841732149576589509 2868294720324778045610533)
                      ·
                        rfl

theorem cell23_5585984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 4].length) (baseStart_5585984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5585984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5585984 prefixEnd_5585984 := by exact prefixLift 5585984
  have htrace : WordTrace (prefixWord ++ tailWord_5585984) baseStart_5585984 baseEnd_5585984 := by
    simpa [prefixWord, tailWord_5585984, baseEnd_5585984] using wordTrace_append hprefix tailTrace_5585984
  have hstable : (prefixWord ++ tailWord_5585984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5585984).length < 2 ^ (prefixWord ++ tailWord_5585984).sum := by decide
  have hdescent : baseEnd_5585984 < baseStart_5585984 := by decide
  rcases family_descends (prefixWord ++ tailWord_5585984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5585985 : List Nat := [1, 2, 5, 1, 4, 1, 1, 2, 1, 5]
def baseStart_5585985 : Nat := 118140960795 + 5585985 * 2 ^ 59
def prefixEnd_5585985 : Nat := 4983230072969 + 3 ^ 40 * 5585985 * 2
def baseEnd_5585985 : Nat := 956098411268477513899343

theorem tailTrace_5585985 : CollatzResearch.WordTrace tailWord_5585985 prefixEnd_5585985 956098411268477513899343 := by
  unfold tailWord_5585985
  simp only [CollatzResearch.WordTrace]
  refine ⟨203737610667937830130471409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135825073778625220086980939 203737610667937830130471409)
  ·
    refine ⟨152803208000953372597853557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203737610667937830130471409 152803208000953372597853557)
    ·
      refine ⟨14325300750089378681048771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 152803208000953372597853557 14325300750089378681048771)
      ·
        refine ⟨21487951125134068021573157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14325300750089378681048771 21487951125134068021573157)
        ·
          refine ⟨4028990835962637754044967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21487951125134068021573157 4028990835962637754044967)
          ·
            refine ⟨6043486253943956631067451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4028990835962637754044967 6043486253943956631067451)
            ·
              refine ⟨9065229380915934946601177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6043486253943956631067451 9065229380915934946601177)
              ·
                refine ⟨6798922035686951209950883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9065229380915934946601177 6798922035686951209950883)
                ·
                  refine ⟨10198383053530426814926325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6798922035686951209950883 10198383053530426814926325)
                  ·
                    refine ⟨956098411268477513899343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10198383053530426814926325 956098411268477513899343)
                    ·
                      rfl

theorem cell23_5585985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 2, 1, 5].length) (baseStart_5585985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5585985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5585985 prefixEnd_5585985 := by exact prefixLift 5585985
  have htrace : WordTrace (prefixWord ++ tailWord_5585985) baseStart_5585985 baseEnd_5585985 := by
    simpa [prefixWord, tailWord_5585985, baseEnd_5585985] using wordTrace_append hprefix tailTrace_5585985
  have hstable : (prefixWord ++ tailWord_5585985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5585985).length < 2 ^ (prefixWord ++ tailWord_5585985).sum := by decide
  have hdescent : baseEnd_5585985 < baseStart_5585985 := by decide
  rcases family_descends (prefixWord ++ tailWord_5585985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5585991 : List Nat := [1, 1, 4, 1, 3, 3, 1, 1, 3, 2, 3]
def baseStart_5585991 : Nat := 118140960795 + 5585991 * 2 ^ 59
def prefixEnd_5585991 : Nat := 4983230072969 + 3 ^ 40 * 5585991 * 2
def baseEnd_5585991 : Nat := 2868298314689359518223001

theorem tailTrace_5585991 : CollatzResearch.WordTrace tailWord_5585991 prefixEnd_5585991 2868298314689359518223001 := by
  unfold tailWord_5585991
  simp only [CollatzResearch.WordTrace]
  refine ⟨203737829505916093155189827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135825219670610728770126551 203737829505916093155189827)
  ·
    refine ⟨305606744258874139732784741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203737829505916093155189827 305606744258874139732784741)
    ·
      refine ⟨57301264548538901199897139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 305606744258874139732784741 57301264548538901199897139)
      ·
        refine ⟨85951896822808351799845709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57301264548538901199897139 85951896822808351799845709)
        ·
          refine ⟨32231961308553131924942141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85951896822808351799845709 32231961308553131924942141)
          ·
            refine ⟨12086985490707424471853303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32231961308553131924942141 12086985490707424471853303)
            ·
              refine ⟨18130478236061136707779955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12086985490707424471853303 18130478236061136707779955)
              ·
                refine ⟨27195717354091705061669933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18130478236061136707779955 27195717354091705061669933)
                ·
                  refine ⟨10198394007784389398126225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27195717354091705061669933 10198394007784389398126225)
                  ·
                    refine ⟨7648795505838292048594669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10198394007784389398126225 7648795505838292048594669)
                    ·
                      refine ⟨2868298314689359518223001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7648795505838292048594669 2868298314689359518223001)
                      ·
                        rfl

theorem cell23_5585991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 1, 3, 2, 3].length) (baseStart_5585991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5585991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5585991 prefixEnd_5585991 := by exact prefixLift 5585991
  have htrace : WordTrace (prefixWord ++ tailWord_5585991) baseStart_5585991 baseEnd_5585991 := by
    simpa [prefixWord, tailWord_5585991, baseEnd_5585991] using wordTrace_append hprefix tailTrace_5585991
  have hstable : (prefixWord ++ tailWord_5585991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5585991).length < 2 ^ (prefixWord ++ tailWord_5585991).sum := by decide
  have hdescent : baseEnd_5585991 < baseStart_5585991 := by decide
  rcases family_descends (prefixWord ++ tailWord_5585991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5586005 : List Nat := [1, 3, 2, 2, 1, 2, 2, 5, 1, 2, 2]
def baseStart_5586005 : Nat := 118140960795 + 5586005 * 2 ^ 59
def prefixEnd_5586005 : Nat := 4983230072969 + 3 ^ 40 * 5586005 * 2
def baseEnd_5586005 : Nat := 2868305503418522463447937

theorem tailTrace_5586005 : CollatzResearch.WordTrace tailWord_5586005 prefixEnd_5586005 2868305503418522463447937 := by
  unfold tailWord_5586005
  simp only [CollatzResearch.WordTrace]
  refine ⟨203738340127865373546199469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135825560085243582364132979 203738340127865373546199469)
  ·
    refine ⟨76401877547949515079824801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 203738340127865373546199469 76401877547949515079824801)
    ·
      refine ⟨57301408160962136309868601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76401877547949515079824801 57301408160962136309868601)
      ·
        refine ⟨42976056120721602232401451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57301408160962136309868601 42976056120721602232401451)
        ·
          refine ⟨64464084181082403348602177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42976056120721602232401451 64464084181082403348602177)
          ·
            refine ⟨48348063135811802511451633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64464084181082403348602177 48348063135811802511451633)
            ·
              refine ⟨36261047351858851883588725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48348063135811802511451633 36261047351858851883588725)
              ·
                refine ⟨3399473189236767364086443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36261047351858851883588725 3399473189236767364086443)
                ·
                  refine ⟨5099209783855151046129665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3399473189236767364086443 5099209783855151046129665)
                  ·
                    refine ⟨3824407337891363284597249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5099209783855151046129665 3824407337891363284597249)
                    ·
                      refine ⟨2868305503418522463447937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3824407337891363284597249 2868305503418522463447937)
                      ·
                        rfl

theorem cell23_5586005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 5, 1, 2, 2].length) (baseStart_5586005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5586005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5586005 prefixEnd_5586005 := by exact prefixLift 5586005
  have htrace : WordTrace (prefixWord ++ tailWord_5586005) baseStart_5586005 baseEnd_5586005 := by
    simpa [prefixWord, tailWord_5586005, baseEnd_5586005] using wordTrace_append hprefix tailTrace_5586005
  have hstable : (prefixWord ++ tailWord_5586005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5586005).length < 2 ^ (prefixWord ++ tailWord_5586005).sum := by decide
  have hdescent : baseEnd_5586005 < baseStart_5586005 := by decide
  rcases family_descends (prefixWord ++ tailWord_5586005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5586008 : List Nat := [2, 1, 2, 2, 1, 3, 5, 1, 1, 2, 3]
def baseStart_5586008 : Nat := 118140960795 + 5586008 * 2 ^ 59
def prefixEnd_5586008 : Nat := 4983230072969 + 3 ^ 40 * 5586008 * 2
def baseEnd_5586008 : Nat := 2868307043860485951710423

theorem tailTrace_5586008 : CollatzResearch.WordTrace tailWord_5586008 prefixEnd_5586008 2868307043860485951710423 := by
  unfold tailWord_5586008
  simp only [CollatzResearch.WordTrace]
  refine ⟨101869224773427252529279339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135825633031236336705705785 101869224773427252529279339)
  ·
    refine ⟨152803837160140878793919009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101869224773427252529279339 152803837160140878793919009)
    ·
      refine ⟨114602877870105659095439257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152803837160140878793919009 114602877870105659095439257)
      ·
        refine ⟨85952158402579244321579443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114602877870105659095439257 85952158402579244321579443)
        ·
          refine ⟨128928237603868866482369165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85952158402579244321579443 128928237603868866482369165)
          ·
            refine ⟨48348089101450824930888437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 128928237603868866482369165 48348089101450824930888437)
            ·
              refine ⟨4532633353261014837270791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48348089101450824930888437 4532633353261014837270791)
              ·
                refine ⟨6798950029891522255906187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4532633353261014837270791 6798950029891522255906187)
                ·
                  refine ⟨10198425044837283383859281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6798950029891522255906187 10198425044837283383859281)
                  ·
                    refine ⟨7648818783627962537894461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10198425044837283383859281 7648818783627962537894461)
                    ·
                      refine ⟨2868307043860485951710423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7648818783627962537894461 2868307043860485951710423)
                      ·
                        rfl

theorem cell23_5586008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 5, 1, 1, 2, 3].length) (baseStart_5586008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5586008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5586008 prefixEnd_5586008 := by exact prefixLift 5586008
  have htrace : WordTrace (prefixWord ++ tailWord_5586008) baseStart_5586008 baseEnd_5586008 := by
    simpa [prefixWord, tailWord_5586008, baseEnd_5586008] using wordTrace_append hprefix tailTrace_5586008
  have hstable : (prefixWord ++ tailWord_5586008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5586008).length < 2 ^ (prefixWord ++ tailWord_5586008).sum := by decide
  have hdescent : baseEnd_5586008 < baseStart_5586008 := by decide
  rcases family_descends (prefixWord ++ tailWord_5586008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5586031 : List Nat := [1, 1, 2, 1, 3, 3, 1, 1, 5, 3, 2]
def baseStart_5586031 : Nat := 118140960795 + 5586031 * 2 ^ 59
def prefixEnd_5586031 : Nat := 4983230072969 + 3 ^ 40 * 5586031 * 2
def baseEnd_5586031 : Nat := 2868318853915539361722817

theorem tailTrace_5586031 : CollatzResearch.WordTrace tailWord_5586031 prefixEnd_5586031 2868318853915539361722817 := by
  unfold tailWord_5586031
  simp only [CollatzResearch.WordTrace]
  refine ⟨203739288425771179986645947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135826192283847453324430631 203739288425771179986645947)
  ·
    refine ⟨305608932638656769979968921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203739288425771179986645947 305608932638656769979968921)
    ·
      refine ⟨229206699478992577484976691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 305608932638656769979968921 229206699478992577484976691)
      ·
        refine ⟨343810049218488866227465037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229206699478992577484976691 343810049218488866227465037)
        ·
          refine ⟨128928768456933324835299389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 343810049218488866227465037 128928768456933324835299389)
          ·
            refine ⟨48348288171349996813237271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 128928768456933324835299389 48348288171349996813237271)
            ·
              refine ⟨72522432257024995219855907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48348288171349996813237271 72522432257024995219855907)
              ·
                refine ⟨108783648385537492829783861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72522432257024995219855907 108783648385537492829783861)
                ·
                  refine ⟨10198467036144139952792237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 108783648385537492829783861 10198467036144139952792237)
                  ·
                    refine ⟨3824425138554052482297089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10198467036144139952792237 3824425138554052482297089)
                    ·
                      refine ⟨2868318853915539361722817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3824425138554052482297089 2868318853915539361722817)
                      ·
                        rfl

theorem cell23_5586031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 5, 3, 2].length) (baseStart_5586031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5586031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5586031 prefixEnd_5586031 := by exact prefixLift 5586031
  have htrace : WordTrace (prefixWord ++ tailWord_5586031) baseStart_5586031 baseEnd_5586031 := by
    simpa [prefixWord, tailWord_5586031, baseEnd_5586031] using wordTrace_append hprefix tailTrace_5586031
  have hstable : (prefixWord ++ tailWord_5586031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5586031).length < 2 ^ (prefixWord ++ tailWord_5586031).sum := by decide
  have hdescent : baseEnd_5586031 < baseStart_5586031 := by decide
  rcases family_descends (prefixWord ++ tailWord_5586031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5586038 : List Nat := [5, 1, 1, 2, 1, 1, 4, 1, 1, 3, 3]
def baseStart_5586038 : Nat := 118140960795 + 5586038 * 2 ^ 59
def prefixEnd_5586038 : Nat := 4983230072969 + 3 ^ 40 * 5586038 * 2
def baseEnd_5586038 : Nat := 2868322448280120834335285

theorem tailTrace_5586038 : CollatzResearch.WordTrace tailWord_5586038 prefixEnd_5586038 2868322448280120834335285 := by
  unfold tailWord_5586038
  simp only [CollatzResearch.WordTrace]
  refine ⟨12733721483546613761384423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 135826362491163880121433845 12733721483546613761384423)
  ·
    refine ⟨19100582225319920642076635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12733721483546613761384423 19100582225319920642076635)
    ·
      refine ⟨28650873337979880963114953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19100582225319920642076635 28650873337979880963114953)
      ·
        refine ⟨21488155003484910722336215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28650873337979880963114953 21488155003484910722336215)
        ·
          refine ⟨32232232505227366083504323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21488155003484910722336215 32232232505227366083504323)
          ·
            refine ⟨48348348757841049125256485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32232232505227366083504323 48348348757841049125256485)
            ·
              refine ⟨9065315392095196710985591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48348348757841049125256485 9065315392095196710985591)
              ·
                refine ⟨13597973088142795066478387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9065315392095196710985591 13597973088142795066478387)
                ·
                  refine ⟨20396959632214192599717581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13597973088142795066478387 20396959632214192599717581)
                  ·
                    refine ⟨7648859862080322224894093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20396959632214192599717581 7648859862080322224894093)
                    ·
                      refine ⟨2868322448280120834335285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7648859862080322224894093 2868322448280120834335285)
                      ·
                        rfl

theorem cell23_5586038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 1, 1, 3, 3].length) (baseStart_5586038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5586038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5586038 prefixEnd_5586038 := by exact prefixLift 5586038
  have htrace : WordTrace (prefixWord ++ tailWord_5586038) baseStart_5586038 baseEnd_5586038 := by
    simpa [prefixWord, tailWord_5586038, baseEnd_5586038] using wordTrace_append hprefix tailTrace_5586038
  have hstable : (prefixWord ++ tailWord_5586038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5586038).length < 2 ^ (prefixWord ++ tailWord_5586038).sum := by decide
  have hdescent : baseEnd_5586038 < baseStart_5586038 := by decide
  rcases family_descends (prefixWord ++ tailWord_5586038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5586044 : List Nat := [2, 2, 2, 1, 1, 3, 1, 2, 2, 3, 4]
def baseStart_5586044 : Nat := 118140960795 + 5586044 * 2 ^ 59
def prefixEnd_5586044 : Nat := 4983230072969 + 3 ^ 40 * 5586044 * 2
def baseEnd_5586044 : Nat := 2868325529164047810860257

theorem tailTrace_5586044 : CollatzResearch.WordTrace tailWord_5586044 prefixEnd_5586044 2868325529164047810860257 := by
  unfold tailWord_5586044
  simp only [CollatzResearch.WordTrace]
  refine ⟨101869881287362041603434593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135826508383149388804579457 101869881287362041603434593)
  ·
    refine ⟨76402410965521531202575945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101869881287362041603434593 76402410965521531202575945)
    ·
      refine ⟨57301808224141148401931959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76402410965521531202575945 57301808224141148401931959)
      ·
        refine ⟨85952712336211722602897939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57301808224141148401931959 85952712336211722602897939)
        ·
          refine ⟨128929068504317583904346909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85952712336211722602897939 128929068504317583904346909)
          ·
            refine ⟨48348400689119093964130091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 128929068504317583904346909 48348400689119093964130091)
            ·
              refine ⟨72522601033678640946195137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48348400689119093964130091 72522601033678640946195137)
              ·
                refine ⟨54391950775258980709646353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72522601033678640946195137 54391950775258980709646353)
                ·
                  refine ⟨40793963081444235532234765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54391950775258980709646353 40793963081444235532234765)
                  ·
                    refine ⟨15297736155541588324588037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40793963081444235532234765 15297736155541588324588037)
                    ·
                      refine ⟨2868325529164047810860257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15297736155541588324588037 2868325529164047810860257)
                      ·
                        rfl

theorem cell23_5586044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 2, 2, 3, 4].length) (baseStart_5586044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5586044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5586044 prefixEnd_5586044 := by exact prefixLift 5586044
  have htrace : WordTrace (prefixWord ++ tailWord_5586044) baseStart_5586044 baseEnd_5586044 := by
    simpa [prefixWord, tailWord_5586044, baseEnd_5586044] using wordTrace_append hprefix tailTrace_5586044
  have hstable : (prefixWord ++ tailWord_5586044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5586044).length < 2 ^ (prefixWord ++ tailWord_5586044).sum := by decide
  have hdescent : baseEnd_5586044 < baseStart_5586044 := by decide
  rcases family_descends (prefixWord ++ tailWord_5586044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5586064 : List Nat := [2, 1, 1, 1, 1, 1, 4, 2, 1, 6, 3]
def baseStart_5586064 : Nat := 118140960795 + 5586064 * 2 ^ 59
def prefixEnd_5586064 : Nat := 4983230072969 + 3 ^ 40 * 5586064 * 2
def baseEnd_5586064 : Nat := 2868335798777137732610165

theorem tailTrace_5586064 : CollatzResearch.WordTrace tailWord_5586064 prefixEnd_5586064 2868335798777137732610165 := by
  unfold tailWord_5586064
  simp only [CollatzResearch.WordTrace]
  refine ⟨101870246017325813311298623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135826994689767751081731497 101870246017325813311298623)
  ·
    refine ⟨152805369025988719966947935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101870246017325813311298623 152805369025988719966947935)
    ·
      refine ⟨229208053538983079950421903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152805369025988719966947935 229208053538983079950421903)
      ·
        refine ⟨343812080308474619925632855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229208053538983079950421903 343812080308474619925632855)
        ·
          refine ⟨515718120462711929888449283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 343812080308474619925632855 515718120462711929888449283)
          ·
            refine ⟨773577180694067894832673925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 515718120462711929888449283 773577180694067894832673925)
            ·
              refine ⟨145045721380137730281126361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 773577180694067894832673925 145045721380137730281126361)
              ·
                refine ⟨108784291035103297710844771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 145045721380137730281126361 108784291035103297710844771)
                ·
                  refine ⟨163176436552654946566267157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 108784291035103297710844771 163176436552654946566267157)
                  ·
                    refine ⟨7648895463405700620293773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 163176436552654946566267157 7648895463405700620293773)
                    ·
                      refine ⟨2868335798777137732610165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7648895463405700620293773 2868335798777137732610165)
                      ·
                        rfl

theorem cell23_5586064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 1, 6, 3].length) (baseStart_5586064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5586064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5586064 prefixEnd_5586064 := by exact prefixLift 5586064
  have htrace : WordTrace (prefixWord ++ tailWord_5586064) baseStart_5586064 baseEnd_5586064 := by
    simpa [prefixWord, tailWord_5586064, baseEnd_5586064] using wordTrace_append hprefix tailTrace_5586064
  have hstable : (prefixWord ++ tailWord_5586064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5586064).length < 2 ^ (prefixWord ++ tailWord_5586064).sum := by decide
  have hdescent : baseEnd_5586064 < baseStart_5586064 := by decide
  rcases family_descends (prefixWord ++ tailWord_5586064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5586161 : List Nat := [1, 2, 2, 2, 2, 1, 1, 3, 5, 4]
def baseStart_5586161 : Nat := 118140960795 + 5586161 * 2 ^ 59
def prefixEnd_5586161 : Nat := 4983230072969 + 3 ^ 40 * 5586161 * 2
def baseEnd_5586161 : Nat := 956128535466874617699073

theorem tailTrace_5586161 : CollatzResearch.WordTrace tailWord_5586161 prefixEnd_5586161 956128535466874617699073 := by
  unfold tailWord_5586161
  simp only [CollatzResearch.WordTrace]
  refine ⟨203744029915300212188878337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135829353276866808125918891 203744029915300212188878337)
  ·
    refine ⟨152808022436475159141658753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203744029915300212188878337 152808022436475159141658753)
    ·
      refine ⟨114606016827356369356244065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152808022436475159141658753 114606016827356369356244065)
      ·
        refine ⟨85954512620517277017183049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114606016827356369356244065 85954512620517277017183049)
        ·
          refine ⟨64465884465387957762887287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85954512620517277017183049 64465884465387957762887287)
          ·
            refine ⟨96698826698081936644330931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64465884465387957762887287 96698826698081936644330931)
            ·
              refine ⟨145048240047122904966496397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96698826698081936644330931 145048240047122904966496397)
              ·
                refine ⟨54393090017671089362436149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 145048240047122904966496397 54393090017671089362436149)
                ·
                  refine ⟨5099352189156664627728389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54393090017671089362436149 5099352189156664627728389)
                  ·
                    refine ⟨956128535466874617699073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5099352189156664627728389 956128535466874617699073)
                    ·
                      rfl

theorem cell23_5586161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 3, 5, 4].length) (baseStart_5586161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5586161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5586161 prefixEnd_5586161 := by exact prefixLift 5586161
  have htrace : WordTrace (prefixWord ++ tailWord_5586161) baseStart_5586161 baseEnd_5586161 := by
    simpa [prefixWord, tailWord_5586161, baseEnd_5586161] using wordTrace_append hprefix tailTrace_5586161
  have hstable : (prefixWord ++ tailWord_5586161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5586161).length < 2 ^ (prefixWord ++ tailWord_5586161).sum := by decide
  have hdescent : baseEnd_5586161 < baseStart_5586161 := by decide
  rcases family_descends (prefixWord ++ tailWord_5586161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5586188 : List Nat := [2, 2, 1, 2, 2, 3, 2, 2, 2, 2, 3]
def baseStart_5586188 : Nat := 118140960795 + 5586188 * 2 ^ 59
def prefixEnd_5586188 : Nat := 4983230072969 + 3 ^ 40 * 5586188 * 2
def baseEnd_5586188 : Nat := 2868399470378295247459595

theorem tailTrace_5586188 : CollatzResearch.WordTrace tailWord_5586188 prefixEnd_5586188 2868399470378295247459595 := by
  unfold tailWord_5586188
  simp only [CollatzResearch.WordTrace]
  refine ⟨101872507343101197900055609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135830009790801597200074145 101872507343101197900055609)
  ·
    refine ⟨76404380507325898425041707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101872507343101197900055609 76404380507325898425041707)
    ·
      refine ⟨114606570760988847637562561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76404380507325898425041707 114606570760988847637562561)
      ·
        refine ⟨85954928070741635728171921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114606570760988847637562561 85954928070741635728171921)
        ·
          refine ⟨64466196053056226796128941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85954928070741635728171921 64466196053056226796128941)
          ·
            refine ⟨24174823519896085048548353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64466196053056226796128941 24174823519896085048548353)
            ·
              refine ⟨18131117639922063786411265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24174823519896085048548353 18131117639922063786411265)
              ·
                refine ⟨13598338229941547839808449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18131117639922063786411265 13598338229941547839808449)
                ·
                  refine ⟨10198753672456160879856337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13598338229941547839808449 10198753672456160879856337)
                  ·
                    refine ⟨7649065254342120659892253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10198753672456160879856337 7649065254342120659892253)
                    ·
                      refine ⟨2868399470378295247459595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7649065254342120659892253 2868399470378295247459595)
                      ·
                        rfl

theorem cell23_5586188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 2, 2, 2, 3].length) (baseStart_5586188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5586188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5586188 prefixEnd_5586188 := by exact prefixLift 5586188
  have htrace : WordTrace (prefixWord ++ tailWord_5586188) baseStart_5586188 baseEnd_5586188 := by
    simpa [prefixWord, tailWord_5586188, baseEnd_5586188] using wordTrace_append hprefix tailTrace_5586188
  have hstable : (prefixWord ++ tailWord_5586188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5586188).length < 2 ^ (prefixWord ++ tailWord_5586188).sum := by decide
  have hdescent : baseEnd_5586188 < baseStart_5586188 := by decide
  rcases family_descends (prefixWord ++ tailWord_5586188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5586252 : List Nat := [2, 2, 1, 3, 2, 2, 2, 4, 1, 1, 3]
def baseStart_5586252 : Nat := 118140960795 + 5586252 * 2 ^ 59
def prefixEnd_5586252 : Nat := 4983230072969 + 3 ^ 40 * 5586252 * 2
def baseEnd_5586252 : Nat := 2868432333140182997059301

theorem tailTrace_5586252 : CollatzResearch.WordTrace tailWord_5586252 prefixEnd_5586252 2868432333140182997059301 := by
  unfold tailWord_5586252
  simp only [CollatzResearch.WordTrace]
  refine ⟨101873674478985267365220505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135831565971980356486960673 101873674478985267365220505)
  ·
    refine ⟨76405255859238950523915379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101873674478985267365220505 76405255859238950523915379)
    ·
      refine ⟨114607883788858425785873069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76405255859238950523915379 114607883788858425785873069)
      ·
        refine ⟨42977956420821909669702401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114607883788858425785873069 42977956420821909669702401)
        ·
          refine ⟨32233467315616432252276801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42977956420821909669702401 32233467315616432252276801)
          ·
            refine ⟨24175100486712324189207601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32233467315616432252276801 24175100486712324189207601)
            ·
              refine ⟨18131325365034243141905701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24175100486712324189207601 18131325365034243141905701)
              ·
                refine ⟨3399623505943920589107319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18131325365034243141905701 3399623505943920589107319)
                ·
                  refine ⟨5099435258915880883660979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3399623505943920589107319 5099435258915880883660979)
                  ·
                    refine ⟨7649152888373821325491469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5099435258915880883660979 7649152888373821325491469)
                    ·
                      refine ⟨2868432333140182997059301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7649152888373821325491469 2868432333140182997059301)
                      ·
                        rfl

theorem cell23_5586252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 4, 1, 1, 3].length) (baseStart_5586252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5586252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5586252 prefixEnd_5586252 := by exact prefixLift 5586252
  have htrace : WordTrace (prefixWord ++ tailWord_5586252) baseStart_5586252 baseEnd_5586252 := by
    simpa [prefixWord, tailWord_5586252, baseEnd_5586252] using wordTrace_append hprefix tailTrace_5586252
  have hstable : (prefixWord ++ tailWord_5586252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5586252).length < 2 ^ (prefixWord ++ tailWord_5586252).sum := by decide
  have hdescent : baseEnd_5586252 < baseStart_5586252 := by decide
  rcases family_descends (prefixWord ++ tailWord_5586252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5586275 : List Nat := [1, 1, 1, 5, 2, 3, 2, 2, 1, 1, 4]
def baseStart_5586275 : Nat := 118140960795 + 5586275 * 2 ^ 59
def prefixEnd_5586275 : Nat := 4983230072969 + 3 ^ 40 * 5586275 * 2
def baseEnd_5586275 : Nat := 2868444143195236407071695

theorem tailTrace_5586275 : CollatzResearch.WordTrace tailWord_5586275 prefixEnd_5586275 2868444143195236407071695 := by
  unfold tailWord_5586275
  simp only [CollatzResearch.WordTrace]
  refine ⟨203748187836887209658528279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135832125224591473105685519 203748187836887209658528279)
  ·
    refine ⟨305622281755330814487792419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203748187836887209658528279 305622281755330814487792419)
    ·
      refine ⟨458433422632996221731688629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305622281755330814487792419 458433422632996221731688629)
      ·
        refine ⟨42978133371843395787345809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 458433422632996221731688629 42978133371843395787345809)
        ·
          refine ⟨32233600028882546840509357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42978133371843395787345809 32233600028882546840509357)
          ·
            refine ⟨12087600010830955065191009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32233600028882546840509357 12087600010830955065191009)
            ·
              refine ⟨9065700008123216298893257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12087600010830955065191009 9065700008123216298893257)
              ·
                refine ⟨6799275006092412224169943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9065700008123216298893257 6799275006092412224169943)
                ·
                  refine ⟨10198912509138618336254915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6799275006092412224169943 10198912509138618336254915)
                  ·
                    refine ⟨15298368763707927504382373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10198912509138618336254915 15298368763707927504382373)
                    ·
                      refine ⟨2868444143195236407071695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15298368763707927504382373 2868444143195236407071695)
                      ·
                        rfl

theorem cell23_5586275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 2, 1, 1, 4].length) (baseStart_5586275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5586275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5586275 prefixEnd_5586275 := by exact prefixLift 5586275
  have htrace : WordTrace (prefixWord ++ tailWord_5586275) baseStart_5586275 baseEnd_5586275 := by
    simpa [prefixWord, tailWord_5586275, baseEnd_5586275] using wordTrace_append hprefix tailTrace_5586275
  have hstable : (prefixWord ++ tailWord_5586275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5586275).length < 2 ^ (prefixWord ++ tailWord_5586275).sum := by decide
  have hdescent : baseEnd_5586275 < baseStart_5586275 := by decide
  rcases family_descends (prefixWord ++ tailWord_5586275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5586321 : List Nat := [1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 5]
def baseStart_5586321 : Nat := 118140960795 + 5586321 * 2 ^ 59
def prefixEnd_5586321 : Nat := 4983230072969 + 3 ^ 40 * 5586321 * 2
def baseEnd_5586321 : Nat := 2868467763305343227096483

theorem tailTrace_5586321 : CollatzResearch.WordTrace tailWord_5586321 prefixEnd_5586321 2868467763305343227096483 := by
  unfold tailWord_5586321
  simp only [CollatzResearch.WordTrace]
  refine ⟨203749865594720559514702817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135833243729813706343135211 203749865594720559514702817)
  ·
    refine ⟨152812399196040419636027113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203749865594720559514702817 152812399196040419636027113)
    ·
      refine ⟨114609299397030314727020335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152812399196040419636027113 114609299397030314727020335)
      ·
        refine ⟨171913949095545472090530503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114609299397030314727020335 171913949095545472090530503)
        ·
          refine ⟨257870923643318208135795755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171913949095545472090530503 257870923643318208135795755)
          ·
            refine ⟨386806385464977312203693633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 257870923643318208135795755 386806385464977312203693633)
            ·
              refine ⟨290104789098732984152770225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 386806385464977312203693633 290104789098732984152770225)
              ·
                refine ⟨217578591824049738114577669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 290104789098732984152770225 217578591824049738114577669)
                ·
                  refine ⟨40795985967009325896483313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 217578591824049738114577669 40795985967009325896483313)
                  ·
                    refine ⟨30596989475256994422362485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40795985967009325896483313 30596989475256994422362485)
                    ·
                      refine ⟨2868467763305343227096483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30596989475256994422362485 2868467763305343227096483)
                      ·
                        rfl

theorem cell23_5586321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 5].length) (baseStart_5586321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5586321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5586321 prefixEnd_5586321 := by exact prefixLift 5586321
  have htrace : WordTrace (prefixWord ++ tailWord_5586321) baseStart_5586321 baseEnd_5586321 := by
    simpa [prefixWord, tailWord_5586321, baseEnd_5586321] using wordTrace_append hprefix tailTrace_5586321
  have hstable : (prefixWord ++ tailWord_5586321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5586321).length < 2 ^ (prefixWord ++ tailWord_5586321).sum := by decide
  have hdescent : baseEnd_5586321 < baseStart_5586321 := by decide
  rcases family_descends (prefixWord ++ tailWord_5586321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5586331 : List Nat := [1, 1, 1, 1, 1, 1, 2, 1, 5, 5, 4]
def baseStart_5586331 : Nat := 118140960795 + 5586331 * 2 ^ 59
def prefixEnd_5586331 : Nat := 4983230072969 + 3 ^ 40 * 5586331 * 2
def baseEnd_5586331 : Nat := 2868472898111888187971437

theorem tailTrace_5586331 : CollatzResearch.WordTrace tailWord_5586331 prefixEnd_5586331 2868472898111888187971437 := by
  unfold tailWord_5586331
  simp only [CollatzResearch.WordTrace]
  refine ⟨203750230324684331222566847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135833486883122887481711231 203750230324684331222566847)
  ·
    refine ⟨305625345487026496833850271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203750230324684331222566847 305625345487026496833850271)
    ·
      refine ⟨458438018230539745250775407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305625345487026496833850271 458438018230539745250775407)
      ·
        refine ⟨687657027345809617876163111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 458438018230539745250775407 687657027345809617876163111)
        ·
          refine ⟨1031485541018714426814244667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 687657027345809617876163111 1031485541018714426814244667)
          ·
            refine ⟨1547228311528071640221367001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1031485541018714426814244667 1547228311528071640221367001)
            ·
              refine ⟨1160421233646053730166025251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1547228311528071640221367001 1160421233646053730166025251)
              ·
                refine ⟨1740631850469080595249037877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1160421233646053730166025251 1740631850469080595249037877)
                ·
                  refine ⟨163184235981476305804597301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1740631850469080595249037877 163184235981476305804597301)
                  ·
                    refine ⟨15298522123263403669180997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 163184235981476305804597301 15298522123263403669180997)
                    ·
                      refine ⟨2868472898111888187971437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15298522123263403669180997 2868472898111888187971437)
                      ·
                        rfl

theorem cell23_5586331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 5, 4].length) (baseStart_5586331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5586331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5586331 prefixEnd_5586331 := by exact prefixLift 5586331
  have htrace : WordTrace (prefixWord ++ tailWord_5586331) baseStart_5586331 baseEnd_5586331 := by
    simpa [prefixWord, tailWord_5586331, baseEnd_5586331] using wordTrace_append hprefix tailTrace_5586331
  have hstable : (prefixWord ++ tailWord_5586331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5586331).length < 2 ^ (prefixWord ++ tailWord_5586331).sum := by decide
  have hdescent : baseEnd_5586331 < baseStart_5586331 := by decide
  rcases family_descends (prefixWord ++ tailWord_5586331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5586341 : List Nat := [1, 3, 1, 2, 1, 1, 2, 1, 3, 8]
def baseStart_5586341 : Nat := 118140960795 + 5586341 * 2 ^ 59
def prefixEnd_5586341 : Nat := 4983230072969 + 3 ^ 40 * 5586341 * 2
def baseEnd_5586341 : Nat := 956159344306144382948797

theorem tailTrace_5586341 : CollatzResearch.WordTrace tailWord_5586341 prefixEnd_5586341 956159344306144382948797 := by
  unfold tailWord_5586341
  simp only [CollatzResearch.WordTrace]
  refine ⟨203750595054648102930430877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135833730036432068620287251 203750595054648102930430877)
  ·
    refine ⟨76406473145493038598911579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 203750595054648102930430877 76406473145493038598911579)
    ·
      refine ⟨114609709718239557898367369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76406473145493038598911579 114609709718239557898367369)
      ·
        refine ⟨85957282288679668423775527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114609709718239557898367369 85957282288679668423775527)
        ·
          refine ⟨128935923433019502635663291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85957282288679668423775527 128935923433019502635663291)
          ·
            refine ⟨193403885149529253953494937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128935923433019502635663291 193403885149529253953494937)
            ·
              refine ⟨145052913862146940465121203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 193403885149529253953494937 145052913862146940465121203)
              ·
                refine ⟨217579370793220410697681805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 145052913862146940465121203 217579370793220410697681805)
                ·
                  refine ⟨81592264047457654011630677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 217579370793220410697681805 81592264047457654011630677)
                  ·
                    refine ⟨956159344306144382948797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 81592264047457654011630677 956159344306144382948797)
                    ·
                      rfl

theorem cell23_5586341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 3, 8].length) (baseStart_5586341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5586341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5586341 prefixEnd_5586341 := by exact prefixLift 5586341
  have htrace : WordTrace (prefixWord ++ tailWord_5586341) baseStart_5586341 baseEnd_5586341 := by
    simpa [prefixWord, tailWord_5586341, baseEnd_5586341] using wordTrace_append hprefix tailTrace_5586341
  have hstable : (prefixWord ++ tailWord_5586341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5586341).length < 2 ^ (prefixWord ++ tailWord_5586341).sum := by decide
  have hdescent : baseEnd_5586341 < baseStart_5586341 := by decide
  rcases family_descends (prefixWord ++ tailWord_5586341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5586365 : List Nat := [1, 4, 1, 2, 2, 1, 1, 2, 3, 4, 2]
def baseStart_5586365 : Nat := 118140960795 + 5586365 * 2 ^ 59
def prefixEnd_5586365 : Nat := 4983230072969 + 3 ^ 40 * 5586365 * 2
def baseEnd_5586365 : Nat := 2868490356454141054946281

theorem tailTrace_5586365 : CollatzResearch.WordTrace tailWord_5586365 prefixEnd_5586365 2868490356454141054946281 := by
  unfold tailWord_5586365
  simp only [CollatzResearch.WordTrace]
  refine ⟨203751470406561155029304549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135834313604374103352869699 203751470406561155029304549)
  ·
    refine ⟨38203400701230216567994603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 203751470406561155029304549 38203400701230216567994603)
    ·
      refine ⟨57305101051845324851991905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38203400701230216567994603 57305101051845324851991905)
      ·
        refine ⟨42978825788883993638993929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57305101051845324851991905 42978825788883993638993929)
        ·
          refine ⟨32234119341662995229245447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42978825788883993638993929 32234119341662995229245447)
          ·
            refine ⟨48351179012494492843868171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32234119341662995229245447 48351179012494492843868171)
            ·
              refine ⟨72526768518741739265802257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48351179012494492843868171 72526768518741739265802257)
              ·
                refine ⟨54395076389056304449351693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72526768518741739265802257 54395076389056304449351693)
                ·
                  refine ⟨20398153645896114168506885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54395076389056304449351693 20398153645896114168506885)
                  ·
                    refine ⟨3824653808605521406595041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20398153645896114168506885 3824653808605521406595041)
                    ·
                      refine ⟨2868490356454141054946281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3824653808605521406595041 2868490356454141054946281)
                      ·
                        rfl

theorem cell23_5586365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 2, 3, 4, 2].length) (baseStart_5586365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5586365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5586365 prefixEnd_5586365 := by exact prefixLift 5586365
  have htrace : WordTrace (prefixWord ++ tailWord_5586365) baseStart_5586365 baseEnd_5586365 := by
    simpa [prefixWord, tailWord_5586365, baseEnd_5586365] using wordTrace_append hprefix tailTrace_5586365
  have hstable : (prefixWord ++ tailWord_5586365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5586365).length < 2 ^ (prefixWord ++ tailWord_5586365).sum := by decide
  have hdescent : baseEnd_5586365 < baseStart_5586365 := by decide
  rcases family_descends (prefixWord ++ tailWord_5586365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5586368 : List Nat := [2, 1, 1, 2, 3, 1, 3, 1, 2, 4, 3]
def baseStart_5586368 : Nat := 118140960795 + 5586368 * 2 ^ 59
def prefixEnd_5586368 : Nat := 4983230072969 + 3 ^ 40 * 5586368 * 2
def baseEnd_5586368 : Nat := 2868491896896104543208767

theorem tailTrace_5586368 : CollatzResearch.WordTrace tailWord_5586368 prefixEnd_5586368 2868491896896104543208767 := by
  unfold tailWord_5586368
  simp only [CollatzResearch.WordTrace]
  refine ⟨101875789912775143270831879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135834386550366857694442505 101875789912775143270831879)
  ·
    refine ⟨152813684869162714906247819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101875789912775143270831879 152813684869162714906247819)
    ·
      refine ⟨229220527303744072359371729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152813684869162714906247819 229220527303744072359371729)
      ·
        refine ⟨171915395477808054269528797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 229220527303744072359371729 171915395477808054269528797)
        ·
          refine ⟨64468273304178020351073299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 171915395477808054269528797 64468273304178020351073299)
          ·
            refine ⟨96702409956267030526609949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64468273304178020351073299 96702409956267030526609949)
            ·
              refine ⟨36263403733600136447478731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96702409956267030526609949 36263403733600136447478731)
              ·
                refine ⟨54395105600400204671218097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36263403733600136447478731 54395105600400204671218097)
                ·
                  refine ⟨40796329200300153503413573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54395105600400204671218097 40796329200300153503413573)
                  ·
                    refine ⟨7649311725056278781890045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40796329200300153503413573 7649311725056278781890045)
                    ·
                      refine ⟨2868491896896104543208767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7649311725056278781890045 2868491896896104543208767)
                      ·
                        rfl

theorem cell23_5586368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 1, 2, 4, 3].length) (baseStart_5586368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5586368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5586368 prefixEnd_5586368 := by exact prefixLift 5586368
  have htrace : WordTrace (prefixWord ++ tailWord_5586368) baseStart_5586368 baseEnd_5586368 := by
    simpa [prefixWord, tailWord_5586368, baseEnd_5586368] using wordTrace_append hprefix tailTrace_5586368
  have hstable : (prefixWord ++ tailWord_5586368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5586368).length < 2 ^ (prefixWord ++ tailWord_5586368).sum := by decide
  have hdescent : baseEnd_5586368 < baseStart_5586368 := by decide
  rcases family_descends (prefixWord ++ tailWord_5586368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5586378 : List Nat := [3, 1, 2, 1, 2, 3, 1, 1, 1, 4, 4]
def baseStart_5586378 : Nat := 118140960795 + 5586378 * 2 ^ 59
def prefixEnd_5586378 : Nat := 4983230072969 + 3 ^ 40 * 5586378 * 2
def baseEnd_5586378 : Nat := 2868497031702649504083721

theorem tailTrace_5586378 : CollatzResearch.WordTrace tailWord_5586378 prefixEnd_5586378 2868497031702649504083721 := by
  unfold tailWord_5586378
  simp only [CollatzResearch.WordTrace]
  refine ⟨50937986138878514562381947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135834629703676038833018525 50937986138878514562381947)
  ·
    refine ⟨76406979208317771843572921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50937986138878514562381947 76406979208317771843572921)
    ·
      refine ⟨57305234406238328882679691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76406979208317771843572921 57305234406238328882679691)
      ·
        refine ⟨85957851609357493324019537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57305234406238328882679691 85957851609357493324019537)
        ·
          refine ⟨64468388707018119993014653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85957851609357493324019537 64468388707018119993014653)
          ·
            refine ⟨24175645765131794997380495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64468388707018119993014653 24175645765131794997380495)
            ·
              refine ⟨36263468647697692496070743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24175645765131794997380495 36263468647697692496070743)
              ·
                refine ⟨54395202971546538744106115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36263468647697692496070743 54395202971546538744106115)
                ·
                  refine ⟨81592804457319808116159173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54395202971546538744106115 81592804457319808116159173)
                  ·
                    refine ⟨15298650835747464021779845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 81592804457319808116159173 15298650835747464021779845)
                    ·
                      refine ⟨2868497031702649504083721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15298650835747464021779845 2868497031702649504083721)
                      ·
                        rfl

theorem cell23_5586378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 1, 1, 4, 4].length) (baseStart_5586378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5586378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5586378 prefixEnd_5586378 := by exact prefixLift 5586378
  have htrace : WordTrace (prefixWord ++ tailWord_5586378) baseStart_5586378 baseEnd_5586378 := by
    simpa [prefixWord, tailWord_5586378, baseEnd_5586378] using wordTrace_append hprefix tailTrace_5586378
  have hstable : (prefixWord ++ tailWord_5586378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5586378).length < 2 ^ (prefixWord ++ tailWord_5586378).sum := by decide
  have hdescent : baseEnd_5586378 < baseStart_5586378 := by decide
  rcases family_descends (prefixWord ++ tailWord_5586378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5586422 : List Nat := [5, 1, 1, 1, 2, 2, 2, 4, 5]
def baseStart_5586422 : Nat := 118140960795 + 5586422 * 2 ^ 59
def prefixEnd_5586422 : Nat := 4983230072969 + 3 ^ 40 * 5586422 * 2
def baseEnd_5586422 : Nat := 318724402761271925770391

theorem tailTrace_5586422 : CollatzResearch.WordTrace tailWord_5586422 prefixEnd_5586422 318724402761271925770391 := by
  unfold tailWord_5586422
  simp only [CollatzResearch.WordTrace]
  refine ⟨12734596835459665860258095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 135835699578236435842753013 12734596835459665860258095)
  ·
    refine ⟨19101895253189498790387143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12734596835459665860258095 19101895253189498790387143)
    ·
      refine ⟨28652842879784248185580715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19101895253189498790387143 28652842879784248185580715)
      ·
        refine ⟨42979264319676372278371073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28652842879784248185580715 42979264319676372278371073)
        ·
          refine ⟨32234448239757279208778305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42979264319676372278371073 32234448239757279208778305)
          ·
            refine ⟨24175836179817959406583729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32234448239757279208778305 24175836179817959406583729)
            ·
              refine ⟨18131877134863469554937797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24175836179817959406583729 18131877134863469554937797)
              ·
                refine ⟨3399726962786900541550837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18131877134863469554937797 3399726962786900541550837)
                ·
                  refine ⟨318724402761271925770391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3399726962786900541550837 318724402761271925770391)
                  ·
                    rfl

theorem cell23_5586422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 4, 5].length) (baseStart_5586422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5586422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5586422 prefixEnd_5586422 := by exact prefixLift 5586422
  have htrace : WordTrace (prefixWord ++ tailWord_5586422) baseStart_5586422 baseEnd_5586422 := by
    simpa [prefixWord, tailWord_5586422, baseEnd_5586422] using wordTrace_append hprefix tailTrace_5586422
  have hstable : (prefixWord ++ tailWord_5586422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5586422).length < 2 ^ (prefixWord ++ tailWord_5586422).sum := by decide
  have hdescent : baseEnd_5586422 < baseStart_5586422 := by decide
  rcases family_descends (prefixWord ++ tailWord_5586422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5586428 : List Nat := [2, 2, 2, 1, 2, 1, 2, 3, 1, 2, 5]
def baseStart_5586428 : Nat := 118140960795 + 5586428 * 2 ^ 59
def prefixEnd_5586428 : Nat := 4983230072969 + 3 ^ 40 * 5586428 * 2
def baseEnd_5586428 : Nat := 2868522705735374308458491

theorem tailTrace_5586428 : CollatzResearch.WordTrace tailWord_5586428 prefixEnd_5586428 2868522705735374308458491 := by
  unfold tailWord_5586428
  simp only [CollatzResearch.WordTrace]
  refine ⟨101876884102666458394423969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135835845470221944525898625 101876884102666458394423969)
  ·
    refine ⟨76407663076999843795817977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101876884102666458394423969 76407663076999843795817977)
    ·
      refine ⟨57305747307749882846863483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76407663076999843795817977 57305747307749882846863483)
      ·
        refine ⟨85958620961624824270295225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57305747307749882846863483 85958620961624824270295225)
        ·
          refine ⟨64468965721218618202721419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85958620961624824270295225 64468965721218618202721419)
          ·
            refine ⟨96703448581827927304082129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64468965721218618202721419 96703448581827927304082129)
            ·
              refine ⟨72527586436370945478061597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96703448581827927304082129 72527586436370945478061597)
              ·
                refine ⟨27197844913639104554273099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72527586436370945478061597 27197844913639104554273099)
                ·
                  refine ⟨40796767370458656831409649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27197844913639104554273099 40796767370458656831409649)
                  ·
                    refine ⟨30597575527843992623557237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40796767370458656831409649 30597575527843992623557237)
                    ·
                      refine ⟨2868522705735374308458491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30597575527843992623557237 2868522705735374308458491)
                      ·
                        rfl

theorem cell23_5586428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 3, 1, 2, 5].length) (baseStart_5586428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5586428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5586428 prefixEnd_5586428 := by exact prefixLift 5586428
  have htrace : WordTrace (prefixWord ++ tailWord_5586428) baseStart_5586428 baseEnd_5586428 := by
    simpa [prefixWord, tailWord_5586428, baseEnd_5586428] using wordTrace_append hprefix tailTrace_5586428
  have hstable : (prefixWord ++ tailWord_5586428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5586428).length < 2 ^ (prefixWord ++ tailWord_5586428).sum := by decide
  have hdescent : baseEnd_5586428 < baseStart_5586428 := by decide
  rcases family_descends (prefixWord ++ tailWord_5586428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5586458 : List Nat := [3, 1, 1, 3, 1, 1, 1, 2, 2, 3, 5]
def baseStart_5586458 : Nat := 118140960795 + 5586458 * 2 ^ 59
def prefixEnd_5586458 : Nat := 4983230072969 + 3 ^ 40 * 5586458 * 2
def baseEnd_5586458 : Nat := 2868538110155009191083353

theorem tailTrace_5586458 : CollatzResearch.WordTrace tailWord_5586458 prefixEnd_5586458 2868538110155009191083353 := by
  unfold tailWord_5586458
  simp only [CollatzResearch.WordTrace]
  refine ⟨50938715598806057978110007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135836574930149487941626685 50938715598806057978110007)
  ·
    refine ⟨76408073398209086967165011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50938715598806057978110007 76408073398209086967165011)
    ·
      refine ⟨114612110097313630450747517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76408073398209086967165011 114612110097313630450747517)
      ·
        refine ⟨42979541286492611419030319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114612110097313630450747517 42979541286492611419030319)
        ·
          refine ⟨64469311929738917128545479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42979541286492611419030319 64469311929738917128545479)
          ·
            refine ⟨96703967894608375692818219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64469311929738917128545479 96703967894608375692818219)
            ·
              refine ⟨145055951841912563539227329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96703967894608375692818219 145055951841912563539227329)
              ·
                refine ⟨108791963881434422654420497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 145055951841912563539227329 108791963881434422654420497)
                ·
                  refine ⟨81593972911075816990815373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 108791963881434422654420497 81593972911075816990815373)
                  ·
                    refine ⟨30597739841653431371555765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 81593972911075816990815373 30597739841653431371555765)
                    ·
                      refine ⟨2868538110155009191083353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30597739841653431371555765 2868538110155009191083353)
                      ·
                        rfl

theorem cell23_5586458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_5586458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5586458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5586458 prefixEnd_5586458 := by exact prefixLift 5586458
  have htrace : WordTrace (prefixWord ++ tailWord_5586458) baseStart_5586458 baseEnd_5586458 := by
    simpa [prefixWord, tailWord_5586458, baseEnd_5586458] using wordTrace_append hprefix tailTrace_5586458
  have hstable : (prefixWord ++ tailWord_5586458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5586458).length < 2 ^ (prefixWord ++ tailWord_5586458).sum := by decide
  have hdescent : baseEnd_5586458 < baseStart_5586458 := by decide
  rcases family_descends (prefixWord ++ tailWord_5586458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5586495 : List Nat := [1, 1, 2, 2, 3, 4, 1, 3, 6]
def baseStart_5586495 : Nat := 118140960795 + 5586495 * 2 ^ 59
def prefixEnd_5586495 : Nat := 4983230072969 + 3 ^ 40 * 5586495 * 2
def baseEnd_5586495 : Nat := 318728567659913949591187

theorem tailTrace_5586495 : CollatzResearch.WordTrace tailWord_5586495 prefixEnd_5586495 318728567659913949591187 := by
  unfold tailWord_5586495
  simp only [CollatzResearch.WordTrace]
  refine ⟨203756211896090187231536939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135837474597393458154357959 203756211896090187231536939)
  ·
    refine ⟨305634317844135280847305409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203756211896090187231536939 305634317844135280847305409)
    ·
      refine ⟨229225738383101460635479057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 305634317844135280847305409 229225738383101460635479057)
      ·
        refine ⟨171919303787326095476609293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 229225738383101460635479057 171919303787326095476609293)
        ·
          refine ⟨64469738920247285803728485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 171919303787326095476609293 64469738920247285803728485)
          ·
            refine ⟨12088076047546366088199091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64469738920247285803728485 12088076047546366088199091)
            ·
              refine ⟨18132114071319549132298637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12088076047546366088199091 18132114071319549132298637)
              ·
                refine ⟨6799542776744830924611989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18132114071319549132298637 6799542776744830924611989)
                ·
                  refine ⟨318728567659913949591187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6799542776744830924611989 318728567659913949591187)
                  ·
                    rfl

theorem cell23_5586495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 3, 6].length) (baseStart_5586495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5586495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5586495 prefixEnd_5586495 := by exact prefixLift 5586495
  have htrace : WordTrace (prefixWord ++ tailWord_5586495) baseStart_5586495 baseEnd_5586495 := by
    simpa [prefixWord, tailWord_5586495, baseEnd_5586495] using wordTrace_append hprefix tailTrace_5586495
  have hstable : (prefixWord ++ tailWord_5586495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5586495).length < 2 ^ (prefixWord ++ tailWord_5586495).sum := by decide
  have hdescent : baseEnd_5586495 < baseStart_5586495 := by decide
  rcases family_descends (prefixWord ++ tailWord_5586495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5586555 : List Nat := [1, 1, 1, 1, 1, 4, 6, 1, 1, 6]
def baseStart_5586555 : Nat := 118140960795 + 5586555 * 2 ^ 59
def prefixEnd_5586555 : Nat := 4983230072969 + 3 ^ 40 * 5586555 * 2
def baseEnd_5586555 : Nat := 956195972592831770523469

theorem tailTrace_5586555 : CollatzResearch.WordTrace tailWord_5586555 prefixEnd_5586555 956195972592831770523469 := by
  unfold tailWord_5586555
  simp only [CollatzResearch.WordTrace]
  refine ⟨203758400275872817478721119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135838933517248544985814079 203758400275872817478721119)
  ·
    refine ⟨305637600413809226218081679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203758400275872817478721119 305637600413809226218081679)
    ·
      refine ⟨458456400620713839327122519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305637600413809226218081679 458456400620713839327122519)
      ·
        refine ⟨687684600931070758990683779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 458456400620713839327122519 687684600931070758990683779)
        ·
          refine ⟨1031526901396606138486025669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 687684600931070758990683779 1031526901396606138486025669)
          ·
            refine ⟨193411294011863650966129813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1031526901396606138486025669 193411294011863650966129813)
            ·
              refine ⟨9066154406806108639037335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 193411294011863650966129813 9066154406806108639037335)
              ·
                refine ⟨13599231610209162958556003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9066154406806108639037335 13599231610209162958556003)
                ·
                  refine ⟨20398847415313744437834005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13599231610209162958556003 20398847415313744437834005)
                  ·
                    refine ⟨956195972592831770523469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20398847415313744437834005 956195972592831770523469)
                    ·
                      rfl

theorem cell23_5586555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 1, 1, 6].length) (baseStart_5586555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5586555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5586555 prefixEnd_5586555 := by exact prefixLift 5586555
  have htrace : WordTrace (prefixWord ++ tailWord_5586555) baseStart_5586555 baseEnd_5586555 := by
    simpa [prefixWord, tailWord_5586555, baseEnd_5586555] using wordTrace_append hprefix tailTrace_5586555
  have hstable : (prefixWord ++ tailWord_5586555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5586555).length < 2 ^ (prefixWord ++ tailWord_5586555).sum := by decide
  have hdescent : baseEnd_5586555 < baseStart_5586555 := by decide
  rcases family_descends (prefixWord ++ tailWord_5586555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5586596 : List Nat := [2, 3, 1, 2, 2, 3, 2, 1, 3, 2, 2]
def baseStart_5586596 : Nat := 118140960795 + 5586596 * 2 ^ 59
def prefixEnd_5586596 : Nat := 4983230072969 + 3 ^ 40 * 5586596 * 2
def baseEnd_5586596 : Nat := 2868608970485329651157719

theorem tailTrace_5586596 : CollatzResearch.WordTrace tailWord_5586596 prefixEnd_5586596 2868608970485329651157719 := by
  unfold tailWord_5586596
  simp only [CollatzResearch.WordTrace]
  refine ⟨101879947834362140740481821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135839930445816187653975761 101879947834362140740481821)
  ·
    refine ⟨38204980437885802777680683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101879947834362140740481821 38204980437885802777680683)
    ·
      refine ⟨57307470656828704166521025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38204980437885802777680683 57307470656828704166521025)
      ·
        refine ⟨42980602992621528124890769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57307470656828704166521025 42980602992621528124890769)
        ·
          refine ⟨32235452244466146093668077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42980602992621528124890769 32235452244466146093668077)
          ·
            refine ⟨12088294591674804785125529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32235452244466146093668077 12088294591674804785125529)
            ·
              refine ⟨9066220943756103588844147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12088294591674804785125529 9066220943756103588844147)
              ·
                refine ⟨13599331415634155383266221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9066220943756103588844147 13599331415634155383266221)
                ·
                  refine ⟨5099749280862808268724833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13599331415634155383266221 5099749280862808268724833)
                  ·
                    refine ⟨3824811960647106201543625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5099749280862808268724833 3824811960647106201543625)
                    ·
                      refine ⟨2868608970485329651157719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3824811960647106201543625 2868608970485329651157719)
                      ·
                        rfl

theorem cell23_5586596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 1, 3, 2, 2].length) (baseStart_5586596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5586596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5586596 prefixEnd_5586596 := by exact prefixLift 5586596
  have htrace : WordTrace (prefixWord ++ tailWord_5586596) baseStart_5586596 baseEnd_5586596 := by
    simpa [prefixWord, tailWord_5586596, baseEnd_5586596] using wordTrace_append hprefix tailTrace_5586596
  have hstable : (prefixWord ++ tailWord_5586596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5586596).length < 2 ^ (prefixWord ++ tailWord_5586596).sum := by decide
  have hdescent : baseEnd_5586596 < baseStart_5586596 := by decide
  rcases family_descends (prefixWord ++ tailWord_5586596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5586606 : List Nat := [4, 1, 4, 1, 2, 2, 1, 1, 1, 6]
def baseStart_5586606 : Nat := 118140960795 + 5586606 * 2 ^ 59
def prefixEnd_5586606 : Nat := 4983230072969 + 3 ^ 40 * 5586606 * 2
def baseEnd_5586606 : Nat := 956204701763958204010891

theorem tailTrace_5586606 : CollatzResearch.WordTrace tailWord_5586606 prefixEnd_5586606 956204701763958204010891 := by
  unfold tailWord_5586606
  simp only [CollatzResearch.WordTrace]
  refine ⟨25470032549836006648603459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135840173599125368792551781 25470032549836006648603459)
  ·
    refine ⟨38205048824754009972905189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25470032549836006648603459 38205048824754009972905189)
    ·
      refine ⟨7163446654641376869919723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38205048824754009972905189 7163446654641376869919723)
      ·
        refine ⟨10745169981962065304879585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7163446654641376869919723 10745169981962065304879585)
        ·
          refine ⟨8058877486471548978659689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10745169981962065304879585 8058877486471548978659689)
          ·
            refine ⟨6044158114853661733994767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8058877486471548978659689 6044158114853661733994767)
            ·
              refine ⟨9066237172280492600992151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6044158114853661733994767 9066237172280492600992151)
              ·
                refine ⟨13599355758420738901488227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9066237172280492600992151 13599355758420738901488227)
                ·
                  refine ⟨20399033637631108352232341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13599355758420738901488227 20399033637631108352232341)
                  ·
                    refine ⟨956204701763958204010891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20399033637631108352232341 956204701763958204010891)
                    ·
                      rfl

theorem cell23_5586606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_5586606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5586606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5586606 prefixEnd_5586606 := by exact prefixLift 5586606
  have htrace : WordTrace (prefixWord ++ tailWord_5586606) baseStart_5586606 baseEnd_5586606 := by
    simpa [prefixWord, tailWord_5586606, baseEnd_5586606] using wordTrace_append hprefix tailTrace_5586606
  have hstable : (prefixWord ++ tailWord_5586606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5586606).length < 2 ^ (prefixWord ++ tailWord_5586606).sum := by decide
  have hdescent : baseEnd_5586606 < baseStart_5586606 := by decide
  rcases family_descends (prefixWord ++ tailWord_5586606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5586655 : List Nat := [1, 1, 2, 3, 2, 2, 1, 2, 1, 3, 5]
def baseStart_5586655 : Nat := 118140960795 + 5586655 * 2 ^ 59
def prefixEnd_5586655 : Nat := 4983230072969 + 3 ^ 40 * 5586655 * 2
def baseEnd_5586655 : Nat := 2868639265843944920319947

theorem tailTrace_5586655 : CollatzResearch.WordTrace tailWord_5586655 prefixEnd_5586655 2868639265843944920319947 := by
  unfold tailWord_5586655
  simp only [CollatzResearch.WordTrace]
  refine ⟨203762047575510534557361419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135841365050340356371574279 203762047575510534557361419)
  ·
    refine ⟨305643071363265801836042129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203762047575510534557361419 305643071363265801836042129)
    ·
      refine ⟨229232303522449351377031597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 305643071363265801836042129 229232303522449351377031597)
      ·
        refine ⟨85962113820918506766386849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 229232303522449351377031597 85962113820918506766386849)
        ·
          refine ⟨64471585365688880074790137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85962113820918506766386849 64471585365688880074790137)
          ·
            refine ⟨48353689024266660056092603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64471585365688880074790137 48353689024266660056092603)
            ·
              refine ⟨72530533536399990084138905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48353689024266660056092603 72530533536399990084138905)
              ·
                refine ⟨54397900152299992563104179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72530533536399990084138905 54397900152299992563104179)
                ·
                  refine ⟨81596850228449988844656269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54397900152299992563104179 81596850228449988844656269)
                  ·
                    refine ⟨30598818835668745816746101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 81596850228449988844656269 30598818835668745816746101)
                    ·
                      refine ⟨2868639265843944920319947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30598818835668745816746101 2868639265843944920319947)
                      ·
                        rfl

theorem cell23_5586655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 2, 1, 3, 5].length) (baseStart_5586655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5586655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5586655 prefixEnd_5586655 := by exact prefixLift 5586655
  have htrace : WordTrace (prefixWord ++ tailWord_5586655) baseStart_5586655 baseEnd_5586655 := by
    simpa [prefixWord, tailWord_5586655, baseEnd_5586655] using wordTrace_append hprefix tailTrace_5586655
  have hstable : (prefixWord ++ tailWord_5586655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5586655).length < 2 ^ (prefixWord ++ tailWord_5586655).sum := by decide
  have hdescent : baseEnd_5586655 < baseStart_5586655 := by decide
  rcases family_descends (prefixWord ++ tailWord_5586655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5586663 : List Nat := [1, 1, 5, 4, 1, 1, 1, 3, 2, 1, 3]
def baseStart_5586663 : Nat := 118140960795 + 5586663 * 2 ^ 59
def prefixEnd_5586663 : Nat := 4983230072969 + 3 ^ 40 * 5586663 * 2
def baseEnd_5586663 : Nat := 2868643373689180889019911

theorem tailTrace_5586663 : CollatzResearch.WordTrace tailWord_5586663 prefixEnd_5586663 2868643373689180889019911 := by
  unfold tailWord_5586663
  simp only [CollatzResearch.WordTrace]
  refine ⟨203762339359481551923652643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135841559572987701282435095 203762339359481551923652643)
  ·
    refine ⟨305643509039222327885478965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203762339359481551923652643 305643509039222327885478965)
    ·
      refine ⟨28654078972427093239263653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 305643509039222327885478965 28654078972427093239263653)
      ·
        refine ⟨5372639807330079982361935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28654078972427093239263653 5372639807330079982361935)
        ·
          refine ⟨8058959710995119973542903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5372639807330079982361935 8058959710995119973542903)
          ·
            refine ⟨12088439566492679960314355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8058959710995119973542903 12088439566492679960314355)
            ·
              refine ⟨18132659349739019940471533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12088439566492679960314355 18132659349739019940471533)
              ·
                refine ⟨6799747256152132477676825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18132659349739019940471533 6799747256152132477676825)
                ·
                  refine ⟨5099810442114099358257619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6799747256152132477676825 5099810442114099358257619)
                  ·
                    refine ⟨7649715663171149037386429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5099810442114099358257619 7649715663171149037386429)
                    ·
                      refine ⟨2868643373689180889019911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7649715663171149037386429 2868643373689180889019911)
                      ·
                        rfl

theorem cell23_5586663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_5586663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5586663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5586663 prefixEnd_5586663 := by exact prefixLift 5586663
  have htrace : WordTrace (prefixWord ++ tailWord_5586663) baseStart_5586663 baseEnd_5586663 := by
    simpa [prefixWord, tailWord_5586663, baseEnd_5586663] using wordTrace_append hprefix tailTrace_5586663
  have hstable : (prefixWord ++ tailWord_5586663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5586663).length < 2 ^ (prefixWord ++ tailWord_5586663).sum := by decide
  have hdescent : baseEnd_5586663 < baseStart_5586663 := by decide
  rcases family_descends (prefixWord ++ tailWord_5586663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5586665 : List Nat := [1, 2, 1, 1, 1, 2, 3, 3, 1, 4, 4]
def baseStart_5586665 : Nat := 118140960795 + 5586665 * 2 ^ 59
def prefixEnd_5586665 : Nat := 4983230072969 + 3 ^ 40 * 5586665 * 2
def baseEnd_5586665 : Nat := 2868644400650489881194901

theorem tailTrace_5586665 : CollatzResearch.WordTrace tailWord_5586665 prefixEnd_5586665 2868644400650489881194901 := by
  unfold tailWord_5586665
  simp only [CollatzResearch.WordTrace]
  refine ⟨203762412305474306265225449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135841608203649537510150299 203762412305474306265225449)
  ·
    refine ⟨152821809229105729698919087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203762412305474306265225449 152821809229105729698919087)
    ·
      refine ⟨229232713843658594548378631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152821809229105729698919087 229232713843658594548378631)
      ·
        refine ⟨343849070765487891822567947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229232713843658594548378631 343849070765487891822567947)
        ·
          refine ⟨515773606148231837733851921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 343849070765487891822567947 515773606148231837733851921)
          ·
            refine ⟨386830204611173878300388941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 515773606148231837733851921 386830204611173878300388941)
            ·
              refine ⟨145061326729190204362645853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 386830204611173878300388941 145061326729190204362645853)
              ·
                refine ⟨54397997523446326635992195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 145061326729190204362645853 54397997523446326635992195)
                ·
                  refine ⟨81596996285169489953988293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54397997523446326635992195 81596996285169489953988293)
                  ·
                    refine ⟨15299436803469279366372805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 81596996285169489953988293 15299436803469279366372805)
                    ·
                      refine ⟨2868644400650489881194901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15299436803469279366372805 2868644400650489881194901)
                      ·
                        rfl

theorem cell23_5586665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 3, 1, 4, 4].length) (baseStart_5586665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5586665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5586665 prefixEnd_5586665 := by exact prefixLift 5586665
  have htrace : WordTrace (prefixWord ++ tailWord_5586665) baseStart_5586665 baseEnd_5586665 := by
    simpa [prefixWord, tailWord_5586665, baseEnd_5586665] using wordTrace_append hprefix tailTrace_5586665
  have hstable : (prefixWord ++ tailWord_5586665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5586665).length < 2 ^ (prefixWord ++ tailWord_5586665).sum := by decide
  have hdescent : baseEnd_5586665 < baseStart_5586665 := by decide
  rcases family_descends (prefixWord ++ tailWord_5586665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5586675 : List Nat := [1, 1, 1, 2, 2, 3, 2, 4, 7]
def baseStart_5586675 : Nat := 118140960795 + 5586675 * 2 ^ 59
def prefixEnd_5586675 : Nat := 4983230072969 + 3 ^ 40 * 5586675 * 2
def baseEnd_5586675 : Nat := 318738837273003871341095

theorem tailTrace_5586675 : CollatzResearch.WordTrace tailWord_5586675 prefixEnd_5586675 318738837273003871341095 := by
  unfold tailWord_5586675
  simp only [CollatzResearch.WordTrace]
  refine ⟨203762777035438077973089479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135841851356958718648726319 203762777035438077973089479)
  ·
    refine ⟨305644165553157116959634219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203762777035438077973089479 305644165553157116959634219)
    ·
      refine ⟨458466248329735675439451329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305644165553157116959634219 458466248329735675439451329)
      ·
        refine ⟨343849686247301756579588497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 458466248329735675439451329 343849686247301756579588497)
        ·
          refine ⟨257887264685476317434691373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 343849686247301756579588497 257887264685476317434691373)
          ·
            refine ⟨96707724257053619038009265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 257887264685476317434691373 96707724257053619038009265)
            ·
              refine ⟨72530793192790214278506949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96707724257053619038009265 72530793192790214278506949)
              ·
                refine ⟨13599523723648165177220053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72530793192790214278506949 13599523723648165177220053)
                ·
                  refine ⟨318738837273003871341095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13599523723648165177220053 318738837273003871341095)
                  ·
                    rfl

theorem cell23_5586675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 4, 7].length) (baseStart_5586675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5586675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5586675 prefixEnd_5586675 := by exact prefixLift 5586675
  have htrace : WordTrace (prefixWord ++ tailWord_5586675) baseStart_5586675 baseEnd_5586675 := by
    simpa [prefixWord, tailWord_5586675, baseEnd_5586675] using wordTrace_append hprefix tailTrace_5586675
  have hstable : (prefixWord ++ tailWord_5586675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5586675).length < 2 ^ (prefixWord ++ tailWord_5586675).sum := by decide
  have hdescent : baseEnd_5586675 < baseStart_5586675 := by decide
  rcases family_descends (prefixWord ++ tailWord_5586675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5586685 : List Nat := [1, 4, 1, 1, 1, 1, 2, 2, 1, 2, 7]
def baseStart_5586685 : Nat := 118140960795 + 5586685 * 2 ^ 59
def prefixEnd_5586685 : Nat := 4983230072969 + 3 ^ 40 * 5586685 * 2
def baseEnd_5586685 : Nat := 2868654670263579802944809

theorem tailTrace_5586685 : CollatzResearch.WordTrace tailWord_5586685 prefixEnd_5586685 2868654670263579802944809 := by
  unfold tailWord_5586685
  simp only [CollatzResearch.WordTrace]
  refine ⟨203763141765401849680953509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135842094510267899787302339 203763141765401849680953509)
  ·
    refine ⟨38205589081012846815178783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 203763141765401849680953509 38205589081012846815178783)
    ·
      refine ⟨57308383621519270222768175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38205589081012846815178783 57308383621519270222768175)
      ·
        refine ⟨85962575432278905334152263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57308383621519270222768175 85962575432278905334152263)
        ·
          refine ⟨128943863148418358001228395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85962575432278905334152263 128943863148418358001228395)
          ·
            refine ⟨193415794722627537001842593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128943863148418358001228395 193415794722627537001842593)
            ·
              refine ⟨145061846041970652751381945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 193415794722627537001842593 145061846041970652751381945)
              ·
                refine ⟨108796384531477989563536459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 145061846041970652751381945 108796384531477989563536459)
                ·
                  refine ⟨163194576797216984345304689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 108796384531477989563536459 163194576797216984345304689)
                  ·
                    refine ⟨122395932597912738258978517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 163194576797216984345304689 122395932597912738258978517)
                    ·
                      refine ⟨2868654670263579802944809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 122395932597912738258978517 2868654670263579802944809)
                      ·
                        rfl

theorem cell23_5586685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 2, 7].length) (baseStart_5586685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5586685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5586685 prefixEnd_5586685 := by exact prefixLift 5586685
  have htrace : WordTrace (prefixWord ++ tailWord_5586685) baseStart_5586685 baseEnd_5586685 := by
    simpa [prefixWord, tailWord_5586685, baseEnd_5586685] using wordTrace_append hprefix tailTrace_5586685
  have hstable : (prefixWord ++ tailWord_5586685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5586685).length < 2 ^ (prefixWord ++ tailWord_5586685).sum := by decide
  have hdescent : baseEnd_5586685 < baseStart_5586685 := by decide
  rcases family_descends (prefixWord ++ tailWord_5586685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5586705 : List Nat := [1, 2, 2, 1, 1, 3, 1, 2, 3, 7]
def baseStart_5586705 : Nat := 118140960795 + 5586705 * 2 ^ 59
def prefixEnd_5586705 : Nat := 4983230072969 + 3 ^ 40 * 5586705 * 2
def baseEnd_5586705 : Nat := 956221646625556574898239

theorem tailTrace_5586705 : CollatzResearch.WordTrace tailWord_5586705 prefixEnd_5586705 956221646625556574898239 := by
  unfold tailWord_5586705
  simp only [CollatzResearch.WordTrace]
  refine ⟨203763871225329393096681569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135842580816886262064454379 203763871225329393096681569)
  ·
    refine ⟨152822903418997044822511177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203763871225329393096681569 152822903418997044822511177)
    ·
      refine ⟨114617177564247783616883383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152822903418997044822511177 114617177564247783616883383)
      ·
        refine ⟨171925766346371675425325075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114617177564247783616883383 171925766346371675425325075)
        ·
          refine ⟨257888649519557513137987613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171925766346371675425325075 257888649519557513137987613)
          ·
            refine ⟨96708243569834067426745355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 257888649519557513137987613 96708243569834067426745355)
            ·
              refine ⟨145062365354751101140118033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96708243569834067426745355 145062365354751101140118033)
              ·
                refine ⟨108796774016063325855088525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 145062365354751101140118033 108796774016063325855088525)
                ·
                  refine ⟨40798790256023747195658197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 108796774016063325855088525 40798790256023747195658197)
                  ·
                    refine ⟨956221646625556574898239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40798790256023747195658197 956221646625556574898239)
                    ·
                      rfl

theorem cell23_5586705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 7].length) (baseStart_5586705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5586705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5586705 prefixEnd_5586705 := by exact prefixLift 5586705
  have htrace : WordTrace (prefixWord ++ tailWord_5586705) baseStart_5586705 baseEnd_5586705 := by
    simpa [prefixWord, tailWord_5586705, baseEnd_5586705] using wordTrace_append hprefix tailTrace_5586705
  have hstable : (prefixWord ++ tailWord_5586705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5586705).length < 2 ^ (prefixWord ++ tailWord_5586705).sum := by decide
  have hdescent : baseEnd_5586705 < baseStart_5586705 := by decide
  rcases family_descends (prefixWord ++ tailWord_5586705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5586709 : List Nat := [1, 3, 2, 1, 2, 4, 1, 4, 5]
def baseStart_5586709 : Nat := 118140960795 + 5586709 * 2 ^ 59
def prefixEnd_5586709 : Nat := 4983230072969 + 3 ^ 40 * 5586709 * 2
def baseEnd_5586709 : Nat := 318740777088809745449411

theorem tailTrace_5586709 : CollatzResearch.WordTrace tailWord_5586709 prefixEnd_5586709 318740777088809745449411 := by
  unfold tailWord_5586709
  simp only [CollatzResearch.WordTrace]
  refine ⟨203764017117314901779827181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135842678078209934519884787 203764017117314901779827181)
  ·
    refine ⟨76411506418993088167435193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 203764017117314901779827181 76411506418993088167435193)
    ·
      refine ⟨57308629814244816125576395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76411506418993088167435193 57308629814244816125576395)
      ·
        refine ⟨85962944721367224188364593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57308629814244816125576395 85962944721367224188364593)
        ·
          refine ⟨64472208541025418141273445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85962944721367224188364593 64472208541025418141273445)
          ·
            refine ⟨12088539101442265901488771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64472208541025418141273445 12088539101442265901488771)
            ·
              refine ⟨18132808652163398852233157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12088539101442265901488771 18132808652163398852233157)
              ·
                refine ⟨3399901622280637284793717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18132808652163398852233157 3399901622280637284793717)
                ·
                  refine ⟨318740777088809745449411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3399901622280637284793717 318740777088809745449411)
                  ·
                    rfl

theorem cell23_5586709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 4, 5].length) (baseStart_5586709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5586709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5586709 prefixEnd_5586709 := by exact prefixLift 5586709
  have htrace : WordTrace (prefixWord ++ tailWord_5586709) baseStart_5586709 baseEnd_5586709 := by
    simpa [prefixWord, tailWord_5586709, baseEnd_5586709] using wordTrace_append hprefix tailTrace_5586709
  have hstable : (prefixWord ++ tailWord_5586709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5586709).length < 2 ^ (prefixWord ++ tailWord_5586709).sum := by decide
  have hdescent : baseEnd_5586709 < baseStart_5586709 := by decide
  rcases family_descends (prefixWord ++ tailWord_5586709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5586722 : List Nat := [3, 3, 1, 1, 2, 1, 2, 2, 1, 7]
def baseStart_5586722 : Nat := 118140960795 + 5586722 * 2 ^ 59
def prefixEnd_5586722 : Nat := 4983230072969 + 3 ^ 40 * 5586722 * 2
def baseEnd_5586722 : Nat := 956224556349265386060713

theorem tailTrace_5586722 : CollatzResearch.WordTrace tailWord_5586722 prefixEnd_5586722 956224556349265386060713 := by
  unfold tailWord_5586722
  simp only [CollatzResearch.WordTrace]
  refine ⟨50941122816566951250012605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135842994177511870000033613 50941122816566951250012605)
  ·
    refine ⟨19102921056212606718754727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50941122816566951250012605 19102921056212606718754727)
    ·
      refine ⟨28654381584318910078132091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19102921056212606718754727 28654381584318910078132091)
      ·
        refine ⟨42981572376478365117198137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28654381584318910078132091 42981572376478365117198137)
        ·
          refine ⟨32236179282358773837898603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42981572376478365117198137 32236179282358773837898603)
          ·
            refine ⟨48354268923538160756847905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32236179282358773837898603 48354268923538160756847905)
            ·
              refine ⟨36265701692653620567635929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48354268923538160756847905 36265701692653620567635929)
              ·
                refine ⟨27199276269490215425726947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36265701692653620567635929 27199276269490215425726947)
                ·
                  refine ⟨40798914404235323138590421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27199276269490215425726947 40798914404235323138590421)
                  ·
                    refine ⟨956224556349265386060713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40798914404235323138590421 956224556349265386060713)
                    ·
                      rfl

theorem cell23_5586722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 2, 1, 7].length) (baseStart_5586722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5586722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5586722 prefixEnd_5586722 := by exact prefixLift 5586722
  have htrace : WordTrace (prefixWord ++ tailWord_5586722) baseStart_5586722 baseEnd_5586722 := by
    simpa [prefixWord, tailWord_5586722, baseEnd_5586722] using wordTrace_append hprefix tailTrace_5586722
  have hstable : (prefixWord ++ tailWord_5586722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5586722).length < 2 ^ (prefixWord ++ tailWord_5586722).sum := by decide
  have hdescent : baseEnd_5586722 < baseStart_5586722 := by decide
  rcases family_descends (prefixWord ++ tailWord_5586722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5586735 : List Nat := [1, 1, 2, 1, 2, 1, 2, 3, 2, 8]
def baseStart_5586735 : Nat := 118140960795 + 5586735 * 2 ^ 59
def prefixEnd_5586735 : Nat := 4983230072969 + 3 ^ 40 * 5586735 * 2
def baseEnd_5586735 : Nat := 956226781432101535773193

theorem tailTrace_5586735 : CollatzResearch.WordTrace tailWord_5586735 prefixEnd_5586735 956226781432101535773193 := by
  unfold tailWord_5586735
  simp only [CollatzResearch.WordTrace]
  refine ⟨203764965415220708220273659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135843310276813805480182439 203764965415220708220273659)
  ·
    refine ⟨305647448122831062330410489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203764965415220708220273659 305647448122831062330410489)
    ·
      refine ⟨229235586092123296747807867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 305647448122831062330410489 229235586092123296747807867)
      ·
        refine ⟨343853379138184945121711801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229235586092123296747807867 343853379138184945121711801)
        ·
          refine ⟨257890034353638708841283851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 343853379138184945121711801 257890034353638708841283851)
          ·
            refine ⟨386835051530458063261925777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 257890034353638708841283851 386835051530458063261925777)
            ·
              refine ⟨290126288647843547446444333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 386835051530458063261925777 290126288647843547446444333)
              ·
                refine ⟨108797358242941330292416625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 290126288647843547446444333 108797358242941330292416625)
                ·
                  refine ⟨81598018682205997719312469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 108797358242941330292416625 81598018682205997719312469)
                  ·
                    refine ⟨956226781432101535773193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 81598018682205997719312469 956226781432101535773193)
                    ·
                      rfl

theorem cell23_5586735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 2, 8].length) (baseStart_5586735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5586735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5586735 prefixEnd_5586735 := by exact prefixLift 5586735
  have htrace : WordTrace (prefixWord ++ tailWord_5586735) baseStart_5586735 baseEnd_5586735 := by
    simpa [prefixWord, tailWord_5586735, baseEnd_5586735] using wordTrace_append hprefix tailTrace_5586735
  have hstable : (prefixWord ++ tailWord_5586735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5586735).length < 2 ^ (prefixWord ++ tailWord_5586735).sum := by decide
  have hdescent : baseEnd_5586735 < baseStart_5586735 := by decide
  rcases family_descends (prefixWord ++ tailWord_5586735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5586759 : List Nat := [1, 1, 4, 1, 2, 1, 3, 2, 2, 4, 2]
def baseStart_5586759 : Nat := 118140960795 + 5586759 * 2 ^ 59
def prefixEnd_5586759 : Nat := 4983230072969 + 3 ^ 40 * 5586759 * 2
def baseEnd_5586759 : Nat := 2868692667832012513419469

theorem tailTrace_5586759 : CollatzResearch.WordTrace tailWord_5586759 prefixEnd_5586759 2868692667832012513419469 := by
  unfold tailWord_5586759
  simp only [CollatzResearch.WordTrace]
  refine ⟨203765840767133760319147331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135843893844755840212764887 203765840767133760319147331)
  ·
    refine ⟨305648761150700640478720997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203765840767133760319147331 305648761150700640478720997)
    ·
      refine ⟨57309142715756370089760187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 305648761150700640478720997 57309142715756370089760187)
      ·
        refine ⟨85963714073634555134640281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57309142715756370089760187 85963714073634555134640281)
        ·
          refine ⟨64472785555225916350980211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85963714073634555134640281 64472785555225916350980211)
          ·
            refine ⟨96709178332838874526470317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64472785555225916350980211 96709178332838874526470317)
            ·
              refine ⟨36265941874814577947426369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96709178332838874526470317 36265941874814577947426369)
              ·
                refine ⟨27199456406110933460569777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36265941874814577947426369 27199456406110933460569777)
                ·
                  refine ⟨20399592304583200095427333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27199456406110933460569777 20399592304583200095427333)
                  ·
                    refine ⟨3824923557109350017892625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20399592304583200095427333 3824923557109350017892625)
                    ·
                      refine ⟨2868692667832012513419469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3824923557109350017892625 2868692667832012513419469)
                      ·
                        rfl

theorem cell23_5586759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 2, 2, 4, 2].length) (baseStart_5586759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5586759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5586759 prefixEnd_5586759 := by exact prefixLift 5586759
  have htrace : WordTrace (prefixWord ++ tailWord_5586759) baseStart_5586759 baseEnd_5586759 := by
    simpa [prefixWord, tailWord_5586759, baseEnd_5586759] using wordTrace_append hprefix tailTrace_5586759
  have hstable : (prefixWord ++ tailWord_5586759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5586759).length < 2 ^ (prefixWord ++ tailWord_5586759).sum := by decide
  have hdescent : baseEnd_5586759 < baseStart_5586759 := by decide
  rcases family_descends (prefixWord ++ tailWord_5586759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5586769 : List Nat := [1, 2, 2, 1, 5, 1, 1, 3, 3, 4]
def baseStart_5586769 : Nat := 118140960795 + 5586769 * 2 ^ 59
def prefixEnd_5586769 : Nat := 4983230072969 + 3 ^ 40 * 5586769 * 2
def baseEnd_5586769 : Nat := 956232600879519158098141

theorem tailTrace_5586769 : CollatzResearch.WordTrace tailWord_5586769 prefixEnd_5586769 956232600879519158098141 := by
  unfold tailWord_5586769
  simp only [CollatzResearch.WordTrace]
  refine ⟨203766205497097532027011361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135844136998065021351340907 203766205497097532027011361)
  ·
    refine ⟨152824654122823149020258521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203766205497097532027011361 152824654122823149020258521)
    ·
      refine ⟨114618490592117361765193891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152824654122823149020258521 114618490592117361765193891)
      ·
        refine ⟨171927735888176042647790837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114618490592117361765193891 171927735888176042647790837)
        ·
          refine ⟨16118225239516503998230391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 171927735888176042647790837 16118225239516503998230391)
          ·
            refine ⟨24177337859274755997345587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16118225239516503998230391 24177337859274755997345587)
            ·
              refine ⟨36266006788912133996018381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24177337859274755997345587 36266006788912133996018381)
              ·
                refine ⟨13599752545842050248506893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36266006788912133996018381 13599752545842050248506893)
                ·
                  refine ⟨5099907204690768843190085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13599752545842050248506893 5099907204690768843190085)
                  ·
                    refine ⟨956232600879519158098141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5099907204690768843190085 956232600879519158098141)
                    ·
                      rfl

theorem cell23_5586769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 3, 3, 4].length) (baseStart_5586769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5586769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5586769 prefixEnd_5586769 := by exact prefixLift 5586769
  have htrace : WordTrace (prefixWord ++ tailWord_5586769) baseStart_5586769 baseEnd_5586769 := by
    simpa [prefixWord, tailWord_5586769, baseEnd_5586769] using wordTrace_append hprefix tailTrace_5586769
  have hstable : (prefixWord ++ tailWord_5586769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5586769).length < 2 ^ (prefixWord ++ tailWord_5586769).sum := by decide
  have hdescent : baseEnd_5586769 < baseStart_5586769 := by decide
  rcases family_descends (prefixWord ++ tailWord_5586769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5586786 : List Nat := [3, 3, 2, 1, 2, 1, 2, 2, 3, 4]
def baseStart_5586786 : Nat := 118140960795 + 5586786 * 2 ^ 59
def prefixEnd_5586786 : Nat := 4983230072969 + 3 ^ 40 * 5586786 * 2
def baseEnd_5586786 : Nat := 956235510603227969260615

theorem tailTrace_5586786 : CollatzResearch.WordTrace tailWord_5586786 prefixEnd_5586786 956235510603227969260615 := by
  unfold tailWord_5586786
  simp only [CollatzResearch.WordTrace]
  refine ⟨50941706384508985982595053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135844550358690629286920141 50941706384508985982595053)
  ·
    refine ⟨19103139894190869743473145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50941706384508985982595053 19103139894190869743473145)
    ·
      refine ⟨14327354920643152307604859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19103139894190869743473145 14327354920643152307604859)
      ·
        refine ⟨21491032380964728461407289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14327354920643152307604859 21491032380964728461407289)
        ·
          refine ⟨16118274285723546346055467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21491032380964728461407289 16118274285723546346055467)
          ·
            refine ⟨24177411428585319519083201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16118274285723546346055467 24177411428585319519083201)
            ·
              refine ⟨18133058571438989639312401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24177411428585319519083201 18133058571438989639312401)
              ·
                refine ⟨13599793928579242229484301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18133058571438989639312401 13599793928579242229484301)
                ·
                  refine ⟨5099922723217215836056613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13599793928579242229484301 5099922723217215836056613)
                  ·
                    refine ⟨956235510603227969260615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5099922723217215836056613 956235510603227969260615)
                    ·
                      rfl

theorem cell23_5586786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 2, 3, 4].length) (baseStart_5586786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5586786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5586786 prefixEnd_5586786 := by exact prefixLift 5586786
  have htrace : WordTrace (prefixWord ++ tailWord_5586786) baseStart_5586786 baseEnd_5586786 := by
    simpa [prefixWord, tailWord_5586786, baseEnd_5586786] using wordTrace_append hprefix tailTrace_5586786
  have hstable : (prefixWord ++ tailWord_5586786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5586786).length < 2 ^ (prefixWord ++ tailWord_5586786).sum := by decide
  have hdescent : baseEnd_5586786 < baseStart_5586786 := by decide
  rcases family_descends (prefixWord ++ tailWord_5586786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5586812 : List Nat := [2, 2, 2, 1, 1, 1, 1, 1, 7, 5]
def baseStart_5586812 : Nat := 118140960795 + 5586812 * 2 ^ 59
def prefixEnd_5586812 : Nat := 4983230072969 + 3 ^ 40 * 5586812 * 2
def baseEnd_5586812 : Nat := 956239960768900268685575

theorem tailTrace_5586812 : CollatzResearch.WordTrace tailWord_5586812 prefixEnd_5586812 956239960768900268685575 := by
  unfold tailWord_5586812
  simp only [CollatzResearch.WordTrace]
  refine ⟨101883886917970875185413345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135845182557294500247217793 101883886917970875185413345)
  ·
    refine ⟨76412915188478156389060009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101883886917970875185413345 76412915188478156389060009)
    ·
      refine ⟨57309686391358617291795007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76412915188478156389060009 57309686391358617291795007)
      ·
        refine ⟨85964529587037925937692511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57309686391358617291795007 85964529587037925937692511)
        ·
          refine ⟨128946794380556888906538767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85964529587037925937692511 128946794380556888906538767)
          ·
            refine ⟨193420191570835333359808151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128946794380556888906538767 193420191570835333359808151)
            ·
              refine ⟨290130287356253000039712227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 193420191570835333359808151 290130287356253000039712227)
              ·
                refine ⟨435195431034379500059568341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 290130287356253000039712227 435195431034379500059568341)
                ·
                  refine ⟨10199892914868269532646133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 435195431034379500059568341 10199892914868269532646133)
                  ·
                    refine ⟨956239960768900268685575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10199892914868269532646133 956239960768900268685575)
                    ·
                      rfl

theorem cell23_5586812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 7, 5].length) (baseStart_5586812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5586812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5586812 prefixEnd_5586812 := by exact prefixLift 5586812
  have htrace : WordTrace (prefixWord ++ tailWord_5586812) baseStart_5586812 baseEnd_5586812 := by
    simpa [prefixWord, tailWord_5586812, baseEnd_5586812] using wordTrace_append hprefix tailTrace_5586812
  have hstable : (prefixWord ++ tailWord_5586812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5586812).length < 2 ^ (prefixWord ++ tailWord_5586812).sum := by decide
  have hdescent : baseEnd_5586812 < baseStart_5586812 := by decide
  rcases family_descends (prefixWord ++ tailWord_5586812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5586877 : List Nat := [1, 4, 1, 2, 3, 3, 2, 2, 1, 1, 3]
def baseStart_5586877 : Nat := 118140960795 + 5586877 * 2 ^ 59
def prefixEnd_5586877 : Nat := 4983230072969 + 3 ^ 40 * 5586877 * 2
def baseEnd_5586877 : Nat := 2868753258549243051743927

theorem tailTrace_5586877 : CollatzResearch.WordTrace tailWord_5586877 prefixEnd_5586877 2868753258549243051743927 := by
  unfold tailWord_5586877
  simp only [CollatzResearch.WordTrace]
  refine ⟨203770144580706266471942885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135846763053804177647961923 203770144580706266471942885)
  ·
    refine ⟨38206902108882424963489291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 203770144580706266471942885 38206902108882424963489291)
    ·
      refine ⟨57310353163323637445233937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38206902108882424963489291 57310353163323637445233937)
      ·
        refine ⟨42982764872492728083925453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57310353163323637445233937 42982764872492728083925453)
        ·
          refine ⟨16118536827184773031472045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42982764872492728083925453 16118536827184773031472045)
          ·
            refine ⟨6044451310194289886802017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16118536827184773031472045 6044451310194289886802017)
            ·
              refine ⟨4533338482645717415101513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6044451310194289886802017 4533338482645717415101513)
              ·
                refine ⟨3400003861984288061326135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4533338482645717415101513 3400003861984288061326135)
                ·
                  refine ⟨5100005792976432091989203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3400003861984288061326135 5100005792976432091989203)
                  ·
                    refine ⟨7650008689464648137983805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5100005792976432091989203 7650008689464648137983805)
                    ·
                      refine ⟨2868753258549243051743927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7650008689464648137983805 2868753258549243051743927)
                      ·
                        rfl

theorem cell23_5586877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 2, 2, 1, 1, 3].length) (baseStart_5586877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5586877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5586877 prefixEnd_5586877 := by exact prefixLift 5586877
  have htrace : WordTrace (prefixWord ++ tailWord_5586877) baseStart_5586877 baseEnd_5586877 := by
    simpa [prefixWord, tailWord_5586877, baseEnd_5586877] using wordTrace_append hprefix tailTrace_5586877
  have hstable : (prefixWord ++ tailWord_5586877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5586877).length < 2 ^ (prefixWord ++ tailWord_5586877).sum := by decide
  have hdescent : baseEnd_5586877 < baseStart_5586877 := by decide
  rcases family_descends (prefixWord ++ tailWord_5586877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5586906 : List Nat := [3, 1, 1, 2, 5, 1, 3, 7]
def baseStart_5586906 : Nat := 118140960795 + 5586906 * 2 ^ 59
def prefixEnd_5586906 : Nat := 4983230072969 + 3 ^ 40 * 5586906 * 2
def baseEnd_5586906 : Nat := 106250672203267534751159

theorem tailTrace_5586906 : CollatzResearch.WordTrace tailWord_5586906 prefixEnd_5586906 106250672203267534751159 := by
  unfold tailWord_5586906
  simp only [CollatzResearch.WordTrace]
  refine ⟨50942800574400301106187143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135847468198400802949832381 50942800574400301106187143)
  ·
    refine ⟨76414200861600451659280715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50942800574400301106187143 76414200861600451659280715)
    ·
      refine ⟨114621301292400677488921073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76414200861600451659280715 114621301292400677488921073)
      ·
        refine ⟨85965975969300508116690805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114621301292400677488921073 85965975969300508116690805)
        ·
          refine ⟨8059310247121922635939763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 85965975969300508116690805 8059310247121922635939763)
          ·
            refine ⟨12088965370682883953909645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8059310247121922635939763 12088965370682883953909645)
            ·
              refine ⟨4533362014006081482716117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12088965370682883953909645 4533362014006081482716117)
              ·
                refine ⟨106250672203267534751159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4533362014006081482716117 106250672203267534751159)
                ·
                  rfl

theorem cell23_5586906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 3, 7].length) (baseStart_5586906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5586906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5586906 prefixEnd_5586906 := by exact prefixLift 5586906
  have htrace : WordTrace (prefixWord ++ tailWord_5586906) baseStart_5586906 baseEnd_5586906 := by
    simpa [prefixWord, tailWord_5586906, baseEnd_5586906] using wordTrace_append hprefix tailTrace_5586906
  have hstable : (prefixWord ++ tailWord_5586906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5586906).length < 2 ^ (prefixWord ++ tailWord_5586906).sum := by decide
  have hdescent : baseEnd_5586906 < baseStart_5586906 := by decide
  rcases family_descends (prefixWord ++ tailWord_5586906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5586916 : List Nat := [2, 3, 1, 1, 1, 1, 4, 2, 4, 1, 3]
def baseStart_5586916 : Nat := 118140960795 + 5586916 * 2 ^ 59
def prefixEnd_5586916 : Nat := 4983230072969 + 3 ^ 40 * 5586916 * 2
def baseEnd_5586916 : Nat := 2868773284294768399156247

theorem tailTrace_5586916 : CollatzResearch.WordTrace tailWord_5586916 prefixEnd_5586916 2868773284294768399156247 := by
  unfold tailWord_5586916
  simp only [CollatzResearch.WordTrace]
  refine ⟨101885783513782488066306301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135847711351709984088408401 101885783513782488066306301)
  ·
    refine ⟨38207168817668433024864863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101885783513782488066306301 38207168817668433024864863)
    ·
      refine ⟨57310753226502649537297295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38207168817668433024864863 57310753226502649537297295)
      ·
        refine ⟨85966129839753974305945943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57310753226502649537297295 85966129839753974305945943)
        ·
          refine ⟨128949194759630961458918915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85966129839753974305945943 128949194759630961458918915)
          ·
            refine ⟨193423792139446442188378373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128949194759630961458918915 193423792139446442188378373)
            ·
              refine ⟨36266961026146207910320945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 193423792139446442188378373 36266961026146207910320945)
              ·
                refine ⟨27200220769609655932740709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36266961026146207910320945 27200220769609655932740709)
                ·
                  refine ⟨5100041394301810487388883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27200220769609655932740709 5100041394301810487388883)
                  ·
                    refine ⟨7650062091452715731083325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5100041394301810487388883 7650062091452715731083325)
                    ·
                      refine ⟨2868773284294768399156247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7650062091452715731083325 2868773284294768399156247)
                      ·
                        rfl

theorem cell23_5586916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 2, 4, 1, 3].length) (baseStart_5586916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5586916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5586916 prefixEnd_5586916 := by exact prefixLift 5586916
  have htrace : WordTrace (prefixWord ++ tailWord_5586916) baseStart_5586916 baseEnd_5586916 := by
    simpa [prefixWord, tailWord_5586916, baseEnd_5586916] using wordTrace_append hprefix tailTrace_5586916
  have hstable : (prefixWord ++ tailWord_5586916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5586916).length < 2 ^ (prefixWord ++ tailWord_5586916).sum := by decide
  have hdescent : baseEnd_5586916 < baseStart_5586916 := by decide
  rcases family_descends (prefixWord ++ tailWord_5586916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5586949 : List Nat := [1, 3, 1, 1, 2, 4, 2, 1, 2, 6]
def baseStart_5586949 : Nat := 118140960795 + 5586949 * 2 ^ 59
def prefixEnd_5586949 : Nat := 4983230072969 + 3 ^ 40 * 5586949 * 2
def baseEnd_5586949 : Nat := 956263409718788923347865

theorem tailTrace_5586949 : CollatzResearch.WordTrace tailWord_5586949 prefixEnd_5586949 956263409718788923347865 := by
  unfold tailWord_5586949
  simp only [CollatzResearch.WordTrace]
  refine ⟨203772770636445422768563901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135848513757630281845709267 203772770636445422768563901)
  ·
    refine ⟨76414788988667033538211463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 203772770636445422768563901 76414788988667033538211463)
    ·
      refine ⟨114622183483000550307317195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76414788988667033538211463 114622183483000550307317195)
      ·
        refine ⟨171933275224500825460975793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114622183483000550307317195 171933275224500825460975793)
        ·
          refine ⟨128949956418375619095731845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171933275224500825460975793 128949956418375619095731845)
          ·
            refine ⟨24178116828445428580449721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 128949956418375619095731845 24178116828445428580449721)
            ·
              refine ⟨18133587621334071435337291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24178116828445428580449721 18133587621334071435337291)
              ·
                refine ⟨27200381432001107153005937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18133587621334071435337291 27200381432001107153005937)
                ·
                  refine ⟨20400286074000830364754453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27200381432001107153005937 20400286074000830364754453)
                  ·
                    refine ⟨956263409718788923347865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20400286074000830364754453 956263409718788923347865)
                    ·
                      rfl

theorem cell23_5586949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 1, 2, 6].length) (baseStart_5586949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5586949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5586949 prefixEnd_5586949 := by exact prefixLift 5586949
  have htrace : WordTrace (prefixWord ++ tailWord_5586949) baseStart_5586949 baseEnd_5586949 := by
    simpa [prefixWord, tailWord_5586949, baseEnd_5586949] using wordTrace_append hprefix tailTrace_5586949
  have hstable : (prefixWord ++ tailWord_5586949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5586949).length < 2 ^ (prefixWord ++ tailWord_5586949).sum := by decide
  have hdescent : baseEnd_5586949 < baseStart_5586949 := by decide
  rcases family_descends (prefixWord ++ tailWord_5586949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5586957 : List Nat := [1, 7, 1, 2, 1, 2, 2, 7]
def baseStart_5586957 : Nat := 118140960795 + 5586957 * 2 ^ 59
def prefixEnd_5586957 : Nat := 4983230072969 + 3 ^ 40 * 5586957 * 2
def baseEnd_5586957 : Nat := 106251642111170471805317

theorem tailTrace_5586957 : CollatzResearch.WordTrace tailWord_5586957 prefixEnd_5586957 106251642111170471805317 := by
  unfold tailWord_5586957
  simp only [CollatzResearch.WordTrace]
  refine ⟨203773062420416440134855125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135848708280277626756570083 203773062420416440134855125)
  ·
    refine ⟨4775931150478510315660667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 203773062420416440134855125 4775931150478510315660667)
    ·
      refine ⟨7163896725717765473491001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4775931150478510315660667 7163896725717765473491001)
      ·
        refine ⟨5372922544288324105118251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7163896725717765473491001 5372922544288324105118251)
        ·
          refine ⟨8059383816432486157677377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5372922544288324105118251 8059383816432486157677377)
          ·
            refine ⟨6044537862324364618258033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8059383816432486157677377 6044537862324364618258033)
            ·
              refine ⟨4533403396743273463693525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6044537862324364618258033 4533403396743273463693525)
              ·
                refine ⟨106251642111170471805317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4533403396743273463693525 106251642111170471805317)
                ·
                  rfl

theorem cell23_5586957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 2, 7].length) (baseStart_5586957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5586957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5586957 prefixEnd_5586957 := by exact prefixLift 5586957
  have htrace : WordTrace (prefixWord ++ tailWord_5586957) baseStart_5586957 baseEnd_5586957 := by
    simpa [prefixWord, tailWord_5586957, baseEnd_5586957] using wordTrace_append hprefix tailTrace_5586957
  have hstable : (prefixWord ++ tailWord_5586957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5586957).length < 2 ^ (prefixWord ++ tailWord_5586957).sum := by decide
  have hdescent : baseEnd_5586957 < baseStart_5586957 := by decide
  rcases family_descends (prefixWord ++ tailWord_5586957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5586990 : List Nat := [4, 1, 3, 1, 1, 2, 2, 1, 4, 2, 2]
def baseStart_5586990 : Nat := 118140960795 + 5586990 * 2 ^ 59
def prefixEnd_5586990 : Nat := 4983230072969 + 3 ^ 40 * 5586990 * 2
def baseEnd_5586990 : Nat := 2868811281863201109630907

theorem tailTrace_5586990 : CollatzResearch.WordTrace tailWord_5586990 prefixEnd_5586990 2868811281863201109630907 := by
  unfold tailWord_5586990
  simp only [CollatzResearch.WordTrace]
  refine ⟨25471783253662110846350803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135849510686197924513870949 25471783253662110846350803)
  ·
    refine ⟨38207674880493166269526205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25471783253662110846350803 38207674880493166269526205)
    ·
      refine ⟨14327878080184937351072327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38207674880493166269526205 14327878080184937351072327)
      ·
        refine ⟨21491817120277406026608491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14327878080184937351072327 21491817120277406026608491)
        ·
          refine ⟨32237725680416109039912737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21491817120277406026608491 32237725680416109039912737)
          ·
            refine ⟨24178294260312081779934553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32237725680416109039912737 24178294260312081779934553)
            ·
              refine ⟨18133720695234061334950915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24178294260312081779934553 18133720695234061334950915)
              ·
                refine ⟨27200581042851092002426373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18133720695234061334950915 27200581042851092002426373)
                ·
                  refine ⟨5100108945534579750454945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27200581042851092002426373 5100108945534579750454945)
                  ·
                    refine ⟨3825081709150934812841209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5100108945534579750454945 3825081709150934812841209)
                    ·
                      refine ⟨2868811281863201109630907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3825081709150934812841209 2868811281863201109630907)
                      ·
                        rfl

theorem cell23_5586990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 1, 4, 2, 2].length) (baseStart_5586990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5586990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5586990 prefixEnd_5586990 := by exact prefixLift 5586990
  have htrace : WordTrace (prefixWord ++ tailWord_5586990) baseStart_5586990 baseEnd_5586990 := by
    simpa [prefixWord, tailWord_5586990, baseEnd_5586990] using wordTrace_append hprefix tailTrace_5586990
  have hstable : (prefixWord ++ tailWord_5586990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5586990).length < 2 ^ (prefixWord ++ tailWord_5586990).sum := by decide
  have hdescent : baseEnd_5586990 < baseStart_5586990 := by decide
  rcases family_descends (prefixWord ++ tailWord_5586990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5587016 : List Nat := [2, 1, 3, 1, 1, 1, 2, 1, 4, 5, 2]
def baseStart_5587016 : Nat := 118140960795 + 5587016 * 2 ^ 59
def prefixEnd_5587016 : Nat := 4983230072969 + 3 ^ 40 * 5587016 * 2
def baseEnd_5587016 : Nat := 2868824632360218007905787

theorem tailTrace_5587016 : CollatzResearch.WordTrace tailWord_5587016 prefixEnd_5587016 2868824632360218007905787 := by
  unfold tailWord_5587016
  simp only [CollatzResearch.WordTrace]
  refine ⟨101887607163601346605626451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135850142884801795474168601 101887607163601346605626451)
  ·
    refine ⟨152831410745402019908439677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101887607163601346605626451 152831410745402019908439677)
    ·
      refine ⟨57311779029525757465664879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152831410745402019908439677 57311779029525757465664879)
      ·
        refine ⟨85967668544288636198497319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57311779029525757465664879 85967668544288636198497319)
        ·
          refine ⟨128951502816432954297745979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85967668544288636198497319 128951502816432954297745979)
          ·
            refine ⟨193427254224649431446618969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128951502816432954297745979 193427254224649431446618969)
            ·
              refine ⟨145070440668487073584964227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 193427254224649431446618969 145070440668487073584964227)
              ·
                refine ⟨217605661002730610377446341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 145070440668487073584964227 217605661002730610377446341)
                ·
                  refine ⟨40801061438011989445771189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 217605661002730610377446341 40801061438011989445771189)
                  ·
                    refine ⟨3825099509813624010541049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40801061438011989445771189 3825099509813624010541049)
                    ·
                      refine ⟨2868824632360218007905787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3825099509813624010541049 2868824632360218007905787)
                      ·
                        rfl

theorem cell23_5587016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 4, 5, 2].length) (baseStart_5587016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5587016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5587016 prefixEnd_5587016 := by exact prefixLift 5587016
  have htrace : WordTrace (prefixWord ++ tailWord_5587016) baseStart_5587016 baseEnd_5587016 := by
    simpa [prefixWord, tailWord_5587016, baseEnd_5587016] using wordTrace_append hprefix tailTrace_5587016
  have hstable : (prefixWord ++ tailWord_5587016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5587016).length < 2 ^ (prefixWord ++ tailWord_5587016).sum := by decide
  have hdescent : baseEnd_5587016 < baseStart_5587016 := by decide
  rcases family_descends (prefixWord ++ tailWord_5587016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5587036 : List Nat := [2, 2, 4, 1, 1, 2, 1, 2, 1, 2, 5]
def baseStart_5587036 : Nat := 118140960795 + 5587036 * 2 ^ 59
def prefixEnd_5587036 : Nat := 4983230072969 + 3 ^ 40 * 5587036 * 2
def baseEnd_5587036 : Nat := 2868834901973307929655695

theorem tailTrace_5587036 : CollatzResearch.WordTrace tailWord_5587036 prefixEnd_5587036 2868834901973307929655695 := by
  unfold tailWord_5587036
  simp only [CollatzResearch.WordTrace]
  refine ⟨101887971893565118313490481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135850629191420157751320641 101887971893565118313490481)
  ·
    refine ⟨76415978920173838735117861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101887971893565118313490481 76415978920173838735117861)
    ·
      refine ⟨14327996047532594762834599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76415978920173838735117861 14327996047532594762834599)
      ·
        refine ⟨21491994071298892144251899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14327996047532594762834599 21491994071298892144251899)
        ·
          refine ⟨32237991106948338216377849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21491994071298892144251899 32237991106948338216377849)
          ·
            refine ⟨24178493330211253662283387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32237991106948338216377849 24178493330211253662283387)
            ·
              refine ⟨36267739995316880493425081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24178493330211253662283387 36267739995316880493425081)
              ·
                refine ⟨27200804996487660370068811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36267739995316880493425081 27200804996487660370068811)
                ·
                  refine ⟨40801207494731490555103217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27200804996487660370068811 40801207494731490555103217)
                  ·
                    refine ⟨30600905621048617916327413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40801207494731490555103217 30600905621048617916327413)
                    ·
                      refine ⟨2868834901973307929655695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30600905621048617916327413 2868834901973307929655695)
                      ·
                        rfl

theorem cell23_5587036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_5587036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5587036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5587036 prefixEnd_5587036 := by exact prefixLift 5587036
  have htrace : WordTrace (prefixWord ++ tailWord_5587036) baseStart_5587036 baseEnd_5587036 := by
    simpa [prefixWord, tailWord_5587036, baseEnd_5587036] using wordTrace_append hprefix tailTrace_5587036
  have hstable : (prefixWord ++ tailWord_5587036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5587036).length < 2 ^ (prefixWord ++ tailWord_5587036).sum := by decide
  have hdescent : baseEnd_5587036 < baseStart_5587036 := by decide
  rcases family_descends (prefixWord ++ tailWord_5587036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5587049 : List Nat := [1, 2, 1, 1, 1, 5, 1, 1, 2, 3, 5]
def baseStart_5587049 : Nat := 118140960795 + 5587049 * 2 ^ 59
def prefixEnd_5587049 : Nat := 4983230072969 + 3 ^ 40 * 5587049 * 2
def baseEnd_5587049 : Nat := 2868841577221816378793135

theorem tailTrace_5587049 : CollatzResearch.WordTrace tailWord_5587049 prefixEnd_5587049 2868841577221816378793135 := by
  unfold tailWord_5587049
  simp only [CollatzResearch.WordTrace]
  refine ⟨203776417936083139847204201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135850945290722093231469467 203776417936083139847204201)
  ·
    refine ⟨152832313452062354885403151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203776417936083139847204201 152832313452062354885403151)
    ·
      refine ⟨229248470178093532328104727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152832313452062354885403151 229248470178093532328104727)
      ·
        refine ⟨343872705267140298492157091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229248470178093532328104727 343872705267140298492157091)
        ·
          refine ⟨515809057900710447738235637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 343872705267140298492157091 515809057900710447738235637)
          ·
            refine ⟨48357099178191604475459591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 515809057900710447738235637 48357099178191604475459591)
            ·
              refine ⟨72535648767287406713189387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48357099178191604475459591 72535648767287406713189387)
              ·
                refine ⟨108803473150931110069784081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72535648767287406713189387 108803473150931110069784081)
                ·
                  refine ⟨81602604863198332552338061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 108803473150931110069784081 81602604863198332552338061)
                  ·
                    refine ⟨30600976823699374707126773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 81602604863198332552338061 30600976823699374707126773)
                    ·
                      refine ⟨2868841577221816378793135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30600976823699374707126773 2868841577221816378793135)
                      ·
                        rfl

theorem cell23_5587049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 2, 3, 5].length) (baseStart_5587049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5587049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5587049 prefixEnd_5587049 := by exact prefixLift 5587049
  have htrace : WordTrace (prefixWord ++ tailWord_5587049) baseStart_5587049 baseEnd_5587049 := by
    simpa [prefixWord, tailWord_5587049, baseEnd_5587049] using wordTrace_append hprefix tailTrace_5587049
  have hstable : (prefixWord ++ tailWord_5587049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5587049).length < 2 ^ (prefixWord ++ tailWord_5587049).sum := by decide
  have hdescent : baseEnd_5587049 < baseStart_5587049 := by decide
  rcases family_descends (prefixWord ++ tailWord_5587049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5587063 : List Nat := [1, 1, 3, 1, 1, 6, 1, 1, 2, 4, 2]
def baseStart_5587063 : Nat := 118140960795 + 5587063 * 2 ^ 59
def prefixEnd_5587063 : Nat := 4983230072969 + 3 ^ 40 * 5587063 * 2
def baseEnd_5587063 : Nat := 2868848765950979324018071

theorem tailTrace_5587063 : CollatzResearch.WordTrace tailWord_5587063 prefixEnd_5587063 2868848765950979324018071 := by
  unfold tailWord_5587063
  simp only [CollatzResearch.WordTrace]
  refine ⟨203776928558032420238213843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135851285705354946825475895 203776928558032420238213843)
  ·
    refine ⟨305665392837048630357320765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203776928558032420238213843 305665392837048630357320765)
    ·
      refine ⟨114624522313893236383995287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 305665392837048630357320765 114624522313893236383995287)
      ·
        refine ⟨171936783470839854575992931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114624522313893236383995287 171936783470839854575992931)
        ·
          refine ⟨257905175206259781863989397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171936783470839854575992931 257905175206259781863989397)
          ·
            refine ⟨12089305087793427274874503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 257905175206259781863989397 12089305087793427274874503)
            ·
              refine ⟨18133957631690140912311755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12089305087793427274874503 18133957631690140912311755)
              ·
                refine ⟨27200936447535211368467633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18133957631690140912311755 27200936447535211368467633)
                ·
                  refine ⟨20400702335651408526350725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27200936447535211368467633 20400702335651408526350725)
                  ·
                    refine ⟨3825131687934639098690761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20400702335651408526350725 3825131687934639098690761)
                    ·
                      refine ⟨2868848765950979324018071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3825131687934639098690761 2868848765950979324018071)
                      ·
                        rfl

theorem cell23_5587063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 1, 2, 4, 2].length) (baseStart_5587063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5587063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5587063 prefixEnd_5587063 := by exact prefixLift 5587063
  have htrace : WordTrace (prefixWord ++ tailWord_5587063) baseStart_5587063 baseEnd_5587063 := by
    simpa [prefixWord, tailWord_5587063, baseEnd_5587063] using wordTrace_append hprefix tailTrace_5587063
  have hstable : (prefixWord ++ tailWord_5587063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5587063).length < 2 ^ (prefixWord ++ tailWord_5587063).sum := by decide
  have hdescent : baseEnd_5587063 < baseStart_5587063 := by decide
  rcases family_descends (prefixWord ++ tailWord_5587063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5587080 : List Nat := [2, 1, 3, 4, 1, 3, 1, 1, 2, 1, 4]
def baseStart_5587080 : Nat := 118140960795 + 5587080 * 2 ^ 59
def prefixEnd_5587080 : Nat := 4983230072969 + 3 ^ 40 * 5587080 * 2
def baseEnd_5587080 : Nat := 2868857495122105757505493

theorem tailTrace_5587080 : CollatzResearch.WordTrace tailWord_5587080 prefixEnd_5587080 2868857495122105757505493 := by
  unfold tailWord_5587080
  simp only [CollatzResearch.WordTrace]
  refine ⟨101888774299485416070791347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135851699065980554761055129 101888774299485416070791347)
  ·
    refine ⟨152833161449228124106187021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101888774299485416070791347 152833161449228124106187021)
    ·
      refine ⟨57312435543460546539820133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152833161449228124106187021 57312435543460546539820133)
      ·
        refine ⟨10746081664398852476216275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57312435543460546539820133 10746081664398852476216275)
        ·
          refine ⟨16119122496598278714324413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10746081664398852476216275 16119122496598278714324413)
          ·
            refine ⟨6044670936224354517871655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16119122496598278714324413 6044670936224354517871655)
            ·
              refine ⟨9067006404336531776807483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6044670936224354517871655 9067006404336531776807483)
              ·
                refine ⟨13600509606504797665211225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9067006404336531776807483 13600509606504797665211225)
                ·
                  refine ⟨10200382204878598248908419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13600509606504797665211225 10200382204878598248908419)
                  ·
                    refine ⟨15300573307317897373362629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10200382204878598248908419 15300573307317897373362629)
                    ·
                      refine ⟨2868857495122105757505493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15300573307317897373362629 2868857495122105757505493)
                      ·
                        rfl

theorem cell23_5587080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_5587080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5587080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5587080 prefixEnd_5587080 := by exact prefixLift 5587080
  have htrace : WordTrace (prefixWord ++ tailWord_5587080) baseStart_5587080 baseEnd_5587080 := by
    simpa [prefixWord, tailWord_5587080, baseEnd_5587080] using wordTrace_append hprefix tailTrace_5587080
  have hstable : (prefixWord ++ tailWord_5587080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5587080).length < 2 ^ (prefixWord ++ tailWord_5587080).sum := by decide
  have hdescent : baseEnd_5587080 < baseStart_5587080 := by decide
  rcases family_descends (prefixWord ++ tailWord_5587080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5587089 : List Nat := [1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 6]
def baseStart_5587089 : Nat := 118140960795 + 5587089 * 2 ^ 59
def prefixEnd_5587089 : Nat := 4983230072969 + 3 ^ 40 * 5587089 * 2
def baseEnd_5587089 : Nat := 2868862116447996222292951

theorem tailTrace_5587089 : CollatzResearch.WordTrace tailWord_5587089 prefixEnd_5587089 2868862116447996222292951 := by
  unfold tailWord_5587089
  simp only [CollatzResearch.WordTrace]
  refine ⟨203777876855938226678660321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135851917903958817785773547 203777876855938226678660321)
  ·
    refine ⟨152833407641953670008995241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203777876855938226678660321 152833407641953670008995241)
    ·
      refine ⟨114625055731465252506746431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152833407641953670008995241 114625055731465252506746431)
      ·
        refine ⟨171937583597197878760119647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114625055731465252506746431 171937583597197878760119647)
        ·
          refine ⟨257906375395796818140179471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171937583597197878760119647 257906375395796818140179471)
          ·
            refine ⟨386859563093695227210269207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 257906375395796818140179471 386859563093695227210269207)
            ·
              refine ⟨580289344640542840815403811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 386859563093695227210269207 580289344640542840815403811)
              ·
                refine ⟨870434016960814261223105717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 580289344640542840815403811 870434016960814261223105717)
                ·
                  refine ⟨81603189090076336989666161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 870434016960814261223105717 81603189090076336989666161)
                  ·
                    refine ⟨61202391817557252742249621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 81603189090076336989666161 61202391817557252742249621)
                    ·
                      refine ⟨2868862116447996222292951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61202391817557252742249621 2868862116447996222292951)
                      ·
                        rfl

theorem cell23_5587089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 6].length) (baseStart_5587089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5587089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5587089 prefixEnd_5587089 := by exact prefixLift 5587089
  have htrace : WordTrace (prefixWord ++ tailWord_5587089) baseStart_5587089 baseEnd_5587089 := by
    simpa [prefixWord, tailWord_5587089, baseEnd_5587089] using wordTrace_append hprefix tailTrace_5587089
  have hstable : (prefixWord ++ tailWord_5587089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5587089).length < 2 ^ (prefixWord ++ tailWord_5587089).sum := by decide
  have hdescent : baseEnd_5587089 < baseStart_5587089 := by decide
  rcases family_descends (prefixWord ++ tailWord_5587089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5587103 : List Nat := [1, 1, 2, 6, 1, 1, 3, 2, 6]
def baseStart_5587103 : Nat := 118140960795 + 5587103 * 2 ^ 59
def prefixEnd_5587103 : Nat := 4983230072969 + 3 ^ 40 * 5587103 * 2
def baseEnd_5587103 : Nat := 318763256130795463057543

theorem tailTrace_5587103 : CollatzResearch.WordTrace tailWord_5587103 prefixEnd_5587103 318763256130795463057543 := by
  unfold tailWord_5587103
  simp only [CollatzResearch.WordTrace]
  refine ⟨203778387477887507069669963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135852258318591671379779975 203778387477887507069669963)
  ·
    refine ⟨305667581216831260604504945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203778387477887507069669963 305667581216831260604504945)
    ·
      refine ⟨229250685912623445453378709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 305667581216831260604504945 229250685912623445453378709)
      ·
        refine ⟨10746125902154224005627127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 229250685912623445453378709 10746125902154224005627127)
        ·
          refine ⟨16119188853231336008440691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10746125902154224005627127 16119188853231336008440691)
          ·
            refine ⟨24178783279847004012661037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16119188853231336008440691 24178783279847004012661037)
            ·
              refine ⟨9067043729942626504747889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24178783279847004012661037 9067043729942626504747889)
              ·
                refine ⟨6800282797456969878560917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9067043729942626504747889 6800282797456969878560917)
                ·
                  refine ⟨318763256130795463057543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6800282797456969878560917 318763256130795463057543)
                  ·
                    rfl

theorem cell23_5587103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 2, 6].length) (baseStart_5587103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5587103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5587103 prefixEnd_5587103 := by exact prefixLift 5587103
  have htrace : WordTrace (prefixWord ++ tailWord_5587103) baseStart_5587103 baseEnd_5587103 := by
    simpa [prefixWord, tailWord_5587103, baseEnd_5587103] using wordTrace_append hprefix tailTrace_5587103
  have hstable : (prefixWord ++ tailWord_5587103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5587103).length < 2 ^ (prefixWord ++ tailWord_5587103).sum := by decide
  have hdescent : baseEnd_5587103 < baseStart_5587103 := by decide
  rcases family_descends (prefixWord ++ tailWord_5587103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5587140 : List Nat := [2, 3, 3, 1, 2, 1, 2, 1, 1, 5, 2]
def baseStart_5587140 : Nat := 118140960795 + 5587140 * 2 ^ 59
def prefixEnd_5587140 : Nat := 4983230072969 + 3 ^ 40 * 5587140 * 2
def baseEnd_5587140 : Nat := 2868888303961375522755217

theorem tailTrace_5587140 : CollatzResearch.WordTrace tailWord_5587140 prefixEnd_5587140 2868888303961375522755217 := by
  unfold tailWord_5587140
  simp only [CollatzResearch.WordTrace]
  refine ⟨101889868489376731194383437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135853157985835641592511249 101889868489376731194383437)
  ·
    refine ⟨38208700683516274197893789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101889868489376731194383437 38208700683516274197893789)
    ·
      refine ⟨14328262756318602824210171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38208700683516274197893789 14328262756318602824210171)
      ·
        refine ⟨21492394134477904236315257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14328262756318602824210171 21492394134477904236315257)
        ·
          refine ⟨16119295600858428177236443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21492394134477904236315257 16119295600858428177236443)
          ·
            refine ⟨24178943401287642265854665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16119295600858428177236443 24178943401287642265854665)
            ·
              refine ⟨18134207550965731699390999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24178943401287642265854665 18134207550965731699390999)
              ·
                refine ⟨27201311326448597549086499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18134207550965731699390999 27201311326448597549086499)
                ·
                  refine ⟨40801966989672896323629749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27201311326448597549086499 40801966989672896323629749)
                  ·
                    refine ⟨3825184405281834030340289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40801966989672896323629749 3825184405281834030340289)
                    ·
                      refine ⟨2868888303961375522755217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3825184405281834030340289 2868888303961375522755217)
                      ·
                        rfl

theorem cell23_5587140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 1, 1, 5, 2].length) (baseStart_5587140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5587140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5587140 prefixEnd_5587140 := by exact prefixLift 5587140
  have htrace : WordTrace (prefixWord ++ tailWord_5587140) baseStart_5587140 baseEnd_5587140 := by
    simpa [prefixWord, tailWord_5587140, baseEnd_5587140] using wordTrace_append hprefix tailTrace_5587140
  have hstable : (prefixWord ++ tailWord_5587140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5587140).length < 2 ^ (prefixWord ++ tailWord_5587140).sum := by decide
  have hdescent : baseEnd_5587140 < baseStart_5587140 := by decide
  rcases family_descends (prefixWord ++ tailWord_5587140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5587146 : List Nat := [3, 1, 2, 1, 3, 1, 2, 1, 3, 6]
def baseStart_5587146 : Nat := 118140960795 + 5587146 * 2 ^ 59
def prefixEnd_5587146 : Nat := 4983230072969 + 3 ^ 40 * 5587146 * 2
def baseEnd_5587146 : Nat := 956297128281767499760063

theorem tailTrace_5587146 : CollatzResearch.WordTrace tailWord_5587146 prefixEnd_5587146 956297128281767499760063 := by
  unfold tailWord_5587146
  simp only [CollatzResearch.WordTrace]
  refine ⟨50944988954182931353371323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135853303877821150275656861 50944988954182931353371323)
  ·
    refine ⟨76417483431274397030056985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50944988954182931353371323 76417483431274397030056985)
    ·
      refine ⟨57313112573455797772542739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76417483431274397030056985 57313112573455797772542739)
      ·
        refine ⟨85969668860183696658814109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57313112573455797772542739 85969668860183696658814109)
        ·
          refine ⟨32238625822568886247055291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85969668860183696658814109 32238625822568886247055291)
          ·
            refine ⟨48357938733853329370582937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32238625822568886247055291 48357938733853329370582937)
            ·
              refine ⟨36268454050389997027937203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48357938733853329370582937 36268454050389997027937203)
              ·
                refine ⟨54402681075584995541905805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36268454050389997027937203 54402681075584995541905805)
                ·
                  refine ⟨20401005403344373328214677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54402681075584995541905805 20401005403344373328214677)
                  ·
                    refine ⟨956297128281767499760063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20401005403344373328214677 956297128281767499760063)
                    ·
                      rfl

theorem cell23_5587146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 6].length) (baseStart_5587146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5587146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5587146 prefixEnd_5587146 := by exact prefixLift 5587146
  have htrace : WordTrace (prefixWord ++ tailWord_5587146) baseStart_5587146 baseEnd_5587146 := by
    simpa [prefixWord, tailWord_5587146, baseEnd_5587146] using wordTrace_append hprefix tailTrace_5587146
  have hstable : (prefixWord ++ tailWord_5587146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5587146).length < 2 ^ (prefixWord ++ tailWord_5587146).sum := by decide
  have hdescent : baseEnd_5587146 < baseStart_5587146 := by decide
  rcases family_descends (prefixWord ++ tailWord_5587146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5587153 : List Nat := [1, 2, 2, 1, 2, 2, 4, 3, 1, 1, 4]
def baseStart_5587153 : Nat := 118140960795 + 5587153 * 2 ^ 59
def prefixEnd_5587153 : Nat := 4983230072969 + 3 ^ 40 * 5587153 * 2
def baseEnd_5587153 : Nat := 2868894979209883971892657

theorem tailTrace_5587153 : CollatzResearch.WordTrace tailWord_5587153 prefixEnd_5587153 2868894979209883971892657 := by
  unfold tailWord_5587153
  simp only [CollatzResearch.WordTrace]
  refine ⟨203780211127706365608990113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135853474085137577072660075 203780211127706365608990113)
  ·
    refine ⟨152835158345779774206742585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203780211127706365608990113 152835158345779774206742585)
    ·
      refine ⟨114626368759334830655056939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152835158345779774206742585 114626368759334830655056939)
      ·
        refine ⟨171939553139002245982585409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114626368759334830655056939 171939553139002245982585409)
        ·
          refine ⟨128954664854251684486939057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171939553139002245982585409 128954664854251684486939057)
          ·
            refine ⟨96715998640688763365204293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128954664854251684486939057 96715998640688763365204293)
            ·
              refine ⟨18134249745129143130975805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 96715998640688763365204293 18134249745129143130975805)
              ·
                refine ⟨6800343654423428674115927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18134249745129143130975805 6800343654423428674115927)
                ·
                  refine ⟨10200515481635143011173891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6800343654423428674115927 10200515481635143011173891)
                  ·
                    refine ⟨15300773222452714516760837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10200515481635143011173891 15300773222452714516760837)
                    ·
                      refine ⟨2868894979209883971892657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15300773222452714516760837 2868894979209883971892657)
                      ·
                        rfl

theorem cell23_5587153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 3, 1, 1, 4].length) (baseStart_5587153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5587153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5587153 prefixEnd_5587153 := by exact prefixLift 5587153
  have htrace : WordTrace (prefixWord ++ tailWord_5587153) baseStart_5587153 baseEnd_5587153 := by
    simpa [prefixWord, tailWord_5587153, baseEnd_5587153] using wordTrace_append hprefix tailTrace_5587153
  have hstable : (prefixWord ++ tailWord_5587153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5587153).length < 2 ^ (prefixWord ++ tailWord_5587153).sum := by decide
  have hdescent : baseEnd_5587153 < baseStart_5587153 := by decide
  rcases family_descends (prefixWord ++ tailWord_5587153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5587157 : List Nat := [1, 3, 2, 4, 2, 1, 1, 2, 2, 3, 2]
def baseStart_5587157 : Nat := 118140960795 + 5587157 * 2 ^ 59
def prefixEnd_5587157 : Nat := 4983230072969 + 3 ^ 40 * 5587157 * 2
def baseEnd_5587157 : Nat := 2868897033132501956242639

theorem tailTrace_5587157 : CollatzResearch.WordTrace tailWord_5587157 prefixEnd_5587157 2868897033132501956242639 := by
  unfold tailWord_5587157
  simp only [CollatzResearch.WordTrace]
  refine ⟨203780357019691874292135725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135853571346461249528090483 203780357019691874292135725)
  ·
    refine ⟨76417633882384452859550897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 203780357019691874292135725 76417633882384452859550897)
    ·
      refine ⟨57313225411788339644663173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76417633882384452859550897 57313225411788339644663173)
      ·
        refine ⟨10746229764710313683374345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57313225411788339644663173 10746229764710313683374345)
        ·
          refine ⟨8059672323532735262530759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10746229764710313683374345 8059672323532735262530759)
          ·
            refine ⟨12089508485299102893796139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8059672323532735262530759 12089508485299102893796139)
            ·
              refine ⟨18134262727948654340694209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12089508485299102893796139 18134262727948654340694209)
              ·
                refine ⟨13600697045961490755520657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18134262727948654340694209 13600697045961490755520657)
                ·
                  refine ⟨10200522784471118066640493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13600697045961490755520657 10200522784471118066640493)
                  ·
                    refine ⟨3825196044176669274990185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10200522784471118066640493 3825196044176669274990185)
                    ·
                      refine ⟨2868897033132501956242639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3825196044176669274990185 2868897033132501956242639)
                      ·
                        rfl

theorem cell23_5587157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 2, 2, 3, 2].length) (baseStart_5587157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5587157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5587157 prefixEnd_5587157 := by exact prefixLift 5587157
  have htrace : WordTrace (prefixWord ++ tailWord_5587157) baseStart_5587157 baseEnd_5587157 := by
    simpa [prefixWord, tailWord_5587157, baseEnd_5587157] using wordTrace_append hprefix tailTrace_5587157
  have hstable : (prefixWord ++ tailWord_5587157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5587157).length < 2 ^ (prefixWord ++ tailWord_5587157).sum := by decide
  have hdescent : baseEnd_5587157 < baseStart_5587157 := by decide
  rcases family_descends (prefixWord ++ tailWord_5587157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5587173 : List Nat := [1, 3, 1, 4, 2, 1, 2, 2, 1, 1, 5]
def baseStart_5587173 : Nat := 118140960795 + 5587173 * 2 ^ 59
def prefixEnd_5587173 : Nat := 4983230072969 + 3 ^ 40 * 5587173 * 2
def baseEnd_5587173 : Nat := 2868905248822973893642565

theorem tailTrace_5587173 : CollatzResearch.WordTrace tailWord_5587173 prefixEnd_5587173 2868905248822973893642565 := by
  unfold tailWord_5587173
  simp only [CollatzResearch.WordTrace]
  refine ⟨203780940587633909024718173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135853960391755939349812115 203780940587633909024718173)
  ·
    refine ⟨76417852720362715884269315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 203780940587633909024718173 76417852720362715884269315)
    ·
      refine ⟨114626779080544073826403973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76417852720362715884269315 114626779080544073826403973)
      ·
        refine ⟨21492521077602013842450745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 114626779080544073826403973 21492521077602013842450745)
        ·
          refine ⟨16119390808201510381838059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21492521077602013842450745 16119390808201510381838059)
          ·
            refine ⟨24179086212302265572757089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16119390808201510381838059 24179086212302265572757089)
            ·
              refine ⟨18134314659226699179567817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24179086212302265572757089 18134314659226699179567817)
              ·
                refine ⟨13600735994420024384675863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18134314659226699179567817 13600735994420024384675863)
                ·
                  refine ⟨20401103991630036577013795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13600735994420024384675863 20401103991630036577013795)
                  ·
                    refine ⟨30601655987445054865520693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20401103991630036577013795 30601655987445054865520693)
                    ·
                      refine ⟨2868905248822973893642565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30601655987445054865520693 2868905248822973893642565)
                      ·
                        rfl

theorem cell23_5587173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_5587173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5587173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5587173 prefixEnd_5587173 := by exact prefixLift 5587173
  have htrace : WordTrace (prefixWord ++ tailWord_5587173) baseStart_5587173 baseEnd_5587173 := by
    simpa [prefixWord, tailWord_5587173, baseEnd_5587173] using wordTrace_append hprefix tailTrace_5587173
  have hstable : (prefixWord ++ tailWord_5587173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5587173).length < 2 ^ (prefixWord ++ tailWord_5587173).sum := by decide
  have hdescent : baseEnd_5587173 < baseStart_5587173 := by decide
  rcases family_descends (prefixWord ++ tailWord_5587173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5587176 : List Nat := [2, 1, 4, 1, 2, 2, 1, 10]
def baseStart_5587176 : Nat := 118140960795 + 5587176 * 2 ^ 59
def prefixEnd_5587176 : Nat := 4983230072969 + 3 ^ 40 * 5587176 * 2
def baseEnd_5587176 : Nat := 106255807009812495626113

theorem tailTrace_5587176 : CollatzResearch.WordTrace tailWord_5587176 prefixEnd_5587176 106255807009812495626113 := by
  unfold tailWord_5587176
  simp only [CollatzResearch.WordTrace]
  refine ⟨101890525003311520268538691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135854033337748693691384921 101890525003311520268538691)
  ·
    refine ⟨152835787504967280402808037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101890525003311520268538691 152835787504967280402808037)
    ·
      refine ⟨28656710157181365075526507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 152835787504967280402808037 28656710157181365075526507)
      ·
        refine ⟨42985065235772047613289761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28656710157181365075526507 42985065235772047613289761)
        ·
          refine ⟨32238798926829035709967321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42985065235772047613289761 32238798926829035709967321)
          ·
            refine ⟨24179099195121776782475491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32238798926829035709967321 24179099195121776782475491)
            ·
              refine ⟨36268648792682665173713237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24179099195121776782475491 36268648792682665173713237)
              ·
                refine ⟨106255807009812495626113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 36268648792682665173713237 106255807009812495626113)
                ·
                  rfl

theorem cell23_5587176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 10].length) (baseStart_5587176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5587176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5587176 prefixEnd_5587176 := by exact prefixLift 5587176
  have htrace : WordTrace (prefixWord ++ tailWord_5587176) baseStart_5587176 baseEnd_5587176 := by
    simpa [prefixWord, tailWord_5587176, baseEnd_5587176] using wordTrace_append hprefix tailTrace_5587176
  have hstable : (prefixWord ++ tailWord_5587176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5587176).length < 2 ^ (prefixWord ++ tailWord_5587176).sum := by decide
  have hdescent : baseEnd_5587176 < baseStart_5587176 := by decide
  rcases family_descends (prefixWord ++ tailWord_5587176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5587203 : List Nat := [1, 1, 1, 3, 2, 3, 3, 2, 1, 3, 3]
def baseStart_5587203 : Nat := 118140960795 + 5587203 * 2 ^ 59
def prefixEnd_5587203 : Nat := 4983230072969 + 3 ^ 40 * 5587203 * 2
def baseEnd_5587203 : Nat := 2868920653242608776267427

theorem tailTrace_5587203 : CollatzResearch.WordTrace tailWord_5587203 prefixEnd_5587203 2868920653242608776267427 := by
  unfold tailWord_5587203
  simp only [CollatzResearch.WordTrace]
  refine ⟨203782034777525224148310263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135854689851683482765540175 203782034777525224148310263)
  ·
    refine ⟨305673052166287836222465395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203782034777525224148310263 305673052166287836222465395)
    ·
      refine ⟨458509578249431754333698093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305673052166287836222465395 458509578249431754333698093)
      ·
        refine ⟨171941091843536907875136785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 458509578249431754333698093 171941091843536907875136785)
        ·
          refine ⟨128955818882652680906352589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171941091843536907875136785 128955818882652680906352589)
          ·
            refine ⟨48358432080994755339882221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 128955818882652680906352589 48358432080994755339882221)
            ·
              refine ⟨18134412030373033252455833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48358432080994755339882221 18134412030373033252455833)
              ·
                refine ⟨13600809022779774939341875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18134412030373033252455833 13600809022779774939341875)
                ·
                  refine ⟨20401213534169662409012813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13600809022779774939341875 20401213534169662409012813)
                  ·
                    refine ⟨7650455075313623403379805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20401213534169662409012813 7650455075313623403379805)
                    ·
                      refine ⟨2868920653242608776267427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7650455075313623403379805 2868920653242608776267427)
                      ·
                        rfl

theorem cell23_5587203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 2, 1, 3, 3].length) (baseStart_5587203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5587203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5587203 prefixEnd_5587203 := by exact prefixLift 5587203
  have htrace : WordTrace (prefixWord ++ tailWord_5587203) baseStart_5587203 baseEnd_5587203 := by
    simpa [prefixWord, tailWord_5587203, baseEnd_5587203] using wordTrace_append hprefix tailTrace_5587203
  have hstable : (prefixWord ++ tailWord_5587203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5587203).length < 2 ^ (prefixWord ++ tailWord_5587203).sum := by decide
  have hdescent : baseEnd_5587203 < baseStart_5587203 := by decide
  rcases family_descends (prefixWord ++ tailWord_5587203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5587207 : List Nat := [1, 1, 4, 5, 1, 2, 1, 1, 1, 1, 5]
def baseStart_5587207 : Nat := 118140960795 + 5587207 * 2 ^ 59
def prefixEnd_5587207 : Nat := 4983230072969 + 3 ^ 40 * 5587207 * 2
def baseEnd_5587207 : Nat := 2868922707165226760617409

theorem tailTrace_5587207 : CollatzResearch.WordTrace tailWord_5587207 prefixEnd_5587207 2868922707165226760617409 := by
  unfold tailWord_5587207
  simp only [CollatzResearch.WordTrace]
  refine ⟨203782180669510732831455875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135854787113007155220970583 203782180669510732831455875)
  ·
    refine ⟨305673271004266099247183813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203782180669510732831455875 305673271004266099247183813)
    ·
      refine ⟨57313738313299893608846965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 305673271004266099247183813 57313738313299893608846965)
      ·
        refine ⟨5373162966871865025829403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 57313738313299893608846965 5373162966871865025829403)
        ·
          refine ⟨8059744450307797538744105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5373162966871865025829403 8059744450307797538744105)
          ·
            refine ⟨6044808337730848154058079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8059744450307797538744105 6044808337730848154058079)
            ·
              refine ⟨9067212506596272231087119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6044808337730848154058079 9067212506596272231087119)
              ·
                refine ⟨13600818759894408346630679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9067212506596272231087119 13600818759894408346630679)
                ·
                  refine ⟨20401228139841612519946019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13600818759894408346630679 20401228139841612519946019)
                  ·
                    refine ⟨30601842209762418779919029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20401228139841612519946019 30601842209762418779919029)
                    ·
                      refine ⟨2868922707165226760617409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30601842209762418779919029 2868922707165226760617409)
                      ·
                        rfl

theorem cell23_5587207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_5587207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5587207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5587207 prefixEnd_5587207 := by exact prefixLift 5587207
  have htrace : WordTrace (prefixWord ++ tailWord_5587207) baseStart_5587207 baseEnd_5587207 := by
    simpa [prefixWord, tailWord_5587207, baseEnd_5587207] using wordTrace_append hprefix tailTrace_5587207
  have hstable : (prefixWord ++ tailWord_5587207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5587207).length < 2 ^ (prefixWord ++ tailWord_5587207).sum := by decide
  have hdescent : baseEnd_5587207 < baseStart_5587207 := by decide
  rcases family_descends (prefixWord ++ tailWord_5587207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5587260 : List Nat := [2, 2, 2, 2, 1, 2, 1, 4, 1, 4, 2]
def baseStart_5587260 : Nat := 118140960795 + 5587260 * 2 ^ 59
def prefixEnd_5587260 : Nat := 4983230072969 + 3 ^ 40 * 5587260 * 2
def baseEnd_5587260 : Nat := 2868949921639915053254665

theorem tailTrace_5587260 : CollatzResearch.WordTrace tailWord_5587260 prefixEnd_5587260 2868949921639915053254665 := by
  unfold tailWord_5587260
  simp only [CollatzResearch.WordTrace]
  refine ⟨101892056869159361441567617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135856075825545815255423489 101892056869159361441567617)
  ·
    refine ⟨76419042651869521081175713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101892056869159361441567617 76419042651869521081175713)
    ·
      refine ⟨57314281988902140810881785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76419042651869521081175713 57314281988902140810881785)
      ·
        refine ⟨42985711491676605608161339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57314281988902140810881785 42985711491676605608161339)
        ·
          refine ⟨64478567237514908412242009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42985711491676605608161339 64478567237514908412242009)
          ·
            refine ⟨48358925428136181309181507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64478567237514908412242009 48358925428136181309181507)
            ·
              refine ⟨72538388142204271963772261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48358925428136181309181507 72538388142204271963772261)
              ·
                refine ⟨13600947776663300993207299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72538388142204271963772261 13600947776663300993207299)
                ·
                  refine ⟨20401421664994951489810949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13600947776663300993207299 20401421664994951489810949)
                  ·
                    refine ⟨3825266562186553404339553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20401421664994951489810949 3825266562186553404339553)
                    ·
                      refine ⟨2868949921639915053254665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3825266562186553404339553 2868949921639915053254665)
                      ·
                        rfl

theorem cell23_5587260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 4, 1, 4, 2].length) (baseStart_5587260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5587260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5587260 prefixEnd_5587260 := by exact prefixLift 5587260
  have htrace : WordTrace (prefixWord ++ tailWord_5587260) baseStart_5587260 baseEnd_5587260 := by
    simpa [prefixWord, tailWord_5587260, baseEnd_5587260] using wordTrace_append hprefix tailTrace_5587260
  have hstable : (prefixWord ++ tailWord_5587260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5587260).length < 2 ^ (prefixWord ++ tailWord_5587260).sum := by decide
  have hdescent : baseEnd_5587260 < baseStart_5587260 := by decide
  rcases family_descends (prefixWord ++ tailWord_5587260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5587313 : List Nat := [1, 2, 2, 2, 1, 2, 1, 5, 2, 5]
def baseStart_5587313 : Nat := 118140960795 + 5587313 * 2 ^ 59
def prefixEnd_5587313 : Nat := 4983230072969 + 3 ^ 40 * 5587313 * 2
def baseEnd_5587313 : Nat := 956325712038201115297307

theorem tailTrace_5587313 : CollatzResearch.WordTrace tailWord_5587313 prefixEnd_5587313 956325712038201115297307 := by
  unfold tailWord_5587313
  simp only [CollatzResearch.WordTrace]
  refine ⟨203786046807126712934814593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135857364538084475289876395 203786046807126712934814593)
  ·
    refine ⟨152839535105345034701110945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203786046807126712934814593 152839535105345034701110945)
    ·
      refine ⟨114629651329008776025833209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152839535105345034701110945 114629651329008776025833209)
      ·
        refine ⟨85972238496756582019374907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114629651329008776025833209 85972238496756582019374907)
        ·
          refine ⟨128958357745134873029062361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85972238496756582019374907 128958357745134873029062361)
          ·
            refine ⟨96718768308851154771796771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128958357745134873029062361 96718768308851154771796771)
            ·
              refine ⟨145078152463276732157695157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96718768308851154771796771 145078152463276732157695157)
              ·
                refine ⟨13601076793432193639783921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 145078152463276732157695157 13601076793432193639783921)
                ·
                  refine ⟨10200807595074145229837941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13601076793432193639783921 10200807595074145229837941)
                  ·
                    refine ⟨956325712038201115297307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10200807595074145229837941 956325712038201115297307)
                    ·
                      rfl

theorem cell23_5587313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 5, 2, 5].length) (baseStart_5587313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5587313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5587313 prefixEnd_5587313 := by exact prefixLift 5587313
  have htrace : WordTrace (prefixWord ++ tailWord_5587313) baseStart_5587313 baseEnd_5587313 := by
    simpa [prefixWord, tailWord_5587313, baseEnd_5587313] using wordTrace_append hprefix tailTrace_5587313
  have hstable : (prefixWord ++ tailWord_5587313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5587313).length < 2 ^ (prefixWord ++ tailWord_5587313).sum := by decide
  have hdescent : baseEnd_5587313 < baseStart_5587313 := by decide
  rcases family_descends (prefixWord ++ tailWord_5587313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5587317 : List Nat := [1, 3, 4, 1, 2, 1, 3, 3, 5]
def baseStart_5587317 : Nat := 118140960795 + 5587317 * 2 ^ 59
def prefixEnd_5587317 : Nat := 4983230072969 + 3 ^ 40 * 5587317 * 2
def baseEnd_5587317 : Nat := 318775465559691258915767

theorem tailTrace_5587317 : CollatzResearch.WordTrace tailWord_5587317 prefixEnd_5587317 318775465559691258915767 := by
  unfold tailWord_5587317
  simp only [CollatzResearch.WordTrace]
  refine ⟨203786192699112221617960205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135857461799408147745306803 203786192699112221617960205)
  ·
    refine ⟨76419822262167083106735077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 203786192699112221617960205 76419822262167083106735077)
    ·
      refine ⟨14328716674156328082512827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76419822262167083106735077 14328716674156328082512827)
      ·
        refine ⟨21493075011234492123769241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14328716674156328082512827 21493075011234492123769241)
        ·
          refine ⟨16119806258425869092826931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21493075011234492123769241 16119806258425869092826931)
          ·
            refine ⟨24179709387638803639240397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16119806258425869092826931 24179709387638803639240397)
            ·
              refine ⟨9067391020364551364715149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24179709387638803639240397 9067391020364551364715149)
              ·
                refine ⟨3400271632636706761768181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9067391020364551364715149 3400271632636706761768181)
                ·
                  refine ⟨318775465559691258915767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3400271632636706761768181 318775465559691258915767)
                  ·
                    rfl

theorem cell23_5587317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 3, 5].length) (baseStart_5587317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5587317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5587317 prefixEnd_5587317 := by exact prefixLift 5587317
  have htrace : WordTrace (prefixWord ++ tailWord_5587317) baseStart_5587317 baseEnd_5587317 := by
    simpa [prefixWord, tailWord_5587317, baseEnd_5587317] using wordTrace_append hprefix tailTrace_5587317
  have hstable : (prefixWord ++ tailWord_5587317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5587317).length < 2 ^ (prefixWord ++ tailWord_5587317).sum := by decide
  have hdescent : baseEnd_5587317 < baseStart_5587317 := by decide
  rcases family_descends (prefixWord ++ tailWord_5587317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5587367 : List Nat := [1, 1, 6, 1, 1, 3, 2, 1, 2, 1, 4]
def baseStart_5587367 : Nat := 118140960795 + 5587367 * 2 ^ 59
def prefixEnd_5587367 : Nat := 4983230072969 + 3 ^ 40 * 5587367 * 2
def baseEnd_5587367 : Nat := 2869004864069946134616673

theorem tailTrace_5587367 : CollatzResearch.WordTrace tailWord_5587367 prefixEnd_5587367 2869004864069946134616673 := by
  unfold tailWord_5587367
  simp only [CollatzResearch.WordTrace]
  refine ⟨203788016348931080157280355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135858677565954053438186903 203788016348931080157280355)
  ·
    refine ⟨305682024523396620235920533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203788016348931080157280355 305682024523396620235920533)
    ·
      refine ⟨14328844899534216573558775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 305682024523396620235920533 14328844899534216573558775)
      ·
        refine ⟨21493267349301324860338163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14328844899534216573558775 21493267349301324860338163)
        ·
          refine ⟨32239901023951987290507245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21493267349301324860338163 32239901023951987290507245)
          ·
            refine ⟨12089962883981995233940217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32239901023951987290507245 12089962883981995233940217)
            ·
              refine ⟨9067472162986496425455163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12089962883981995233940217 9067472162986496425455163)
              ·
                refine ⟨13601208244479744638182745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9067472162986496425455163 13601208244479744638182745)
                ·
                  refine ⟨10200906183359808478637059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13601208244479744638182745 10200906183359808478637059)
                  ·
                    refine ⟨15301359275039712717955589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10200906183359808478637059 15301359275039712717955589)
                    ·
                      refine ⟨2869004864069946134616673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15301359275039712717955589 2869004864069946134616673)
                      ·
                        rfl

theorem cell23_5587367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 1, 2, 1, 4].length) (baseStart_5587367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5587367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5587367 prefixEnd_5587367 := by exact prefixLift 5587367
  have htrace : WordTrace (prefixWord ++ tailWord_5587367) baseStart_5587367 baseEnd_5587367 := by
    simpa [prefixWord, tailWord_5587367, baseEnd_5587367] using wordTrace_append hprefix tailTrace_5587367
  have hstable : (prefixWord ++ tailWord_5587367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5587367).length < 2 ^ (prefixWord ++ tailWord_5587367).sum := by decide
  have hdescent : baseEnd_5587367 < baseStart_5587367 := by decide
  rcases family_descends (prefixWord ++ tailWord_5587367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5587390 : List Nat := [4, 2, 1, 1, 1, 1, 3, 4, 6]
def baseStart_5587390 : Nat := 118140960795 + 5587390 * 2 ^ 59
def prefixEnd_5587390 : Nat := 4983230072969 + 3 ^ 40 * 5587390 * 2
def baseEnd_5587390 : Nat := 318779630458333282736563

theorem tailTrace_5587390 : CollatzResearch.WordTrace tailWord_5587390 prefixEnd_5587390 318779630458333282736563 := by
  unfold tailWord_5587390
  simp only [CollatzResearch.WordTrace]
  refine ⟨25473606903480969385670953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135859236818565170056911749 25473606903480969385670953)
  ·
    refine ⟨19105205177610727039253215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25473606903480969385670953 19105205177610727039253215)
    ·
      refine ⟨28657807766416090558879823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19105205177610727039253215 28657807766416090558879823)
      ·
        refine ⟨42986711649624135838319735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28657807766416090558879823 42986711649624135838319735)
        ·
          refine ⟨64480067474436203757479603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42986711649624135838319735 64480067474436203757479603)
          ·
            refine ⟨96720101211654305636219405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64480067474436203757479603 96720101211654305636219405)
            ·
              refine ⟨36270037954370364613582277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96720101211654305636219405 36270037954370364613582277)
              ·
                refine ⟨6800632116444443365046677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36270037954370364613582277 6800632116444443365046677)
                ·
                  refine ⟨318779630458333282736563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6800632116444443365046677 318779630458333282736563)
                  ·
                    rfl

theorem cell23_5587390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 4, 6].length) (baseStart_5587390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5587390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5587390 prefixEnd_5587390 := by exact prefixLift 5587390
  have htrace : WordTrace (prefixWord ++ tailWord_5587390) baseStart_5587390 baseEnd_5587390 := by
    simpa [prefixWord, tailWord_5587390, baseEnd_5587390] using wordTrace_append hprefix tailTrace_5587390
  have hstable : (prefixWord ++ tailWord_5587390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5587390).length < 2 ^ (prefixWord ++ tailWord_5587390).sum := by decide
  have hdescent : baseEnd_5587390 < baseStart_5587390 := by decide
  rcases family_descends (prefixWord ++ tailWord_5587390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5587417 : List Nat := [1, 2, 1, 2, 4, 1, 3, 2, 3, 1, 3]
def baseStart_5587417 : Nat := 118140960795 + 5587417 * 2 ^ 59
def prefixEnd_5587417 : Nat := 4983230072969 + 3 ^ 40 * 5587417 * 2
def baseEnd_5587417 : Nat := 2869030538102670938991443

theorem tailTrace_5587417 : CollatzResearch.WordTrace tailWord_5587417 prefixEnd_5587417 2869030538102670938991443 := by
  unfold tailWord_5587417
  simp only [CollatzResearch.WordTrace]
  refine ⟨203789839998749938696600505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135859893332499959131067003 203789839998749938696600505)
  ·
    refine ⟨152842379999062454022450379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203789839998749938696600505 152842379999062454022450379)
    ·
      refine ⟨229263569998593681033675569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152842379999062454022450379 229263569998593681033675569)
      ·
        refine ⟨171947677498945260775256677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 229263569998593681033675569 171947677498945260775256677)
        ·
          refine ⟨32240189531052236395360627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 171947677498945260775256677 32240189531052236395360627)
          ·
            refine ⟨48360284296578354593040941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32240189531052236395360627 48360284296578354593040941)
            ·
              refine ⟨18135106611216882972390353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48360284296578354593040941 18135106611216882972390353)
              ·
                refine ⟨13601329958412662229292765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18135106611216882972390353 13601329958412662229292765)
                ·
                  refine ⟨5100498734404748335984787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13601329958412662229292765 5100498734404748335984787)
                  ·
                    refine ⟨7650748101607122503977181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5100498734404748335984787 7650748101607122503977181)
                    ·
                      refine ⟨2869030538102670938991443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7650748101607122503977181 2869030538102670938991443)
                      ·
                        rfl

theorem cell23_5587417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 2, 3, 1, 3].length) (baseStart_5587417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5587417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5587417 prefixEnd_5587417 := by exact prefixLift 5587417
  have htrace : WordTrace (prefixWord ++ tailWord_5587417) baseStart_5587417 baseEnd_5587417 := by
    simpa [prefixWord, tailWord_5587417, baseEnd_5587417] using wordTrace_append hprefix tailTrace_5587417
  have hstable : (prefixWord ++ tailWord_5587417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5587417).length < 2 ^ (prefixWord ++ tailWord_5587417).sum := by decide
  have hdescent : baseEnd_5587417 < baseStart_5587417 := by decide
  rcases family_descends (prefixWord ++ tailWord_5587417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5587433 : List Nat := [1, 2, 1, 1, 1, 2, 1, 5, 3, 6]
def baseStart_5587433 : Nat := 118140960795 + 5587433 * 2 ^ 59
def prefixEnd_5587433 : Nat := 4983230072969 + 3 ^ 40 * 5587433 * 2
def baseEnd_5587433 : Nat := 956346251264380958797123

theorem tailTrace_5587433 : CollatzResearch.WordTrace tailWord_5587433 prefixEnd_5587433 956346251264380958797123 := by
  unfold tailWord_5587433
  simp only [CollatzResearch.WordTrace]
  refine ⟨203790423566691973429182953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135860282377794648952788635 203790423566691973429182953)
  ·
    refine ⟨152842817675018980071887215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203790423566691973429182953 152842817675018980071887215)
    ·
      refine ⟨229264226512528470107830823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152842817675018980071887215 229264226512528470107830823)
      ·
        refine ⟨343896339768792705161746235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229264226512528470107830823 343896339768792705161746235)
        ·
          refine ⟨515844509653189057742619353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 343896339768792705161746235 515844509653189057742619353)
          ·
            refine ⟨386883382239891793306964515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 515844509653189057742619353 386883382239891793306964515)
            ·
              refine ⟨580325073359837689960446773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 386883382239891793306964515 580325073359837689960446773)
              ·
                refine ⟨54405475627484783433791885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 580325073359837689960446773 54405475627484783433791885)
                ·
                  refine ⟨20402053360306793787671957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54405475627484783433791885 20402053360306793787671957)
                  ·
                    refine ⟨956346251264380958797123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20402053360306793787671957 956346251264380958797123)
                    ·
                      rfl

theorem cell23_5587433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 5, 3, 6].length) (baseStart_5587433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5587433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5587433 prefixEnd_5587433 := by exact prefixLift 5587433
  have htrace : WordTrace (prefixWord ++ tailWord_5587433) baseStart_5587433 baseEnd_5587433 := by
    simpa [prefixWord, tailWord_5587433, baseEnd_5587433] using wordTrace_append hprefix tailTrace_5587433
  have hstable : (prefixWord ++ tailWord_5587433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5587433).length < 2 ^ (prefixWord ++ tailWord_5587433).sum := by decide
  have hdescent : baseEnd_5587433 < baseStart_5587433 := by decide
  rcases family_descends (prefixWord ++ tailWord_5587433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5587467 : List Nat := [1, 1, 1, 1, 7, 3, 1, 1, 1, 6]
def baseStart_5587467 : Nat := 118140960795 + 5587467 * 2 ^ 59
def prefixEnd_5587467 : Nat := 4983230072969 + 3 ^ 40 * 5587467 * 2
def baseEnd_5587467 : Nat := 956352070711798581122071

theorem tailTrace_5587467 : CollatzResearch.WordTrace tailWord_5587467 prefixEnd_5587467 956352070711798581122071 := by
  unfold tailWord_5587467
  simp only [CollatzResearch.WordTrace]
  refine ⟨203791663648568797235920655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135861109099045864823947103 203791663648568797235920655)
  ·
    refine ⟨305687495472853195853880983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203791663648568797235920655 305687495472853195853880983)
    ·
      refine ⟨458531243209279793780821475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305687495472853195853880983 458531243209279793780821475)
      ·
        refine ⟨687796864813919690671232213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 458531243209279793780821475 687796864813919690671232213)
        ·
          refine ⟨16120239019076242750107005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 687796864813919690671232213 16120239019076242750107005)
          ·
            refine ⟨6045089632153591031290127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16120239019076242750107005 6045089632153591031290127)
            ·
              refine ⟨9067634448230386546935191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6045089632153591031290127 9067634448230386546935191)
              ·
                refine ⟨13601451672345579820402787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9067634448230386546935191 13601451672345579820402787)
                ·
                  refine ⟨20402177508518369730604181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13601451672345579820402787 20402177508518369730604181)
                  ·
                    refine ⟨956352070711798581122071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20402177508518369730604181 956352070711798581122071)
                    ·
                      rfl

theorem cell23_5587467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 1, 1, 6].length) (baseStart_5587467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5587467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5587467 prefixEnd_5587467 := by exact prefixLift 5587467
  have htrace : WordTrace (prefixWord ++ tailWord_5587467) baseStart_5587467 baseEnd_5587467 := by
    simpa [prefixWord, tailWord_5587467, baseEnd_5587467] using wordTrace_append hprefix tailTrace_5587467
  have hstable : (prefixWord ++ tailWord_5587467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5587467).length < 2 ^ (prefixWord ++ tailWord_5587467).sum := by decide
  have hdescent : baseEnd_5587467 < baseStart_5587467 := by decide
  rcases family_descends (prefixWord ++ tailWord_5587467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5587480 : List Nat := [2, 1, 2, 3, 3, 2, 1, 9]
def baseStart_5587480 : Nat := 118140960795 + 5587480 * 2 ^ 59
def prefixEnd_5587480 : Nat := 4983230072969 + 3 ^ 40 * 5587480 * 2
def baseEnd_5587480 : Nat := 106261588421626081203839

theorem tailTrace_5587480 : CollatzResearch.WordTrace tailWord_5587480 prefixEnd_5587480 106261588421626081203839 := by
  unfold tailWord_5587480
  simp only [CollatzResearch.WordTrace]
  refine ⟨101896068898760850228071947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135861425198347800304095929 101896068898760850228071947)
  ·
    refine ⟨152844103348141275342107921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101896068898760850228071947 152844103348141275342107921)
    ·
      refine ⟨114633077511105956506580941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152844103348141275342107921 114633077511105956506580941)
      ·
        refine ⟨42987404066664733689967853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114633077511105956506580941 42987404066664733689967853)
        ·
          refine ⟨16120276524999275133737945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42987404066664733689967853 16120276524999275133737945)
          ·
            refine ⟨12090207393749456350303459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16120276524999275133737945 12090207393749456350303459)
            ·
              refine ⟨18135311090624184525455189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12090207393749456350303459 18135311090624184525455189)
              ·
                refine ⟨106261588421626081203839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18135311090624184525455189 106261588421626081203839)
                ·
                  rfl

theorem cell23_5587480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 9].length) (baseStart_5587480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5587480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5587480 prefixEnd_5587480 := by exact prefixLift 5587480
  have htrace : WordTrace (prefixWord ++ tailWord_5587480) baseStart_5587480 baseEnd_5587480 := by
    simpa [prefixWord, tailWord_5587480, baseEnd_5587480] using wordTrace_append hprefix tailTrace_5587480
  have hstable : (prefixWord ++ tailWord_5587480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5587480).length < 2 ^ (prefixWord ++ tailWord_5587480).sum := by decide
  have hdescent : baseEnd_5587480 < baseStart_5587480 := by decide
  rcases family_descends (prefixWord ++ tailWord_5587480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5587483 : List Nat := [1, 1, 1, 1, 1, 1, 3, 1, 3, 4, 6]
def baseStart_5587483 : Nat := 118140960795 + 5587483 * 2 ^ 59
def prefixEnd_5587483 : Nat := 4983230072969 + 3 ^ 40 * 5587483 * 2
def baseEnd_5587483 : Nat := 2869064427825867680766139

theorem tailTrace_5587483 : CollatzResearch.WordTrace tailWord_5587483 prefixEnd_5587483 2869064427825867680766139 := by
  unfold tailWord_5587483
  simp only [CollatzResearch.WordTrace]
  refine ⟨203792247216510831968503103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135861498144340554645668735 203792247216510831968503103)
  ·
    refine ⟨305688370824766247952754655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203792247216510831968503103 305688370824766247952754655)
    ·
      refine ⟨458532556237149371929131983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305688370824766247952754655 458532556237149371929131983)
      ·
        refine ⟨687798834355724057893697975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 458532556237149371929131983 687798834355724057893697975)
        ·
          refine ⟨1031698251533586086840546963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 687798834355724057893697975 1031698251533586086840546963)
          ·
            refine ⟨1547547377300379130260820445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1031698251533586086840546963 1547547377300379130260820445)
            ·
              refine ⟨580330266487642173847807667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1547547377300379130260820445 580330266487642173847807667)
              ·
                refine ⟨870495399731463260771711501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 580330266487642173847807667 870495399731463260771711501)
                ·
                  refine ⟨326435774899298722789391813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 870495399731463260771711501 326435774899298722789391813)
                  ·
                    refine ⟨61206707793618510523010965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 326435774899298722789391813 61206707793618510523010965)
                    ·
                      refine ⟨2869064427825867680766139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61206707793618510523010965 2869064427825867680766139)
                      ·
                        rfl

theorem cell23_5587483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 4, 6].length) (baseStart_5587483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5587483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5587483 prefixEnd_5587483 := by exact prefixLift 5587483
  have htrace : WordTrace (prefixWord ++ tailWord_5587483) baseStart_5587483 baseEnd_5587483 := by
    simpa [prefixWord, tailWord_5587483, baseEnd_5587483] using wordTrace_append hprefix tailTrace_5587483
  have hstable : (prefixWord ++ tailWord_5587483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5587483).length < 2 ^ (prefixWord ++ tailWord_5587483).sum := by decide
  have hdescent : baseEnd_5587483 < baseStart_5587483 := by decide
  rcases family_descends (prefixWord ++ tailWord_5587483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5587507 : List Nat := [1, 1, 1, 2, 4, 2, 1, 3, 4, 1, 3]
def baseStart_5587507 : Nat := 118140960795 + 5587507 * 2 ^ 59
def prefixEnd_5587507 : Nat := 4983230072969 + 3 ^ 40 * 5587507 * 2
def baseEnd_5587507 : Nat := 2869076751361575586866029

theorem tailTrace_5587507 : CollatzResearch.WordTrace tailWord_5587507 prefixEnd_5587507 2869076751361575586866029 := by
  unfold tailWord_5587507
  simp only [CollatzResearch.WordTrace]
  refine ⟨203793122568423884067376775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135862081712282589378251183 203793122568423884067376775)
  ·
    refine ⟨305689683852635826101065163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203793122568423884067376775 305689683852635826101065163)
    ·
      refine ⟨458534525778953739151597745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305689683852635826101065163 458534525778953739151597745)
      ·
        refine ⟨343900894334215304363698309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 458534525778953739151597745 343900894334215304363698309)
        ·
          refine ⟨64481417687665369568193433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 343900894334215304363698309 64481417687665369568193433)
          ·
            refine ⟨48361063265749027176145075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64481417687665369568193433 48361063265749027176145075)
            ·
              refine ⟨72541594898623540764217613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48361063265749027176145075 72541594898623540764217613)
              ·
                refine ⟨27203098086983827786581605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72541594898623540764217613 27203098086983827786581605)
                ·
                  refine ⟨5100580891309467709984051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27203098086983827786581605 5100580891309467709984051)
                  ·
                    refine ⟨7650871336964201564976077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5100580891309467709984051 7650871336964201564976077)
                    ·
                      refine ⟨2869076751361575586866029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7650871336964201564976077 2869076751361575586866029)
                      ·
                        rfl

theorem cell23_5587507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 3, 4, 1, 3].length) (baseStart_5587507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5587507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5587507 prefixEnd_5587507 := by exact prefixLift 5587507
  have htrace : WordTrace (prefixWord ++ tailWord_5587507) baseStart_5587507 baseEnd_5587507 := by
    simpa [prefixWord, tailWord_5587507, baseEnd_5587507] using wordTrace_append hprefix tailTrace_5587507
  have hstable : (prefixWord ++ tailWord_5587507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5587507).length < 2 ^ (prefixWord ++ tailWord_5587507).sum := by decide
  have hdescent : baseEnd_5587507 < baseStart_5587507 := by decide
  rcases family_descends (prefixWord ++ tailWord_5587507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5587564 : List Nat := [2, 2, 1, 1, 3, 1, 2, 3, 4, 2, 2]
def baseStart_5587564 : Nat := 118140960795 + 5587564 * 2 ^ 59
def prefixEnd_5587564 : Nat := 4983230072969 + 3 ^ 40 * 5587564 * 2
def baseEnd_5587564 : Nat := 2869106019758881863853267

theorem tailTrace_5587564 : CollatzResearch.WordTrace tailWord_5587564 prefixEnd_5587564 2869106019758881863853267 := by
  unfold tailWord_5587564
  simp only [CollatzResearch.WordTrace]
  refine ⟨101897600764608691401100873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135863467686144921868134497 101897600764608691401100873)
  ·
    refine ⟨76423200573456518550825655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101897600764608691401100873 76423200573456518550825655)
    ·
      refine ⟨114634800860184777826238483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76423200573456518550825655 114634800860184777826238483)
      ·
        refine ⟨171952201290277166739357725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114634800860184777826238483 171952201290277166739357725)
        ·
          refine ⟨64482075483853937527259147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 171952201290277166739357725 64482075483853937527259147)
          ·
            refine ⟨96723113225780906290888721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64482075483853937527259147 96723113225780906290888721)
            ·
              refine ⟨72542334919335679718166541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96723113225780906290888721 72542334919335679718166541)
              ·
                refine ⟨27203375594750879894312453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72542334919335679718166541 27203375594750879894312453)
                ·
                  refine ⟨5100632924015789980183585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27203375594750879894312453 5100632924015789980183585)
                  ·
                    refine ⟨3825474693011842485137689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5100632924015789980183585 3825474693011842485137689)
                    ·
                      refine ⟨2869106019758881863853267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3825474693011842485137689 2869106019758881863853267)
                      ·
                        rfl

theorem cell23_5587564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 2, 2].length) (baseStart_5587564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5587564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5587564 prefixEnd_5587564 := by exact prefixLift 5587564
  have htrace : WordTrace (prefixWord ++ tailWord_5587564) baseStart_5587564 baseEnd_5587564 := by
    simpa [prefixWord, tailWord_5587564, baseEnd_5587564] using wordTrace_append hprefix tailTrace_5587564
  have hstable : (prefixWord ++ tailWord_5587564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5587564).length < 2 ^ (prefixWord ++ tailWord_5587564).sum := by decide
  have hdescent : baseEnd_5587564 < baseStart_5587564 := by decide
  rcases family_descends (prefixWord ++ tailWord_5587564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5587574 : List Nat := [5, 1, 1, 2, 3, 1, 1, 1, 2, 6]
def baseStart_5587574 : Nat := 118140960795 + 5587574 * 2 ^ 59
def prefixEnd_5587574 : Nat := 4983230072969 + 3 ^ 40 * 5587574 * 2
def baseEnd_5587574 : Nat := 956370384855142274909407

theorem tailTrace_5587574 : CollatzResearch.WordTrace tailWord_5587574 prefixEnd_5587574 956370384855142274909407 := by
  unfold tailWord_5587574
  simp only [CollatzResearch.WordTrace]
  refine ⟨12737222891198822156879111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 135863710839454103006710517 12737222891198822156879111)
  ·
    refine ⟨19105834336798233235318667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12737222891198822156879111 19105834336798233235318667)
    ·
      refine ⟨28658751505197349852978001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19105834336798233235318667 28658751505197349852978001)
      ·
        refine ⟨21494063628898012389733501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28658751505197349852978001 21494063628898012389733501)
        ·
          refine ⟨8060273860836754646150063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21494063628898012389733501 8060273860836754646150063)
          ·
            refine ⟨12090410791255131969225095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8060273860836754646150063 12090410791255131969225095)
            ·
              refine ⟨18135616186882697953837643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12090410791255131969225095 18135616186882697953837643)
              ·
                refine ⟨27203424280324046930756465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18135616186882697953837643 27203424280324046930756465)
                ·
                  refine ⟨20402568210243035198067349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27203424280324046930756465 20402568210243035198067349)
                  ·
                    refine ⟨956370384855142274909407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20402568210243035198067349 956370384855142274909407)
                    ·
                      rfl

theorem cell23_5587574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 1, 2, 6].length) (baseStart_5587574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5587574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5587574 prefixEnd_5587574 := by exact prefixLift 5587574
  have htrace : WordTrace (prefixWord ++ tailWord_5587574) baseStart_5587574 baseEnd_5587574 := by
    simpa [prefixWord, tailWord_5587574, baseEnd_5587574] using wordTrace_append hprefix tailTrace_5587574
  have hstable : (prefixWord ++ tailWord_5587574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5587574).length < 2 ^ (prefixWord ++ tailWord_5587574).sum := by decide
  have hdescent : baseEnd_5587574 < baseStart_5587574 := by decide
  rcases family_descends (prefixWord ++ tailWord_5587574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5587577 : List Nat := [1, 2, 1, 3, 3, 3, 1, 1, 2, 2, 4]
def baseStart_5587577 : Nat := 118140960795 + 5587577 * 2 ^ 59
def prefixEnd_5587577 : Nat := 4983230072969 + 3 ^ 40 * 5587577 * 2
def baseEnd_5587577 : Nat := 2869112695007390312990707

theorem tailTrace_5587577 : CollatzResearch.WordTrace tailWord_5587577 prefixEnd_5587577 2869112695007390312990707 := by
  unfold tailWord_5587577
  simp only [CollatzResearch.WordTrace]
  refine ⟨203795675678170286022424985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135863783785446857348283323 203795675678170286022424985)
  ·
    refine ⟨152846756758627714516818739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203795675678170286022424985 152846756758627714516818739)
    ·
      refine ⟨229270135137941571775228109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152846756758627714516818739 229270135137941571775228109)
      ·
        refine ⟨85976300676728089415710541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 229270135137941571775228109 85976300676728089415710541)
        ·
          refine ⟨32241112753773033530891453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85976300676728089415710541 32241112753773033530891453)
          ·
            refine ⟨12090417282664887574084295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32241112753773033530891453 12090417282664887574084295)
            ·
              refine ⟨18135625923997331361126443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12090417282664887574084295 18135625923997331361126443)
              ·
                refine ⟨27203438885995997041689665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18135625923997331361126443 27203438885995997041689665)
                ·
                  refine ⟨20402579164496997781267249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27203438885995997041689665 20402579164496997781267249)
                  ·
                    refine ⟨15301934373372748335950437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20402579164496997781267249 15301934373372748335950437)
                    ·
                      refine ⟨2869112695007390312990707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15301934373372748335950437 2869112695007390312990707)
                      ·
                        rfl

theorem cell23_5587577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 1, 2, 2, 4].length) (baseStart_5587577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5587577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5587577 prefixEnd_5587577 := by exact prefixLift 5587577
  have htrace : WordTrace (prefixWord ++ tailWord_5587577) baseStart_5587577 baseEnd_5587577 := by
    simpa [prefixWord, tailWord_5587577, baseEnd_5587577] using wordTrace_append hprefix tailTrace_5587577
  have hstable : (prefixWord ++ tailWord_5587577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5587577).length < 2 ^ (prefixWord ++ tailWord_5587577).sum := by decide
  have hdescent : baseEnd_5587577 < baseStart_5587577 := by decide
  rcases family_descends (prefixWord ++ tailWord_5587577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5587581 : List Nat := [1, 4, 1, 1, 5, 1, 2, 1, 1, 4, 2]
def baseStart_5587581 : Nat := 118140960795 + 5587581 * 2 ^ 59
def prefixEnd_5587581 : Nat := 4983230072969 + 3 ^ 40 * 5587581 * 2
def baseEnd_5587581 : Nat := 2869114748930008297340689

theorem tailTrace_5587581 : CollatzResearch.WordTrace tailWord_5587581 prefixEnd_5587581 2869114748930008297340689 := by
  unfold tailWord_5587581
  simp only [CollatzResearch.WordTrace]
  refine ⟨203795821570155794705570597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135863881046770529803713731 203795821570155794705570597)
  ·
    refine ⟨38211716544404211507294487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 203795821570155794705570597 38211716544404211507294487)
    ·
      refine ⟨57317574816606317260941731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38211716544404211507294487 57317574816606317260941731)
      ·
        refine ⟨85976362224909475891412597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57317574816606317260941731 85976362224909475891412597)
        ·
          refine ⟨8060283958585263364819931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 85976362224909475891412597 8060283958585263364819931)
          ·
            refine ⟨12090425937877895047229897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8060283958585263364819931 12090425937877895047229897)
            ·
              refine ⟨9067819453408421285422423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12090425937877895047229897 9067819453408421285422423)
              ·
                refine ⟨13601729180112631928133635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9067819453408421285422423 13601729180112631928133635)
                ·
                  refine ⟨20402593770168947892200453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13601729180112631928133635 20402593770168947892200453)
                  ·
                    refine ⟨3825486331906677729787585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20402593770168947892200453 3825486331906677729787585)
                    ·
                      refine ⟨2869114748930008297340689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3825486331906677729787585 2869114748930008297340689)
                      ·
                        rfl

theorem cell23_5587581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 1, 1, 4, 2].length) (baseStart_5587581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5587581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5587581 prefixEnd_5587581 := by exact prefixLift 5587581
  have htrace : WordTrace (prefixWord ++ tailWord_5587581) baseStart_5587581 baseEnd_5587581 := by
    simpa [prefixWord, tailWord_5587581, baseEnd_5587581] using wordTrace_append hprefix tailTrace_5587581
  have hstable : (prefixWord ++ tailWord_5587581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5587581).length < 2 ^ (prefixWord ++ tailWord_5587581).sum := by decide
  have hdescent : baseEnd_5587581 < baseStart_5587581 := by decide
  rcases family_descends (prefixWord ++ tailWord_5587581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5587614 : List Nat := [4, 3, 1, 1, 1, 1, 1, 1, 4, 3, 3]
def baseStart_5587614 : Nat := 118140960795 + 5587614 * 2 ^ 59
def prefixEnd_5587614 : Nat := 4983230072969 + 3 ^ 40 * 5587614 * 2
def baseEnd_5587614 : Nat := 2869131693791606668228037

theorem tailTrace_5587614 : CollatzResearch.WordTrace tailWord_5587614 prefixEnd_5587614 2869131693791606668228037 := by
  unfold tailWord_5587614
  simp only [CollatzResearch.WordTrace]
  refine ⟨25474628147379530167690237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135864683452690827561014597 25474628147379530167690237)
  ·
    refine ⟨9552985555267323812883839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25474628147379530167690237 9552985555267323812883839)
    ·
      refine ⟨14329478332900985719325759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9552985555267323812883839 14329478332900985719325759)
      ·
        refine ⟨21494217499351478578988639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14329478332900985719325759 21494217499351478578988639)
        ·
          refine ⟨32241326249027217868482959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21494217499351478578988639 32241326249027217868482959)
          ·
            refine ⟨48361989373540826802724439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32241326249027217868482959 48361989373540826802724439)
            ·
              refine ⟨72542984060311240204086659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48361989373540826802724439 72542984060311240204086659)
              ·
                refine ⟨108814476090466860306129989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72542984060311240204086659 108814476090466860306129989)
                ·
                  refine ⟨20402714266962536307399373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 108814476090466860306129989 20402714266962536307399373)
                  ·
                    refine ⟨7651017850110951115274765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20402714266962536307399373 7651017850110951115274765)
                    ·
                      refine ⟨2869131693791606668228037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7651017850110951115274765 2869131693791606668228037)
                      ·
                        rfl

theorem cell23_5587614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 4, 3, 3].length) (baseStart_5587614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5587614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5587614 prefixEnd_5587614 := by exact prefixLift 5587614
  have htrace : WordTrace (prefixWord ++ tailWord_5587614) baseStart_5587614 baseEnd_5587614 := by
    simpa [prefixWord, tailWord_5587614, baseEnd_5587614] using wordTrace_append hprefix tailTrace_5587614
  have hstable : (prefixWord ++ tailWord_5587614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5587614).length < 2 ^ (prefixWord ++ tailWord_5587614).sum := by decide
  have hdescent : baseEnd_5587614 < baseStart_5587614 := by decide
  rcases family_descends (prefixWord ++ tailWord_5587614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5587657 : List Nat := [1, 2, 1, 1, 2, 1, 1, 1, 8, 2, 3]
def baseStart_5587657 : Nat := 118140960795 + 5587657 * 2 ^ 59
def prefixEnd_5587657 : Nat := 4983230072969 + 3 ^ 40 * 5587657 * 2
def baseEnd_5587657 : Nat := 2869153773459749999990339

theorem tailTrace_5587657 : CollatzResearch.WordTrace tailWord_5587657 prefixEnd_5587657 2869153773459749999990339 := by
  unfold tailWord_5587657
  simp only [CollatzResearch.WordTrace]
  refine ⟨203798593517880459685337225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135865729011920306456891483 203798593517880459685337225)
  ·
    refine ⟨152848945138410344764002919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203798593517880459685337225 152848945138410344764002919)
    ·
      refine ⟨229273417707615517146004379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152848945138410344764002919 229273417707615517146004379)
      ·
        refine ⟨343910126561423275719006569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229273417707615517146004379 343910126561423275719006569)
        ·
          refine ⟨257932594921067456789254927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 343910126561423275719006569 257932594921067456789254927)
          ·
            refine ⟨386898892381601185183882391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 257932594921067456789254927 386898892381601185183882391)
            ·
              refine ⟨580348338572401777775823587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 386898892381601185183882391 580348338572401777775823587)
              ·
                refine ⟨870522507858602666663735381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 580348338572401777775823587 870522507858602666663735381)
                ·
                  refine ⟨10201435638967999999965649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 870522507858602666663735381 10201435638967999999965649)
                  ·
                    refine ⟨7651076729225999999974237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10201435638967999999965649 7651076729225999999974237)
                    ·
                      refine ⟨2869153773459749999990339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7651076729225999999974237 2869153773459749999990339)
                      ·
                        rfl

theorem cell23_5587657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 8, 2, 3].length) (baseStart_5587657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5587657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5587657 prefixEnd_5587657 := by exact prefixLift 5587657
  have htrace : WordTrace (prefixWord ++ tailWord_5587657) baseStart_5587657 baseEnd_5587657 := by
    simpa [prefixWord, tailWord_5587657, baseEnd_5587657] using wordTrace_append hprefix tailTrace_5587657
  have hstable : (prefixWord ++ tailWord_5587657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5587657).length < 2 ^ (prefixWord ++ tailWord_5587657).sum := by decide
  have hdescent : baseEnd_5587657 < baseStart_5587657 := by decide
  rcases family_descends (prefixWord ++ tailWord_5587657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5587674 : List Nat := [3, 1, 1, 2, 2, 2, 3, 2, 2, 2, 3]
def baseStart_5587674 : Nat := 118140960795 + 5587674 * 2 ^ 59
def prefixEnd_5587674 : Nat := 4983230072969 + 3 ^ 40 * 5587674 * 2
def baseEnd_5587674 : Nat := 2869162502630876433477761

theorem tailTrace_5587674 : CollatzResearch.WordTrace tailWord_5587674 prefixEnd_5587674 2869162502630876433477761 := by
  unfold tailWord_5587674
  simp only [CollatzResearch.WordTrace]
  refine ⟨50949803389704717897176519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135866142372545914392470717 50949803389704717897176519)
  ·
    refine ⟨76424705084557076845764779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50949803389704717897176519 76424705084557076845764779)
    ·
      refine ⟨114637057626835615268647169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76424705084557076845764779 114637057626835615268647169)
      ·
        refine ⟨85977793220126711451485377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114637057626835615268647169 85977793220126711451485377)
        ·
          refine ⟨64483344915095033588614033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85977793220126711451485377 64483344915095033588614033)
          ·
            refine ⟨48362508686321275191460525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64483344915095033588614033 48362508686321275191460525)
            ·
              refine ⟨18135940757370478196797697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48362508686321275191460525 18135940757370478196797697)
              ·
                refine ⟨13601955568027858647598273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18135940757370478196797697 13601955568027858647598273)
                ·
                  refine ⟨10201466676020893985698705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13601955568027858647598273 10201466676020893985698705)
                  ·
                    refine ⟨7651100007015670489274029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10201466676020893985698705 7651100007015670489274029)
                    ·
                      refine ⟨2869162502630876433477761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7651100007015670489274029 2869162502630876433477761)
                      ·
                        rfl

theorem cell23_5587674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 2, 2, 2, 3].length) (baseStart_5587674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5587674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5587674 prefixEnd_5587674 := by exact prefixLift 5587674
  have htrace : WordTrace (prefixWord ++ tailWord_5587674) baseStart_5587674 baseEnd_5587674 := by
    simpa [prefixWord, tailWord_5587674, baseEnd_5587674] using wordTrace_append hprefix tailTrace_5587674
  have hstable : (prefixWord ++ tailWord_5587674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5587674).length < 2 ^ (prefixWord ++ tailWord_5587674).sum := by decide
  have hdescent : baseEnd_5587674 < baseStart_5587674 := by decide
  rcases family_descends (prefixWord ++ tailWord_5587674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
