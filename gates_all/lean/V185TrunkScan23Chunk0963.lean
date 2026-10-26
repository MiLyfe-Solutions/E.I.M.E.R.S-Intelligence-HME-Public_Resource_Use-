import V185TrunkScan23Chunk0962

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5701449 : List Nat := [1, 2, 1, 1, 2, 4, 2, 1, 1, 3, 5]
def baseStart_5701449 : Nat := 118140960795 + 5701449 * 2 ^ 59
def prefixEnd_5701449 : Nat := 4983230072969 + 3 ^ 40 * 5701449 * 2
def baseEnd_5701449 : Nat := 2927583764096168788267019

theorem tailTrace_5701449 : CollatzResearch.WordTrace tailWord_5701449 prefixEnd_5701449 2927583764096168788267019 := by
  unfold tailWord_5701449
  simp only [CollatzResearch.WordTrace]
  refine ⟨207948928721631477811707401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138632619147754318541138267 207948928721631477811707401)
  ·
    refine ⟨155961696541223608358780551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207948928721631477811707401 155961696541223608358780551)
    ·
      refine ⟨233942544811835412538170827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155961696541223608358780551 233942544811835412538170827)
      ·
        refine ⟨350913817217753118807256241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233942544811835412538170827 350913817217753118807256241)
        ·
          refine ⟨263185362913314839105442181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 350913817217753118807256241 263185362913314839105442181)
          ·
            refine ⟨49347255546246532332270409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 263185362913314839105442181 49347255546246532332270409)
            ·
              refine ⟨37010441659684899249202807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49347255546246532332270409 37010441659684899249202807)
              ·
                refine ⟨55515662489527348873804211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37010441659684899249202807 55515662489527348873804211)
                ·
                  refine ⟨83273493734291023310706317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55515662489527348873804211 83273493734291023310706317)
                  ·
                    refine ⟨31227560150359133741514869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 83273493734291023310706317 31227560150359133741514869)
                    ·
                      refine ⟨2927583764096168788267019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31227560150359133741514869 2927583764096168788267019)
                      ·
                        rfl

theorem cell23_5701449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 1, 1, 3, 5].length) (baseStart_5701449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5701449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5701449 prefixEnd_5701449 := by exact prefixLift 5701449
  have htrace : WordTrace (prefixWord ++ tailWord_5701449) baseStart_5701449 baseEnd_5701449 := by
    simpa [prefixWord, tailWord_5701449, baseEnd_5701449] using wordTrace_append hprefix tailTrace_5701449
  have hstable : (prefixWord ++ tailWord_5701449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5701449).length < 2 ^ (prefixWord ++ tailWord_5701449).sum := by decide
  have hdescent : baseEnd_5701449 < baseStart_5701449 := by decide
  rcases family_descends (prefixWord ++ tailWord_5701449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5701536 : List Nat := [2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 4]
def baseStart_5701536 : Nat := 118140960795 + 5701536 * 2 ^ 59
def prefixEnd_5701536 : Nat := 4983230072969 + 3 ^ 40 * 5701536 * 2
def baseEnd_5701536 : Nat := 2927628436913109947879119

theorem tailTrace_5701536 : CollatzResearch.WordTrace tailWord_5701536 prefixEnd_5701536 2927628436913109947879119 := by
  unfold tailWord_5701536
  simp only [CollatzResearch.WordTrace]
  refine ⟨103976050936158145835062231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138634734581544194446749641 103976050936158145835062231)
  ·
    refine ⟨155964076404237218752593347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103976050936158145835062231 155964076404237218752593347)
    ·
      refine ⟨233946114606355828128890021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155964076404237218752593347 233946114606355828128890021)
      ·
        refine ⟨43864896488691717774166879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 233946114606355828128890021 43864896488691717774166879)
        ·
          refine ⟨65797344733037576661250319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43864896488691717774166879 65797344733037576661250319)
          ·
            refine ⟨98696017099556364991875479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65797344733037576661250319 98696017099556364991875479)
            ·
              refine ⟨148044025649334547487813219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98696017099556364991875479 148044025649334547487813219)
              ·
                refine ⟨222066038474001821231719829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 148044025649334547487813219 222066038474001821231719829)
                ·
                  refine ⟨10409345553468835370236867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 222066038474001821231719829 10409345553468835370236867)
                  ·
                    refine ⟨15614018330203253055355301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10409345553468835370236867 15614018330203253055355301)
                    ·
                      refine ⟨2927628436913109947879119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15614018330203253055355301 2927628436913109947879119)
                      ·
                        rfl

theorem cell23_5701536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 4].length) (baseStart_5701536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5701536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5701536 prefixEnd_5701536 := by exact prefixLift 5701536
  have htrace : WordTrace (prefixWord ++ tailWord_5701536) baseStart_5701536 baseEnd_5701536 := by
    simpa [prefixWord, tailWord_5701536, baseEnd_5701536] using wordTrace_append hprefix tailTrace_5701536
  have hstable : (prefixWord ++ tailWord_5701536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5701536).length < 2 ^ (prefixWord ++ tailWord_5701536).sum := by decide
  have hdescent : baseEnd_5701536 < baseStart_5701536 := by decide
  rcases family_descends (prefixWord ++ tailWord_5701536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5701553 : List Nat := [1, 2, 2, 4, 2, 1, 1, 3, 2, 1, 4]
def baseStart_5701553 : Nat := 118140960795 + 5701553 * 2 ^ 59
def prefixEnd_5701553 : Nat := 4983230072969 + 3 ^ 40 * 5701553 * 2
def baseEnd_5701553 : Nat := 2927637166084236381366541

theorem tailTrace_5701553 : CollatzResearch.WordTrace tailWord_5701553 prefixEnd_5701553 2927637166084236381366541 := by
  unfold tailWord_5701553
  simp only [CollatzResearch.WordTrace]
  refine ⟨207952721913254703573493313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138635147942169802382328875 207952721913254703573493313)
  ·
    refine ⟨155964541434941027680119985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207952721913254703573493313 155964541434941027680119985)
    ·
      refine ⟨116973406076205770760089989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155964541434941027680119985 116973406076205770760089989)
      ·
        refine ⟨21932513639288582017516873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 116973406076205770760089989 21932513639288582017516873)
        ·
          refine ⟨16449385229466436513137655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21932513639288582017516873 16449385229466436513137655)
          ·
            refine ⟨24674077844199654769706483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16449385229466436513137655 24674077844199654769706483)
            ·
              refine ⟨37011116766299482154559725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24674077844199654769706483 37011116766299482154559725)
              ·
                refine ⟨13879168787362305807959897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37011116766299482154559725 13879168787362305807959897)
                ·
                  refine ⟨10409376590521729355969923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13879168787362305807959897 10409376590521729355969923)
                  ·
                    refine ⟨15614064885782594033954885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10409376590521729355969923 15614064885782594033954885)
                    ·
                      refine ⟨2927637166084236381366541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15614064885782594033954885 2927637166084236381366541)
                      ·
                        rfl

theorem cell23_5701553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_5701553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5701553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5701553 prefixEnd_5701553 := by exact prefixLift 5701553
  have htrace : WordTrace (prefixWord ++ tailWord_5701553) baseStart_5701553 baseEnd_5701553 := by
    simpa [prefixWord, tailWord_5701553, baseEnd_5701553] using wordTrace_append hprefix tailTrace_5701553
  have hstable : (prefixWord ++ tailWord_5701553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5701553).length < 2 ^ (prefixWord ++ tailWord_5701553).sum := by decide
  have hdescent : baseEnd_5701553 < baseStart_5701553 := by decide
  rcases family_descends (prefixWord ++ tailWord_5701553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5701607 : List Nat := [1, 1, 5, 2, 3, 2, 1, 1, 2, 2, 3]
def baseStart_5701607 : Nat := 118140960795 + 5701607 * 2 ^ 59
def prefixEnd_5701607 : Nat := 4983230072969 + 3 ^ 40 * 5701607 * 2
def baseEnd_5701607 : Nat := 2927664894039579170091293

theorem tailTrace_5701607 : CollatzResearch.WordTrace tailWord_5701607 prefixEnd_5701607 2927664894039579170091293 := by
  unfold tailWord_5701607
  simp only [CollatzResearch.WordTrace]
  refine ⟨207954691455059070795959075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138636460970039380530639383 207954691455059070795959075)
  ·
    refine ⟨311932037182588606193938613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207954691455059070795959075 311932037182588606193938613)
    ·
      refine ⟨29243628485867681830681745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 311932037182588606193938613 29243628485867681830681745)
      ·
        refine ⟨21932721364400761373011309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29243628485867681830681745 21932721364400761373011309)
        ·
          refine ⟨8224770511650285514879241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21932721364400761373011309 8224770511650285514879241)
          ·
            refine ⟨6168577883737714136159431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8224770511650285514879241 6168577883737714136159431)
            ·
              refine ⟨9252866825606571204239147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6168577883737714136159431 9252866825606571204239147)
              ·
                refine ⟨13879300238409856806358721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9252866825606571204239147 13879300238409856806358721)
                ·
                  refine ⟨10409475178807392604769041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13879300238409856806358721 10409475178807392604769041)
                  ·
                    refine ⟨7807106384105544453576781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10409475178807392604769041 7807106384105544453576781)
                    ·
                      refine ⟨2927664894039579170091293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7807106384105544453576781 2927664894039579170091293)
                      ·
                        rfl

theorem cell23_5701607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 1, 2, 2, 3].length) (baseStart_5701607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5701607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5701607 prefixEnd_5701607 := by exact prefixLift 5701607
  have htrace : WordTrace (prefixWord ++ tailWord_5701607) baseStart_5701607 baseEnd_5701607 := by
    simpa [prefixWord, tailWord_5701607, baseEnd_5701607] using wordTrace_append hprefix tailTrace_5701607
  have hstable : (prefixWord ++ tailWord_5701607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5701607).length < 2 ^ (prefixWord ++ tailWord_5701607).sum := by decide
  have hdescent : baseEnd_5701607 < baseStart_5701607 := by decide
  rcases family_descends (prefixWord ++ tailWord_5701607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5701637 : List Nat := [1, 3, 1, 1, 2, 4, 2, 4, 1, 1, 3]
def baseStart_5701637 : Nat := 118140960795 + 5701637 * 2 ^ 59
def prefixEnd_5701637 : Nat := 4983230072969 + 3 ^ 40 * 5701637 * 2
def baseEnd_5701637 : Nat := 2927680298459214052716155

theorem tailTrace_5701637 : CollatzResearch.WordTrace tailWord_5701637 prefixEnd_5701637 2927680298459214052716155 := by
  unfold tailWord_5701637
  simp only [CollatzResearch.WordTrace]
  refine ⟨207955785644950385919551165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138637190429966923946367443 207955785644950385919551165)
  ·
    refine ⟨77983419616856394719831687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207955785644950385919551165 77983419616856394719831687)
    ·
      refine ⟨116975129425284592079747531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77983419616856394719831687 116975129425284592079747531)
      ·
        refine ⟨175462694137926888119621297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116975129425284592079747531 175462694137926888119621297)
        ·
          refine ⟨131597020603445166089715973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175462694137926888119621297 131597020603445166089715973)
          ·
            refine ⟨24674441363145968641821745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 131597020603445166089715973 24674441363145968641821745)
            ·
              refine ⟨18505831022359476481366309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24674441363145968641821745 18505831022359476481366309)
              ·
                refine ⟨3469843316692401840256183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18505831022359476481366309 3469843316692401840256183)
                ·
                  refine ⟨5204764975038602760384275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3469843316692401840256183 5204764975038602760384275)
                  ·
                    refine ⟨7807147462557904140576413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5204764975038602760384275 7807147462557904140576413)
                    ·
                      refine ⟨2927680298459214052716155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7807147462557904140576413 2927680298459214052716155)
                      ·
                        rfl

theorem cell23_5701637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 4, 1, 1, 3].length) (baseStart_5701637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5701637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5701637 prefixEnd_5701637 := by exact prefixLift 5701637
  have htrace : WordTrace (prefixWord ++ tailWord_5701637) baseStart_5701637 baseEnd_5701637 := by
    simpa [prefixWord, tailWord_5701637, baseEnd_5701637] using wordTrace_append hprefix tailTrace_5701637
  have hstable : (prefixWord ++ tailWord_5701637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5701637).length < 2 ^ (prefixWord ++ tailWord_5701637).sum := by decide
  have hdescent : baseEnd_5701637 < baseStart_5701637 := by decide
  rcases family_descends (prefixWord ++ tailWord_5701637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5701660 : List Nat := [2, 2, 3, 1, 3, 1, 1, 4, 1, 1, 4]
def baseStart_5701660 : Nat := 118140960795 + 5701660 * 2 ^ 59
def prefixEnd_5701660 : Nat := 4983230072969 + 3 ^ 40 * 5701660 * 2
def baseEnd_5701660 : Nat := 2927692108514267462728549

theorem tailTrace_5701660 : CollatzResearch.WordTrace tailWord_5701660 prefixEnd_5701660 2927692108514267462728549 := by
  unfold tailWord_5701660
  simp only [CollatzResearch.WordTrace]
  refine ⟨103978312261933530423819217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138637749682578040565092289 103978312261933530423819217)
  ·
    refine ⟨77983734196450147817864413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103978312261933530423819217 77983734196450147817864413)
    ·
      refine ⟨29243900323668805431699155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77983734196450147817864413 29243900323668805431699155)
      ·
        refine ⟨43865850485503208147548733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29243900323668805431699155 43865850485503208147548733)
        ·
          refine ⟨16449693932063703055330775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43865850485503208147548733 16449693932063703055330775)
          ·
            refine ⟨24674540898095554582996163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16449693932063703055330775 24674540898095554582996163)
            ·
              refine ⟨37011811347143331874494245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24674540898095554582996163 37011811347143331874494245)
              ·
                refine ⟨6939714627589374726467671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37011811347143331874494245 6939714627589374726467671)
                ·
                  refine ⟨10409571941384062089701507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6939714627589374726467671 10409571941384062089701507)
                  ·
                    refine ⟨15614357912076093134552261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10409571941384062089701507 15614357912076093134552261)
                    ·
                      refine ⟨2927692108514267462728549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15614357912076093134552261 2927692108514267462728549)
                      ·
                        rfl

theorem cell23_5701660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 4, 1, 1, 4].length) (baseStart_5701660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5701660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5701660 prefixEnd_5701660 := by exact prefixLift 5701660
  have htrace : WordTrace (prefixWord ++ tailWord_5701660) baseStart_5701660 baseEnd_5701660 := by
    simpa [prefixWord, tailWord_5701660, baseEnd_5701660] using wordTrace_append hprefix tailTrace_5701660
  have hstable : (prefixWord ++ tailWord_5701660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5701660).length < 2 ^ (prefixWord ++ tailWord_5701660).sum := by decide
  have hdescent : baseEnd_5701660 < baseStart_5701660 := by decide
  rcases family_descends (prefixWord ++ tailWord_5701660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5701680 : List Nat := [2, 1, 1, 1, 2, 5, 2, 3, 1, 2, 3]
def baseStart_5701680 : Nat := 118140960795 + 5701680 * 2 ^ 59
def prefixEnd_5701680 : Nat := 4983230072969 + 3 ^ 40 * 5701680 * 2
def baseEnd_5701680 : Nat := 2927702378127357384478457

theorem tailTrace_5701680 : CollatzResearch.WordTrace tailWord_5701680 prefixEnd_5701680 2927702378127357384478457 := by
  unfold tailWord_5701680
  simp only [CollatzResearch.WordTrace]
  refine ⟨103978676991897302131683247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138638235989196402842244329 103978676991897302131683247)
  ·
    refine ⟨155968015487845953197524871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103978676991897302131683247 155968015487845953197524871)
    ·
      refine ⟨233952023231768929796287307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155968015487845953197524871 233952023231768929796287307)
      ·
        refine ⟨350928034847653394694430961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233952023231768929796287307 350928034847653394694430961)
        ·
          refine ⟨263196026135740046020823221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 350928034847653394694430961 263196026135740046020823221)
          ·
            refine ⟨24674627450225629314452177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 263196026135740046020823221 24674627450225629314452177)
            ·
              refine ⟨18505970587669221985839133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24674627450225629314452177 18505970587669221985839133)
              ·
                refine ⟨6939738970375958244689675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18505970587669221985839133 6939738970375958244689675)
                ·
                  refine ⟨10409608455563937367034513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6939738970375958244689675 10409608455563937367034513)
                  ·
                    refine ⟨7807206341672953025275885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10409608455563937367034513 7807206341672953025275885)
                    ·
                      refine ⟨2927702378127357384478457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7807206341672953025275885 2927702378127357384478457)
                      ·
                        rfl

theorem cell23_5701680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 3, 1, 2, 3].length) (baseStart_5701680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5701680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5701680 prefixEnd_5701680 := by exact prefixLift 5701680
  have htrace : WordTrace (prefixWord ++ tailWord_5701680) baseStart_5701680 baseEnd_5701680 := by
    simpa [prefixWord, tailWord_5701680, baseEnd_5701680] using wordTrace_append hprefix tailTrace_5701680
  have hstable : (prefixWord ++ tailWord_5701680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5701680).length < 2 ^ (prefixWord ++ tailWord_5701680).sum := by decide
  have hdescent : baseEnd_5701680 < baseStart_5701680 := by decide
  rcases family_descends (prefixWord ++ tailWord_5701680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5701714 : List Nat := [3, 2, 2, 1, 4, 2, 1, 2, 1, 2, 3]
def baseStart_5701714 : Nat := 118140960795 + 5701714 * 2 ^ 59
def prefixEnd_5701714 : Nat := 4983230072969 + 3 ^ 40 * 5701714 * 2
def baseEnd_5701714 : Nat := 2927719836469610251453301

theorem tailTrace_5701714 : CollatzResearch.WordTrace tailWord_5701714 prefixEnd_5701714 2927719836469610251453301 := by
  unfold tailWord_5701714
  simp only [CollatzResearch.WordTrace]
  refine ⟨51989648516417857017526049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138639062710447618713402797 51989648516417857017526049)
  ·
    refine ⟨38992236387313392763144537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51989648516417857017526049 38992236387313392763144537)
    ·
      refine ⟨29244177290485044572358403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38992236387313392763144537 29244177290485044572358403)
      ·
        refine ⟨43866265935727566858537605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29244177290485044572358403 43866265935727566858537605)
        ·
          refine ⟨8224924862948918785975801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43866265935727566858537605 8224924862948918785975801)
          ·
            refine ⟨6168693647211689089481851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8224924862948918785975801 6168693647211689089481851)
            ·
              refine ⟨9253040470817533634222777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6168693647211689089481851 9253040470817533634222777)
              ·
                refine ⟨6939780353113150225667083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9253040470817533634222777 6939780353113150225667083)
                ·
                  refine ⟨10409670529669725338500625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6939780353113150225667083 10409670529669725338500625)
                  ·
                    refine ⟨7807252897252294003875469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10409670529669725338500625 7807252897252294003875469)
                    ·
                      refine ⟨2927719836469610251453301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7807252897252294003875469 2927719836469610251453301)
                      ·
                        rfl

theorem cell23_5701714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 2, 1, 2, 3].length) (baseStart_5701714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5701714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5701714 prefixEnd_5701714 := by exact prefixLift 5701714
  have htrace : WordTrace (prefixWord ++ tailWord_5701714) baseStart_5701714 baseEnd_5701714 := by
    simpa [prefixWord, tailWord_5701714, baseEnd_5701714] using wordTrace_append hprefix tailTrace_5701714
  have hstable : (prefixWord ++ tailWord_5701714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5701714).length < 2 ^ (prefixWord ++ tailWord_5701714).sum := by decide
  have hdescent : baseEnd_5701714 < baseStart_5701714 := by decide
  rcases family_descends (prefixWord ++ tailWord_5701714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5701750 : List Nat := [5, 1, 1, 2, 1, 2, 1, 1, 2, 3, 4]
def baseStart_5701750 : Nat := 118140960795 + 5701750 * 2 ^ 59
def prefixEnd_5701750 : Nat := 4983230072969 + 3 ^ 40 * 5701750 * 2
def baseEnd_5701750 : Nat := 2927738321773172110603135

theorem tailTrace_5701750 : CollatzResearch.WordTrace tailWord_5701750 prefixEnd_5701750 2927738321773172110603135 := by
  unfold tailWord_5701750
  simp only [CollatzResearch.WordTrace]
  refine ⟨12997494193346312888650919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 138639938062360670812276469 12997494193346312888650919)
  ·
    refine ⟨19496241290019469332976379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12997494193346312888650919 19496241290019469332976379)
    ·
      refine ⟨29244361935029203999464569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19496241290019469332976379 29244361935029203999464569)
      ·
        refine ⟨21933271451271902999598427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29244361935029203999464569 21933271451271902999598427)
        ·
          refine ⟨32899907176907854499397641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21933271451271902999598427 32899907176907854499397641)
          ·
            refine ⟨24674930382680890874548231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32899907176907854499397641 24674930382680890874548231)
            ·
              refine ⟨37012395574021336311822347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24674930382680890874548231 37012395574021336311822347)
              ·
                refine ⟨55518593361032004467733521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37012395574021336311822347 55518593361032004467733521)
                ·
                  refine ⟨41638945020774003350800141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55518593361032004467733521 41638945020774003350800141)
                  ·
                    refine ⟨15614604382790251256550053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41638945020774003350800141 15614604382790251256550053)
                    ·
                      refine ⟨2927738321773172110603135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15614604382790251256550053 2927738321773172110603135)
                      ·
                        rfl

theorem cell23_5701750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_5701750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5701750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5701750 prefixEnd_5701750 := by exact prefixLift 5701750
  have htrace : WordTrace (prefixWord ++ tailWord_5701750) baseStart_5701750 baseEnd_5701750 := by
    simpa [prefixWord, tailWord_5701750, baseEnd_5701750] using wordTrace_append hprefix tailTrace_5701750
  have hstable : (prefixWord ++ tailWord_5701750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5701750).length < 2 ^ (prefixWord ++ tailWord_5701750).sum := by decide
  have hdescent : baseEnd_5701750 < baseStart_5701750 := by decide
  rcases family_descends (prefixWord ++ tailWord_5701750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5701763 : List Nat := [1, 1, 1, 3, 3, 3, 1, 1, 1, 4, 4]
def baseStart_5701763 : Nat := 118140960795 + 5701763 * 2 ^ 59
def prefixEnd_5701763 : Nat := 4983230072969 + 3 ^ 40 * 5701763 * 2
def baseEnd_5701763 : Nat := 2927744997021680559740575

theorem tailTrace_5701763 : CollatzResearch.WordTrace tailWord_5701763 prefixEnd_5701763 2927744997021680559740575 := by
  unfold tailWord_5701763
  simp only [CollatzResearch.WordTrace]
  refine ⟨207960381242493909438637943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138640254161662606292425295 207960381242493909438637943)
  ·
    refine ⟨311940571863740864157956915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207960381242493909438637943 311940571863740864157956915)
    ·
      refine ⟨467910857795611296236935373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 311940571863740864157956915 467910857795611296236935373)
      ·
        refine ⟨175466571673354236088850765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 467910857795611296236935373 175466571673354236088850765)
        ·
          refine ⟨65799964377507838533319037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 175466571673354236088850765 65799964377507838533319037)
          ·
            refine ⟨24674986641565439449994639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65799964377507838533319037 24674986641565439449994639)
            ·
              refine ⟨37012479962348159174991959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24674986641565439449994639 37012479962348159174991959)
              ·
                refine ⟨55518719943522238762487939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37012479962348159174991959 55518719943522238762487939)
                ·
                  refine ⟨83278079915283358143731909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55518719943522238762487939 83278079915283358143731909)
                  ·
                    refine ⟨15614639984115629651949733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 83278079915283358143731909 15614639984115629651949733)
                    ·
                      refine ⟨2927744997021680559740575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15614639984115629651949733 2927744997021680559740575)
                      ·
                        rfl

theorem cell23_5701763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 4, 4].length) (baseStart_5701763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5701763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5701763 prefixEnd_5701763 := by exact prefixLift 5701763
  have htrace : WordTrace (prefixWord ++ tailWord_5701763) baseStart_5701763 baseEnd_5701763 := by
    simpa [prefixWord, tailWord_5701763, baseEnd_5701763] using wordTrace_append hprefix tailTrace_5701763
  have hstable : (prefixWord ++ tailWord_5701763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5701763).length < 2 ^ (prefixWord ++ tailWord_5701763).sum := by decide
  have hdescent : baseEnd_5701763 < baseStart_5701763 := by decide
  rcases family_descends (prefixWord ++ tailWord_5701763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5701782 : List Nat := [5, 3, 2, 1, 1, 2, 2, 1, 1, 2, 3]
def baseStart_5701782 : Nat := 118140960795 + 5701782 * 2 ^ 59
def prefixEnd_5701782 : Nat := 4983230072969 + 3 ^ 40 * 5701782 * 2
def baseEnd_5701782 : Nat := 2927754753154115985402989

theorem tailTrace_5701782 : CollatzResearch.WordTrace tailWord_5701782 prefixEnd_5701782 2927754753154115985402989 := by
  unfold tailWord_5701782
  simp only [CollatzResearch.WordTrace]
  refine ⟨12997567139339067230223725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 138640716152950050455719733 12997567139339067230223725)
  ·
    refine ⟨4874087677252150211333897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12997567139339067230223725 4874087677252150211333897)
    ·
      refine ⟨3655565757939112658500423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4874087677252150211333897 3655565757939112658500423)
      ·
        refine ⟨5483348636908668987750635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3655565757939112658500423 5483348636908668987750635)
        ·
          refine ⟨8225022955363003481625953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5483348636908668987750635 8225022955363003481625953)
          ·
            refine ⟨6168767216522252611219465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8225022955363003481625953 6168767216522252611219465)
            ·
              refine ⟨4626575412391689458414599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6168767216522252611219465 4626575412391689458414599)
              ·
                refine ⟨6939863118587534187621899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4626575412391689458414599 6939863118587534187621899)
                ·
                  refine ⟨10409794677881301281432849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6939863118587534187621899 10409794677881301281432849)
                  ·
                    refine ⟨7807346008410975961074637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10409794677881301281432849 7807346008410975961074637)
                    ·
                      refine ⟨2927754753154115985402989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7807346008410975961074637 2927754753154115985402989)
                      ·
                        rfl

theorem cell23_5701782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_5701782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5701782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5701782 prefixEnd_5701782 := by exact prefixLift 5701782
  have htrace : WordTrace (prefixWord ++ tailWord_5701782) baseStart_5701782 baseEnd_5701782 := by
    simpa [prefixWord, tailWord_5701782, baseEnd_5701782] using wordTrace_append hprefix tailTrace_5701782
  have hstable : (prefixWord ++ tailWord_5701782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5701782).length < 2 ^ (prefixWord ++ tailWord_5701782).sum := by decide
  have hdescent : baseEnd_5701782 < baseStart_5701782 := by decide
  rcases family_descends (prefixWord ++ tailWord_5701782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5701850 : List Nat := [3, 1, 1, 2, 2, 1, 2, 2, 5, 4]
def baseStart_5701850 : Nat := 118140960795 + 5701850 * 2 ^ 59
def prefixEnd_5701850 : Nat := 4983230072969 + 3 ^ 40 * 5701850 * 2
def baseEnd_5701850 : Nat := 975929889946207239784225

theorem tailTrace_5701850 : CollatzResearch.WordTrace tailWord_5701850 prefixEnd_5701850 975929889946207239784225 := by
  unfold tailWord_5701850
  simp only [CollatzResearch.WordTrace]
  refine ⟨51990888598294680824263751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138642369595452482198036669 51990888598294680824263751)
  ·
    refine ⟨77986332897442021236395627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51990888598294680824263751 77986332897442021236395627)
    ·
      refine ⟨116979499346163031854593441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77986332897442021236395627 116979499346163031854593441)
      ·
        refine ⟨87734624509622273890945081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116979499346163031854593441 87734624509622273890945081)
        ·
          refine ⟨65800968382216705418208811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87734624509622273890945081 65800968382216705418208811)
          ·
            refine ⟨98701452573325058127313217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65800968382216705418208811 98701452573325058127313217)
            ·
              refine ⟨74026089429993793595484913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98701452573325058127313217 74026089429993793595484913)
              ·
                refine ⟨55519567072495345196613685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74026089429993793595484913 55519567072495345196613685)
                ·
                  refine ⟨5204959413046438612182533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55519567072495345196613685 5204959413046438612182533)
                  ·
                    refine ⟨975929889946207239784225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5204959413046438612182533 975929889946207239784225)
                    ·
                      rfl

theorem cell23_5701850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 2, 5, 4].length) (baseStart_5701850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5701850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5701850 prefixEnd_5701850 := by exact prefixLift 5701850
  have htrace : WordTrace (prefixWord ++ tailWord_5701850) baseStart_5701850 baseEnd_5701850 := by
    simpa [prefixWord, tailWord_5701850, baseEnd_5701850] using wordTrace_append hprefix tailTrace_5701850
  have hstable : (prefixWord ++ tailWord_5701850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5701850).length < 2 ^ (prefixWord ++ tailWord_5701850).sum := by decide
  have hdescent : baseEnd_5701850 < baseStart_5701850 := by decide
  rcases family_descends (prefixWord ++ tailWord_5701850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5701858 : List Nat := [3, 3, 4, 1, 2, 1, 1, 1, 7]
def baseStart_5701858 : Nat := 118140960795 + 5701858 * 2 ^ 59
def prefixEnd_5701858 : Nat := 4983230072969 + 3 ^ 40 * 5701858 * 2
def baseEnd_5701858 : Nat := 325310419742650854228071

theorem tailTrace_5701858 : CollatzResearch.WordTrace tailWord_5701858 prefixEnd_5701858 325310419742650854228071 := by
  unfold tailWord_5701858
  simp only [CollatzResearch.WordTrace]
  refine ⟨51990961544287435165836557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138642564118099827108897485 51990961544287435165836557)
  ·
    refine ⟨19496610579107788187188709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51990961544287435165836557 19496610579107788187188709)
    ·
      refine ⟨3655614483582710285097883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19496610579107788187188709 3655614483582710285097883)
      ·
        refine ⟨5483421725374065427646825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3655614483582710285097883 5483421725374065427646825)
        ·
          refine ⟨4112566294030549070735119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5483421725374065427646825 4112566294030549070735119)
          ·
            refine ⟨6168849441045823606102679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4112566294030549070735119 6168849441045823606102679)
            ·
              refine ⟨9253274161568735409154019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6168849441045823606102679 9253274161568735409154019)
              ·
                refine ⟨13879911242353103113731029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9253274161568735409154019 13879911242353103113731029)
                ·
                  refine ⟨325310419742650854228071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13879911242353103113731029 325310419742650854228071)
                  ·
                    rfl

theorem cell23_5701858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 1, 7].length) (baseStart_5701858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5701858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5701858 prefixEnd_5701858 := by exact prefixLift 5701858
  have htrace : WordTrace (prefixWord ++ tailWord_5701858) baseStart_5701858 baseEnd_5701858 := by
    simpa [prefixWord, tailWord_5701858, baseEnd_5701858] using wordTrace_append hprefix tailTrace_5701858
  have hstable : (prefixWord ++ tailWord_5701858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5701858).length < 2 ^ (prefixWord ++ tailWord_5701858).sum := by decide
  have hdescent : baseEnd_5701858 < baseStart_5701858 := by decide
  rcases family_descends (prefixWord ++ tailWord_5701858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5701903 : List Nat := [1, 1, 2, 1, 1, 1, 3, 2, 1, 3, 7]
def baseStart_5701903 : Nat := 118140960795 + 5701903 * 2 ^ 59
def prefixEnd_5701903 : Nat := 4983230072969 + 3 ^ 40 * 5701903 * 2
def baseEnd_5701903 : Nat := 2927816884313310011989931

theorem tailTrace_5701903 : CollatzResearch.WordTrace tailWord_5701903 prefixEnd_5701903 2927816884313310011989931 := by
  unfold tailWord_5701903
  simp only [CollatzResearch.WordTrace]
  refine ⟨207965487461986713348734363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138643658307991142232489575 207965487461986713348734363)
  ·
    refine ⟨311948231192980070023101545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207965487461986713348734363 311948231192980070023101545)
    ·
      refine ⟨233961173394735052517326159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 311948231192980070023101545 233961173394735052517326159)
      ·
        refine ⟨350941760092102578775989239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233961173394735052517326159 350941760092102578775989239)
        ·
          refine ⟨526412640138153868163983859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 350941760092102578775989239 526412640138153868163983859)
          ·
            refine ⟨789618960207230802245975789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 526412640138153868163983859 789618960207230802245975789)
            ·
              refine ⟨296107110077711550842240921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 789618960207230802245975789 296107110077711550842240921)
              ·
                refine ⟨222080332558283663131680691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 296107110077711550842240921 222080332558283663131680691)
                ·
                  refine ⟨333120498837425494697521037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 222080332558283663131680691 333120498837425494697521037)
                  ·
                    refine ⟨124920187064034560511570389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 333120498837425494697521037 124920187064034560511570389)
                    ·
                      refine ⟨2927816884313310011989931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 124920187064034560511570389 2927816884313310011989931)
                      ·
                        rfl

theorem cell23_5701903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 3, 7].length) (baseStart_5701903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5701903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5701903 prefixEnd_5701903 := by exact prefixLift 5701903
  have htrace : WordTrace (prefixWord ++ tailWord_5701903) baseStart_5701903 baseEnd_5701903 := by
    simpa [prefixWord, tailWord_5701903, baseEnd_5701903] using wordTrace_append hprefix tailTrace_5701903
  have hstable : (prefixWord ++ tailWord_5701903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5701903).length < 2 ^ (prefixWord ++ tailWord_5701903).sum := by decide
  have hdescent : baseEnd_5701903 < baseStart_5701903 := by decide
  rcases family_descends (prefixWord ++ tailWord_5701903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5701918 : List Nat := [4, 3, 2, 1, 1, 2, 1, 4, 1, 4]
def baseStart_5701918 : Nat := 118140960795 + 5701918 * 2 ^ 59
def prefixEnd_5701918 : Nat := 4983230072969 + 3 ^ 40 * 5701918 * 2
def baseEnd_5701918 : Nat := 975941528841042484434121

theorem tailTrace_5701918 : CollatzResearch.WordTrace tailWord_5701918 prefixEnd_5701918 975941528841042484434121 := by
  unfold tailWord_5701918
  simp only [CollatzResearch.WordTrace]
  refine ⟨25995754319616546363816301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138644023037954913940353605 25995754319616546363816301)
  ·
    refine ⟨9748407869856204886431113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25995754319616546363816301 9748407869856204886431113)
    ·
      refine ⟨7311305902392153664823335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9748407869856204886431113 7311305902392153664823335)
      ·
        refine ⟨10966958853588230497235003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7311305902392153664823335 10966958853588230497235003)
        ·
          refine ⟨16450438280382345745852505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10966958853588230497235003 16450438280382345745852505)
          ·
            refine ⟨12337828710286759309389379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16450438280382345745852505 12337828710286759309389379)
            ·
              refine ⟨18506743065430138964084069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12337828710286759309389379 18506743065430138964084069)
              ·
                refine ⟨3470014324768151055765763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18506743065430138964084069 3470014324768151055765763)
                ·
                  refine ⟨5205021487152226583648645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3470014324768151055765763 5205021487152226583648645)
                  ·
                    refine ⟨975941528841042484434121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5205021487152226583648645 975941528841042484434121)
                    ·
                      rfl

theorem cell23_5701918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_5701918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5701918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5701918 prefixEnd_5701918 := by exact prefixLift 5701918
  have htrace : WordTrace (prefixWord ++ tailWord_5701918) baseStart_5701918 baseEnd_5701918 := by
    simpa [prefixWord, tailWord_5701918, baseEnd_5701918] using wordTrace_append hprefix tailTrace_5701918
  have hstable : (prefixWord ++ tailWord_5701918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5701918).length < 2 ^ (prefixWord ++ tailWord_5701918).sum := by decide
  have hdescent : baseEnd_5701918 < baseStart_5701918 := by decide
  rcases family_descends (prefixWord ++ tailWord_5701918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5701964 : List Nat := [2, 2, 1, 3, 2, 1, 1, 2, 5, 2, 2]
def baseStart_5701964 : Nat := 118140960795 + 5701964 * 2 ^ 59
def prefixEnd_5701964 : Nat := 4983230072969 + 3 ^ 40 * 5701964 * 2
def baseEnd_5701964 : Nat := 2927848206633234273327151

theorem tailTrace_5701964 : CollatzResearch.WordTrace tailWord_5701964 prefixEnd_5701964 2927848206633234273327151 := by
  unfold tailWord_5701964
  simp only [CollatzResearch.WordTrace]
  refine ⟨103983856157382860383352473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138645141543177147177803297 103983856157382860383352473)
  ·
    refine ⟨77987892118037145287514355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103983856157382860383352473 77987892118037145287514355)
    ·
      refine ⟨116981838177055717931271533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77987892118037145287514355 116981838177055717931271533)
      ·
        refine ⟨43868189316395894224226825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116981838177055717931271533 43868189316395894224226825)
        ·
          refine ⟨32901141987296920668170119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43868189316395894224226825 32901141987296920668170119)
          ·
            refine ⟨49351712980945381002255179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32901141987296920668170119 49351712980945381002255179)
            ·
              refine ⟨74027569471418071503382769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49351712980945381002255179 74027569471418071503382769)
              ·
                refine ⟨55520677103563553627537077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74027569471418071503382769 55520677103563553627537077)
                ·
                  refine ⟨5205063478459083152581601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55520677103563553627537077 5205063478459083152581601)
                  ·
                    refine ⟨3903797608844312364436201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5205063478459083152581601 3903797608844312364436201)
                    ·
                      refine ⟨2927848206633234273327151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3903797608844312364436201 2927848206633234273327151)
                      ·
                        rfl

theorem cell23_5701964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 2, 5, 2, 2].length) (baseStart_5701964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5701964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5701964 prefixEnd_5701964 := by exact prefixLift 5701964
  have htrace : WordTrace (prefixWord ++ tailWord_5701964) baseStart_5701964 baseEnd_5701964 := by
    simpa [prefixWord, tailWord_5701964, baseEnd_5701964] using wordTrace_append hprefix tailTrace_5701964
  have hstable : (prefixWord ++ tailWord_5701964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5701964).length < 2 ^ (prefixWord ++ tailWord_5701964).sum := by decide
  have hdescent : baseEnd_5701964 < baseStart_5701964 := by decide
  rcases family_descends (prefixWord ++ tailWord_5701964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5701991 : List Nat := [1, 1, 5, 1, 3, 2, 3, 1, 2, 4]
def baseStart_5701991 : Nat := 118140960795 + 5701991 * 2 ^ 59
def prefixEnd_5701991 : Nat := 4983230072969 + 3 ^ 40 * 5701991 * 2
def baseEnd_5701991 : Nat := 975954023536968555896509

theorem tailTrace_5701991 : CollatzResearch.WordTrace tailWord_5701991 prefixEnd_5701991 975954023536968555896509 := by
  unfold tailWord_5701991
  simp only [CollatzResearch.WordTrace]
  refine ⟨207968697085667904377937827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138645798057111936251958551 207968697085667904377937827)
  ·
    refine ⟨311953045628501856566906741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207968697085667904377937827 311953045628501856566906741)
    ·
      refine ⟨29245598027672049053147507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 311953045628501856566906741 29245598027672049053147507)
      ·
        refine ⟨43868397041508073579721261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29245598027672049053147507 43868397041508073579721261)
        ·
          refine ⟨16450648890565527592395473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43868397041508073579721261 16450648890565527592395473)
          ·
            refine ⟨12337986667924145694296605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16450648890565527592395473 12337986667924145694296605)
            ·
              refine ⟨4626745000471554635361227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12337986667924145694296605 4626745000471554635361227)
              ·
                refine ⟨6940117500707331953041841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4626745000471554635361227 6940117500707331953041841)
                ·
                  refine ⟨5205088125530498964781381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6940117500707331953041841 5205088125530498964781381)
                  ·
                    refine ⟨975954023536968555896509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5205088125530498964781381 975954023536968555896509)
                    ·
                      rfl

theorem cell23_5701991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 3, 1, 2, 4].length) (baseStart_5701991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5701991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5701991 prefixEnd_5701991 := by exact prefixLift 5701991
  have htrace : WordTrace (prefixWord ++ tailWord_5701991) baseStart_5701991 baseEnd_5701991 := by
    simpa [prefixWord, tailWord_5701991, baseEnd_5701991] using wordTrace_append hprefix tailTrace_5701991
  have hstable : (prefixWord ++ tailWord_5701991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5701991).length < 2 ^ (prefixWord ++ tailWord_5701991).sum := by decide
  have hdescent : baseEnd_5701991 < baseStart_5701991 := by decide
  rcases family_descends (prefixWord ++ tailWord_5701991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5701994 : List Nat := [3, 1, 3, 3, 1, 1, 3, 1, 1, 2, 4]
def baseStart_5701994 : Nat := 118140960795 + 5701994 * 2 ^ 59
def prefixEnd_5701994 : Nat := 4983230072969 + 3 ^ 40 * 5701994 * 2
def baseEnd_5701994 : Nat := 2927863611052869155952013

theorem tailTrace_5701994 : CollatzResearch.WordTrace tailWord_5701994 prefixEnd_5701994 2927863611052869155952013 := by
  unfold tailWord_5701994
  simp only [CollatzResearch.WordTrace]
  refine ⟨51992201626164258972574259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138645871003104690593531357 51992201626164258972574259)
  ·
    refine ⟨77988302439246388458861389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51992201626164258972574259 77988302439246388458861389)
    ·
      refine ⟨29245613414717395672073021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77988302439246388458861389 29245613414717395672073021)
      ·
        refine ⟨10967105030519023377027383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29245613414717395672073021 10967105030519023377027383)
        ·
          refine ⟨16450657545778535065541075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10967105030519023377027383 16450657545778535065541075)
          ·
            refine ⟨24675986318667802598311613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16450657545778535065541075 24675986318667802598311613)
            ·
              refine ⟨9253494869500425974366855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24675986318667802598311613 9253494869500425974366855)
              ·
                refine ⟨13880242304250638961550283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9253494869500425974366855 13880242304250638961550283)
                ·
                  refine ⟨20820363456375958442325425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13880242304250638961550283 20820363456375958442325425)
                  ·
                    refine ⟨15615272592281968831744069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20820363456375958442325425 15615272592281968831744069)
                    ·
                      refine ⟨2927863611052869155952013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15615272592281968831744069 2927863611052869155952013)
                      ·
                        rfl

theorem cell23_5701994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_5701994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5701994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5701994 prefixEnd_5701994 := by exact prefixLift 5701994
  have htrace : WordTrace (prefixWord ++ tailWord_5701994) baseStart_5701994 baseEnd_5701994 := by
    simpa [prefixWord, tailWord_5701994, baseEnd_5701994] using wordTrace_append hprefix tailTrace_5701994
  have hstable : (prefixWord ++ tailWord_5701994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5701994).length < 2 ^ (prefixWord ++ tailWord_5701994).sum := by decide
  have hdescent : baseEnd_5701994 < baseStart_5701994 := by decide
  rcases family_descends (prefixWord ++ tailWord_5701994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5702038 : List Nat := [5, 3, 1, 2, 1, 1, 2, 8]
def baseStart_5702038 : Nat := 118140960795 + 5702038 * 2 ^ 59
def prefixEnd_5702038 : Nat := 4983230072969 + 3 ^ 40 * 5702038 * 2
def baseEnd_5702038 : Nat := 108440229785246925325993

theorem tailTrace_5702038 : CollatzResearch.WordTrace tailWord_5702038 prefixEnd_5702038 108440229785246925325993 := by
  unfold tailWord_5702038
  simp only [CollatzResearch.WordTrace]
  refine ⟨12998150707281101962806173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 138646940877665087603265845 12998150707281101962806173)
  ·
    refine ⟨4874306515230413236052315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12998150707281101962806173 4874306515230413236052315)
    ·
      refine ⟨7311459772845619854078473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4874306515230413236052315 7311459772845619854078473)
      ·
        refine ⟨5483594829634214890558855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7311459772845619854078473 5483594829634214890558855)
        ·
          refine ⟨8225392244451322335838283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5483594829634214890558855 8225392244451322335838283)
          ·
            refine ⟨12338088366676983503757425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8225392244451322335838283 12338088366676983503757425)
            ·
              refine ⟨9253566275007737627818069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12338088366676983503757425 9253566275007737627818069)
              ·
                refine ⟨108440229785246925325993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9253566275007737627818069 108440229785246925325993)
                ·
                  rfl

theorem cell23_5702038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 8].length) (baseStart_5702038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5702038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5702038 prefixEnd_5702038 := by exact prefixLift 5702038
  have htrace : WordTrace (prefixWord ++ tailWord_5702038) baseStart_5702038 baseEnd_5702038 := by
    simpa [prefixWord, tailWord_5702038, baseEnd_5702038] using wordTrace_append hprefix tailTrace_5702038
  have hstable : (prefixWord ++ tailWord_5702038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5702038).length < 2 ^ (prefixWord ++ tailWord_5702038).sum := by decide
  have hdescent : baseEnd_5702038 < baseStart_5702038 := by decide
  rcases family_descends (prefixWord ++ tailWord_5702038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5702048 : List Nat := [2, 1, 1, 4, 1, 5, 2, 1, 2, 1, 3]
def baseStart_5702048 : Nat := 118140960795 + 5702048 * 2 ^ 59
def prefixEnd_5702048 : Nat := 4983230072969 + 3 ^ 40 * 5702048 * 2
def baseEnd_5702048 : Nat := 2927891339008211944676765

theorem tailTrace_5702048 : CollatzResearch.WordTrace tailWord_5702048 prefixEnd_5702048 2927891339008211944676765 := by
  unfold tailWord_5702048
  simp only [CollatzResearch.WordTrace]
  refine ⟨103985388023230701556381399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138647184030974268741841865 103985388023230701556381399)
  ·
    refine ⟨155978082034846052334572099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103985388023230701556381399 155978082034846052334572099)
    ·
      refine ⟨233967123052269078501858149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155978082034846052334572099 233967123052269078501858149)
      ·
        refine ⟨43868835572300452219098403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 233967123052269078501858149 43868835572300452219098403)
        ·
          refine ⟨65803253358450678328647605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43868835572300452219098403 65803253358450678328647605)
          ·
            refine ⟨6169055002354751093310713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 65803253358450678328647605 6169055002354751093310713)
            ·
              refine ⟨4626791251766063319983035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6169055002354751093310713 4626791251766063319983035)
              ·
                refine ⟨6940186877649094979974553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4626791251766063319983035 6940186877649094979974553)
                ·
                  refine ⟨5205140158236821234980915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6940186877649094979974553 5205140158236821234980915)
                  ·
                    refine ⟨7807710237355231852471373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5205140158236821234980915 7807710237355231852471373)
                    ·
                      refine ⟨2927891339008211944676765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7807710237355231852471373 2927891339008211944676765)
                      ·
                        rfl

theorem cell23_5702048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 2, 1, 2, 1, 3].length) (baseStart_5702048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5702048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5702048 prefixEnd_5702048 := by exact prefixLift 5702048
  have htrace : WordTrace (prefixWord ++ tailWord_5702048) baseStart_5702048 baseEnd_5702048 := by
    simpa [prefixWord, tailWord_5702048, baseEnd_5702048] using wordTrace_append hprefix tailTrace_5702048
  have hstable : (prefixWord ++ tailWord_5702048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5702048).length < 2 ^ (prefixWord ++ tailWord_5702048).sum := by decide
  have hdescent : baseEnd_5702048 < baseStart_5702048 := by decide
  rcases family_descends (prefixWord ++ tailWord_5702048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5702060 : List Nat := [2, 2, 1, 1, 1, 1, 3, 3, 9]
def baseStart_5702060 : Nat := 118140960795 + 5702060 * 2 ^ 59
def prefixEnd_5702060 : Nat := 4983230072969 + 3 ^ 40 * 5702060 * 2
def baseEnd_5702060 : Nat := 325321944530673988636301

theorem tailTrace_5702060 : CollatzResearch.WordTrace tailWord_5702060 prefixEnd_5702060 325321944530673988636301 := by
  unfold tailWord_5702060
  simp only [CollatzResearch.WordTrace]
  refine ⟨103985606861208964581099817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138647475814945286108133089 103985606861208964581099817)
  ·
    refine ⟨77989205145906723435824863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103985606861208964581099817 77989205145906723435824863)
    ·
      refine ⟨116983807718860085153737295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77989205145906723435824863 116983807718860085153737295)
      ·
        refine ⟨175475711578290127730605943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116983807718860085153737295 175475711578290127730605943)
        ·
          refine ⟨263213567367435191595908915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175475711578290127730605943 263213567367435191595908915)
          ·
            refine ⟨394820351051152787393863373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 263213567367435191595908915 394820351051152787393863373)
            ·
              refine ⟨148057631644182295272698765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 394820351051152787393863373 148057631644182295272698765)
              ·
                refine ⟨55521611866568360727262037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 148057631644182295272698765 55521611866568360727262037)
                ·
                  refine ⟨325321944530673988636301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 55521611866568360727262037 325321944530673988636301)
                  ·
                    rfl

theorem cell23_5702060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 9].length) (baseStart_5702060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5702060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5702060 prefixEnd_5702060 := by exact prefixLift 5702060
  have htrace : WordTrace (prefixWord ++ tailWord_5702060) baseStart_5702060 baseEnd_5702060 := by
    simpa [prefixWord, tailWord_5702060, baseEnd_5702060] using wordTrace_append hprefix tailTrace_5702060
  have hstable : (prefixWord ++ tailWord_5702060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5702060).length < 2 ^ (prefixWord ++ tailWord_5702060).sum := by decide
  have hdescent : baseEnd_5702060 < baseStart_5702060 := by decide
  rcases family_descends (prefixWord ++ tailWord_5702060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5702088 : List Nat := [2, 1, 3, 1, 3, 3, 2, 2, 2, 2, 2]
def baseStart_5702088 : Nat := 118140960795 + 5702088 * 2 ^ 59
def prefixEnd_5702088 : Nat := 4983230072969 + 3 ^ 40 * 5702088 * 2
def baseEnd_5702088 : Nat := 2927911878234391788176581

theorem tailTrace_5702088 : CollatzResearch.WordTrace tailWord_5702088 prefixEnd_5702088 2927911878234391788176581 := by
  unfold tailWord_5702088
  simp only [CollatzResearch.WordTrace]
  refine ⟨103986117483158244972109459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138648156644210993296145945 103986117483158244972109459)
  ·
    refine ⟨155979176224737367458164189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103986117483158244972109459 155979176224737367458164189)
    ·
      refine ⟨58492191084276512796811571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155979176224737367458164189 58492191084276512796811571)
      ·
        refine ⟨87738286626414769195217357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58492191084276512796811571 87738286626414769195217357)
        ·
          refine ⟨32901857484905538448206509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87738286626414769195217357 32901857484905538448206509)
          ·
            refine ⟨12338196556839576918077441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32901857484905538448206509 12338196556839576918077441)
            ·
              refine ⟨9253647417629682688558081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12338196556839576918077441 9253647417629682688558081)
              ·
                refine ⟨6940235563222262016418561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9253647417629682688558081 6940235563222262016418561)
                ·
                  refine ⟨5205176672416696512313921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6940235563222262016418561 5205176672416696512313921)
                  ·
                    refine ⟨3903882504312522384235441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5205176672416696512313921 3903882504312522384235441)
                    ·
                      refine ⟨2927911878234391788176581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3903882504312522384235441 2927911878234391788176581)
                      ·
                        rfl

theorem cell23_5702088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 2, 2, 2, 2].length) (baseStart_5702088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5702088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5702088 prefixEnd_5702088 := by exact prefixLift 5702088
  have htrace : WordTrace (prefixWord ++ tailWord_5702088) baseStart_5702088 baseEnd_5702088 := by
    simpa [prefixWord, tailWord_5702088, baseEnd_5702088] using wordTrace_append hprefix tailTrace_5702088
  have hstable : (prefixWord ++ tailWord_5702088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5702088).length < 2 ^ (prefixWord ++ tailWord_5702088).sum := by decide
  have hdescent : baseEnd_5702088 < baseStart_5702088 := by decide
  rcases family_descends (prefixWord ++ tailWord_5702088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5702184 : List Nat := [2, 1, 5, 2, 1, 1, 1, 2, 8]
def baseStart_5702184 : Nat := 118140960795 + 5702184 * 2 ^ 59
def prefixEnd_5702184 : Nat := 4983230072969 + 3 ^ 40 * 5702184 * 2
def baseEnd_5702184 : Nat := 325329019153024823619571

theorem tailTrace_5702184 : CollatzResearch.WordTrace tailWord_5702184 prefixEnd_5702184 325329019153024823619571 := by
  unfold tailWord_5702184
  simp only [CollatzResearch.WordTrace]
  refine ⟨103987868186984349169856803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138650490915979132226475737 103987868186984349169856803)
  ·
    refine ⟨155981802280476523754785205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103987868186984349169856803 155981802280476523754785205)
    ·
      refine ⟨14623293963794674102011113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 155981802280476523754785205 14623293963794674102011113)
      ·
        refine ⟨10967470472846005576508335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14623293963794674102011113 10967470472846005576508335)
        ·
          refine ⟨16451205709269008364762503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10967470472846005576508335 16451205709269008364762503)
          ·
            refine ⟨24676808563903512547143755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16451205709269008364762503 24676808563903512547143755)
            ·
              refine ⟨37015212845855268820715633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24676808563903512547143755 37015212845855268820715633)
              ·
                refine ⟨27761409634391451615536725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37015212845855268820715633 27761409634391451615536725)
                ·
                  refine ⟨325329019153024823619571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27761409634391451615536725 325329019153024823619571)
                  ·
                    rfl

theorem cell23_5702184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 2, 8].length) (baseStart_5702184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5702184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5702184 prefixEnd_5702184 := by exact prefixLift 5702184
  have htrace : WordTrace (prefixWord ++ tailWord_5702184) baseStart_5702184 baseEnd_5702184 := by
    simpa [prefixWord, tailWord_5702184, baseEnd_5702184] using wordTrace_append hprefix tailTrace_5702184
  have hstable : (prefixWord ++ tailWord_5702184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5702184).length < 2 ^ (prefixWord ++ tailWord_5702184).sum := by decide
  have hdescent : baseEnd_5702184 < baseStart_5702184 := by decide
  rcases family_descends (prefixWord ++ tailWord_5702184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5702198 : List Nat := [5, 1, 2, 1, 2, 2, 1, 2, 2, 2, 3]
def baseStart_5702198 : Nat := 118140960795 + 5702198 * 2 ^ 59
def prefixEnd_5702198 : Nat := 4983230072969 + 3 ^ 40 * 5702198 * 2
def baseEnd_5702198 : Nat := 2927968361106386357801075

theorem tailTrace_5702198 : CollatzResearch.WordTrace tailWord_5702198 prefixEnd_5702198 2927968361106386357801075 := by
  unfold tailWord_5702198
  simp only [CollatzResearch.WordTrace]
  refine ⟨12998515437244873670670203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 138650831330611985820482165 12998515437244873670670203)
  ·
    refine ⟨19497773155867310506005305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12998515437244873670670203 19497773155867310506005305)
    ·
      refine ⟨14623329866900482879503979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19497773155867310506005305 14623329866900482879503979)
      ·
        refine ⟨21934994800350724319255969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14623329866900482879503979 21934994800350724319255969)
        ·
          refine ⟨16451246100263043239441977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21934994800350724319255969 16451246100263043239441977)
          ·
            refine ⟨12338434575197282429581483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16451246100263043239441977 12338434575197282429581483)
            ·
              refine ⟨18507651862795923644372225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12338434575197282429581483 18507651862795923644372225)
              ·
                refine ⟨13880738897096942733279169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18507651862795923644372225 13880738897096942733279169)
                ·
                  refine ⟨10410554172822707049959377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13880738897096942733279169 10410554172822707049959377)
                  ·
                    refine ⟨7807915629617030287469533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10410554172822707049959377 7807915629617030287469533)
                    ·
                      refine ⟨2927968361106386357801075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7807915629617030287469533 2927968361106386357801075)
                      ·
                        rfl

theorem cell23_5702198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 2, 2, 2, 3].length) (baseStart_5702198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5702198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5702198 prefixEnd_5702198 := by exact prefixLift 5702198
  have htrace : WordTrace (prefixWord ++ tailWord_5702198) baseStart_5702198 baseEnd_5702198 := by
    simpa [prefixWord, tailWord_5702198, baseEnd_5702198] using wordTrace_append hprefix tailTrace_5702198
  have hstable : (prefixWord ++ tailWord_5702198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5702198).length < 2 ^ (prefixWord ++ tailWord_5702198).sum := by decide
  have hdescent : baseEnd_5702198 < baseStart_5702198 := by decide
  rcases family_descends (prefixWord ++ tailWord_5702198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5702205 : List Nat := [1, 4, 1, 3, 2, 2, 3, 2, 1, 4]
def baseStart_5702205 : Nat := 118140960795 + 5702205 * 2 ^ 59
def prefixEnd_5702205 : Nat := 4983230072969 + 3 ^ 40 * 5702205 * 2
def baseEnd_5702205 : Nat := 975990651823655943471181

theorem tailTrace_5702205 : CollatzResearch.WordTrace tailWord_5702205 prefixEnd_5702205 975990651823655943471181 := by
  unfold tailWord_5702205
  simp only [CollatzResearch.WordTrace]
  refine ⟨207976502306892618926228069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138651001537928412617485379 207976502306892618926228069)
  ·
    refine ⟨38995594182542366048667763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 207976502306892618926228069 38995594182542366048667763)
    ·
      refine ⟨58493391273813549073001645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38995594182542366048667763 58493391273813549073001645)
      ·
        refine ⟨21935021727680080902375617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58493391273813549073001645 21935021727680080902375617)
        ·
          refine ⟨16451266295760060676781713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21935021727680080902375617 16451266295760060676781713)
          ·
            refine ⟨12338449721820045507586285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16451266295760060676781713 12338449721820045507586285)
            ·
              refine ⟨4626918645682517065344857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12338449721820045507586285 4626918645682517065344857)
              ·
                refine ⟨3470188984261887799008643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4626918645682517065344857 3470188984261887799008643)
                ·
                  refine ⟨5205283476392831698512965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3470188984261887799008643 5205283476392831698512965)
                  ·
                    refine ⟨975990651823655943471181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5205283476392831698512965 975990651823655943471181)
                    ·
                      rfl

theorem cell23_5702205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 3, 2, 1, 4].length) (baseStart_5702205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5702205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5702205 prefixEnd_5702205 := by exact prefixLift 5702205
  have htrace : WordTrace (prefixWord ++ tailWord_5702205) baseStart_5702205 baseEnd_5702205 := by
    simpa [prefixWord, tailWord_5702205, baseEnd_5702205] using wordTrace_append hprefix tailTrace_5702205
  have hstable : (prefixWord ++ tailWord_5702205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5702205).length < 2 ^ (prefixWord ++ tailWord_5702205).sum := by decide
  have hdescent : baseEnd_5702205 < baseStart_5702205 := by decide
  rcases family_descends (prefixWord ++ tailWord_5702205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5702217 : List Nat := [1, 2, 1, 1, 2, 2, 1, 1, 1, 7, 4]
def baseStart_5702217 : Nat := 118140960795 + 5702217 * 2 ^ 59
def prefixEnd_5702217 : Nat := 4983230072969 + 3 ^ 40 * 5702217 * 2
def baseEnd_5702217 : Nat := 2927978117238821783463487

theorem tailTrace_5702217 : CollatzResearch.WordTrace tailWord_5702217 prefixEnd_5702217 2927978117238821783463487 := by
  unfold tailWord_5702217
  simp only [CollatzResearch.WordTrace]
  refine ⟨207976939982849144975664905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138651293321899429983776603 207976939982849144975664905)
  ·
    refine ⟨155982704987136858731748679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207976939982849144975664905 155982704987136858731748679)
    ·
      refine ⟨233974057480705288097623019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155982704987136858731748679 233974057480705288097623019)
      ·
        refine ⟨350961086221057932146434529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233974057480705288097623019 350961086221057932146434529)
        ·
          refine ⟨263220814665793449109825897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 350961086221057932146434529 263220814665793449109825897)
          ·
            refine ⟨197415610999345086832369423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 263220814665793449109825897 197415610999345086832369423)
            ·
              refine ⟨296123416499017630248554135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197415610999345086832369423 296123416499017630248554135)
              ·
                refine ⟨444185124748526445372831203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 296123416499017630248554135 444185124748526445372831203)
                ·
                  refine ⟨666277687122789668059246805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 444185124748526445372831203 666277687122789668059246805)
                  ·
                    refine ⟨15615883291940382845138597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 666277687122789668059246805 15615883291940382845138597)
                    ·
                      refine ⟨2927978117238821783463487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15615883291940382845138597 2927978117238821783463487)
                      ·
                        rfl

theorem cell23_5702217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 7, 4].length) (baseStart_5702217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5702217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5702217 prefixEnd_5702217 := by exact prefixLift 5702217
  have htrace : WordTrace (prefixWord ++ tailWord_5702217) baseStart_5702217 baseEnd_5702217 := by
    simpa [prefixWord, tailWord_5702217, baseEnd_5702217] using wordTrace_append hprefix tailTrace_5702217
  have hstable : (prefixWord ++ tailWord_5702217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5702217).length < 2 ^ (prefixWord ++ tailWord_5702217).sum := by decide
  have hdescent : baseEnd_5702217 < baseStart_5702217 := by decide
  rcases family_descends (prefixWord ++ tailWord_5702217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5702244 : List Nat := [2, 3, 1, 1, 2, 2, 3, 2, 1, 6]
def baseStart_5702244 : Nat := 118140960795 + 5702244 * 2 ^ 59
def prefixEnd_5702244 : Nat := 4983230072969 + 3 ^ 40 * 5702244 * 2
def baseEnd_5702244 : Nat := 975997327072164392608621

theorem tailTrace_5702244 : CollatzResearch.WordTrace tailWord_5702244 prefixEnd_5702244 975997327072164392608621 := by
  unfold tailWord_5702244
  simp only [CollatzResearch.WordTrace]
  refine ⟨103988962376875664293448893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138651949835834219057931857 103988962376875664293448893)
  ·
    refine ⟨38995860891328374110043335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103988962376875664293448893 38995860891328374110043335)
    ·
      refine ⟨58493791336992561165065003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38995860891328374110043335 58493791336992561165065003)
      ·
        refine ⟨87740687005488841747597505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58493791336992561165065003 87740687005488841747597505)
        ·
          refine ⟨65805515254116631310698129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87740687005488841747597505 65805515254116631310698129)
          ·
            refine ⟨49354136440587473483023597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65805515254116631310698129 49354136440587473483023597)
            ·
              refine ⟨18507801165220302556133849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49354136440587473483023597 18507801165220302556133849)
              ·
                refine ⟨13880850873915226917100387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18507801165220302556133849 13880850873915226917100387)
                ·
                  refine ⟨20821276310872840375650581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13880850873915226917100387 20821276310872840375650581)
                  ·
                    refine ⟨975997327072164392608621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20821276310872840375650581 975997327072164392608621)
                    ·
                      rfl

theorem cell23_5702244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 2, 1, 6].length) (baseStart_5702244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5702244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5702244 prefixEnd_5702244 := by exact prefixLift 5702244
  have htrace : WordTrace (prefixWord ++ tailWord_5702244) baseStart_5702244 baseEnd_5702244 := by
    simpa [prefixWord, tailWord_5702244, baseEnd_5702244] using wordTrace_append hprefix tailTrace_5702244
  have hstable : (prefixWord ++ tailWord_5702244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5702244).length < 2 ^ (prefixWord ++ tailWord_5702244).sum := by decide
  have hdescent : baseEnd_5702244 < baseStart_5702244 := by decide
  rcases family_descends (prefixWord ++ tailWord_5702244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5702251 : List Nat := [1, 1, 1, 1, 2, 2, 1, 3, 7, 2, 2]
def baseStart_5702251 : Nat := 118140960795 + 5702251 * 2 ^ 59
def prefixEnd_5702251 : Nat := 4983230072969 + 3 ^ 40 * 5702251 * 2
def baseEnd_5702251 : Nat := 2927995575581074650438331

theorem tailTrace_5702251 : CollatzResearch.WordTrace tailWord_5702251 prefixEnd_5702251 2927995575581074650438331 := by
  unfold tailWord_5702251
  simp only [CollatzResearch.WordTrace]
  refine ⟨207978180064725968782402607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138652120043150645854935071 207978180064725968782402607)
  ·
    refine ⟨311967270097088953173603911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207978180064725968782402607 311967270097088953173603911)
    ·
      refine ⟨467950905145633429760405867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 311967270097088953173603911 467950905145633429760405867)
      ·
        refine ⟨701926357718450144640608801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 467950905145633429760405867 701926357718450144640608801)
        ·
          refine ⟨526444768288837608480456601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 701926357718450144640608801 526444768288837608480456601)
          ·
            refine ⟨394833576216628206360342451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 526444768288837608480456601 394833576216628206360342451)
            ·
              refine ⟨592250364324942309540513677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 394833576216628206360342451 592250364324942309540513677)
              ·
                refine ⟨222093886621853366077692629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 592250364324942309540513677 222093886621853366077692629)
                ·
                  refine ⟨5205325467699688267445921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 222093886621853366077692629 5205325467699688267445921)
                  ·
                    refine ⟨3903994100774766200584441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5205325467699688267445921 3903994100774766200584441)
                    ·
                      refine ⟨2927995575581074650438331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3903994100774766200584441 2927995575581074650438331)
                      ·
                        rfl

theorem cell23_5702251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 7, 2, 2].length) (baseStart_5702251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5702251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5702251 prefixEnd_5702251 := by exact prefixLift 5702251
  have htrace : WordTrace (prefixWord ++ tailWord_5702251) baseStart_5702251 baseEnd_5702251 := by
    simpa [prefixWord, tailWord_5702251, baseEnd_5702251] using wordTrace_append hprefix tailTrace_5702251
  have hstable : (prefixWord ++ tailWord_5702251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5702251).length < 2 ^ (prefixWord ++ tailWord_5702251).sum := by decide
  have hdescent : baseEnd_5702251 < baseStart_5702251 := by decide
  rcases family_descends (prefixWord ++ tailWord_5702251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5702262 : List Nat := [5, 1, 1, 2, 3, 1, 1, 4, 1, 1, 3]
def baseStart_5702262 : Nat := 118140960795 + 5702262 * 2 ^ 59
def prefixEnd_5702262 : Nat := 4983230072969 + 3 ^ 40 * 5702262 * 2
def baseEnd_5702262 : Nat := 2928001223868274107400781

theorem tailTrace_5702262 : CollatzResearch.WordTrace tailWord_5702262 prefixEnd_5702262 2928001223868274107400781 := by
  unfold tailWord_5702262
  simp only [CollatzResearch.WordTrace]
  refine ⟨12998661329230382353815815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 138652387511790745107368693 12998661329230382353815815)
  ·
    refine ⟨19497991993845573530723723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12998661329230382353815815 19497991993845573530723723)
    ·
      refine ⟨29246987990768360296085585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19497991993845573530723723 29246987990768360296085585)
      ·
        refine ⟨21935240993076270222064189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29246987990768360296085585 21935240993076270222064189)
        ·
          refine ⟨8225715372403601333274071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21935240993076270222064189 8225715372403601333274071)
          ·
            refine ⟨12338573058605401999911107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8225715372403601333274071 12338573058605401999911107)
            ·
              refine ⟨18507859587908102999866661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12338573058605401999911107 18507859587908102999866661)
              ·
                refine ⟨3470223672732769312474999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18507859587908102999866661 3470223672732769312474999)
                ·
                  refine ⟨5205335509099153968712499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3470223672732769312474999 5205335509099153968712499)
                  ·
                    refine ⟨7808003263648730953068749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5205335509099153968712499 7808003263648730953068749)
                    ·
                      refine ⟨2928001223868274107400781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7808003263648730953068749 2928001223868274107400781)
                      ·
                        rfl

theorem cell23_5702262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 4, 1, 1, 3].length) (baseStart_5702262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5702262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5702262 prefixEnd_5702262 := by exact prefixLift 5702262
  have htrace : WordTrace (prefixWord ++ tailWord_5702262) baseStart_5702262 baseEnd_5702262 := by
    simpa [prefixWord, tailWord_5702262, baseEnd_5702262] using wordTrace_append hprefix tailTrace_5702262
  have hstable : (prefixWord ++ tailWord_5702262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5702262).length < 2 ^ (prefixWord ++ tailWord_5702262).sum := by decide
  have hdescent : baseEnd_5702262 < baseStart_5702262 := by decide
  rcases family_descends (prefixWord ++ tailWord_5702262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5702267 : List Nat := [1, 1, 1, 1, 1, 4, 2, 1, 2, 2, 7]
def baseStart_5702267 : Nat := 118140960795 + 5702267 * 2 ^ 59
def prefixEnd_5702267 : Nat := 4983230072969 + 3 ^ 40 * 5702267 * 2
def baseEnd_5702267 : Nat := 2928003791271546587838257

theorem tailTrace_5702267 : CollatzResearch.WordTrace tailWord_5702267 prefixEnd_5702267 2928003791271546587838257 := by
  unfold tailWord_5702267
  simp only [CollatzResearch.WordTrace]
  refine ⟨207978763632668003514985055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138652509088445335676656703 207978763632668003514985055)
  ·
    refine ⟨311968145449002005272477583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207978763632668003514985055 311968145449002005272477583)
    ·
      refine ⟨467952218173503007908716375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 311968145449002005272477583 467952218173503007908716375)
      ·
        refine ⟨701928327260254511863074563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 467952218173503007908716375 701928327260254511863074563)
        ·
          refine ⟨1052892490890381767794611845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 701928327260254511863074563 1052892490890381767794611845)
          ·
            refine ⟨197417342041946581461489721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1052892490890381767794611845 197417342041946581461489721)
            ·
              refine ⟨148063006531459936096117291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 197417342041946581461489721 148063006531459936096117291)
              ·
                refine ⟨222094509797189904144175937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 148063006531459936096117291 222094509797189904144175937)
                ·
                  refine ⟨166570882347892428108131953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 222094509797189904144175937 166570882347892428108131953)
                  ·
                    refine ⟨124928161760919321081098965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 166570882347892428108131953 124928161760919321081098965)
                    ·
                      refine ⟨2928003791271546587838257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 124928161760919321081098965 2928003791271546587838257)
                      ·
                        rfl

theorem cell23_5702267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 2, 7].length) (baseStart_5702267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5702267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5702267 prefixEnd_5702267 := by exact prefixLift 5702267
  have htrace : WordTrace (prefixWord ++ tailWord_5702267) baseStart_5702267 baseEnd_5702267 := by
    simpa [prefixWord, tailWord_5702267, baseEnd_5702267] using wordTrace_append hprefix tailTrace_5702267
  have hstable : (prefixWord ++ tailWord_5702267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5702267).length < 2 ^ (prefixWord ++ tailWord_5702267).sum := by decide
  have hdescent : baseEnd_5702267 < baseStart_5702267 := by decide
  rcases family_descends (prefixWord ++ tailWord_5702267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5702301 : List Nat := [1, 4, 2, 1, 1, 1, 4, 2, 1, 3, 3]
def baseStart_5702301 : Nat := 118140960795 + 5702301 * 2 ^ 59
def prefixEnd_5702301 : Nat := 4983230072969 + 3 ^ 40 * 5702301 * 2
def baseEnd_5702301 : Nat := 2928021249613799454813101

theorem tailTrace_5702301 : CollatzResearch.WordTrace tailWord_5702301 prefixEnd_5702301 2928021249613799454813101 := by
  unfold tailWord_5702301
  simp only [CollatzResearch.WordTrace]
  refine ⟨207980003714544827321722757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138653335809696551547815171 207980003714544827321722757)
  ·
    refine ⟨38996250696477155122823017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 207980003714544827321722757 38996250696477155122823017)
    ·
      refine ⟨29247188022357866342117263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38996250696477155122823017 29247188022357866342117263)
      ·
        refine ⟨43870782033536799513175895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29247188022357866342117263 43870782033536799513175895)
        ·
          refine ⟨65806173050305199269763843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43870782033536799513175895 65806173050305199269763843)
          ·
            refine ⟨98709259575457798904645765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65806173050305199269763843 98709259575457798904645765)
            ·
              refine ⟨18507986170398337294621081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 98709259575457798904645765 18507986170398337294621081)
              ·
                refine ⟨13880989627798752970965811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18507986170398337294621081 13880989627798752970965811)
                ·
                  refine ⟨20821484441698129456448717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13880989627798752970965811 20821484441698129456448717)
                  ·
                    refine ⟨7808056665636798546168269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20821484441698129456448717 7808056665636798546168269)
                    ·
                      refine ⟨2928021249613799454813101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7808056665636798546168269 2928021249613799454813101)
                      ·
                        rfl

theorem cell23_5702301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 2, 1, 3, 3].length) (baseStart_5702301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5702301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5702301 prefixEnd_5702301 := by exact prefixLift 5702301
  have htrace : WordTrace (prefixWord ++ tailWord_5702301) baseStart_5702301 baseEnd_5702301 := by
    simpa [prefixWord, tailWord_5702301, baseEnd_5702301] using wordTrace_append hprefix tailTrace_5702301
  have hstable : (prefixWord ++ tailWord_5702301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5702301).length < 2 ^ (prefixWord ++ tailWord_5702301).sum := by decide
  have hdescent : baseEnd_5702301 < baseStart_5702301 := by decide
  rcases family_descends (prefixWord ++ tailWord_5702301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5702335 : List Nat := [1, 1, 2, 2, 2, 5, 3, 1, 2, 1, 3]
def baseStart_5702335 : Nat := 118140960795 + 5702335 * 2 ^ 59
def prefixEnd_5702335 : Nat := 4983230072969 + 3 ^ 40 * 5702335 * 2
def baseEnd_5702335 : Nat := 2928038707956052321787945

theorem tailTrace_5702335 : CollatzResearch.WordTrace tailWord_5702335 prefixEnd_5702335 2928038707956052321787945 := by
  unfold tailWord_5702335
  simp only [CollatzResearch.WordTrace]
  refine ⟨207981243796421651128460459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138654162530947767418973639 207981243796421651128460459)
  ·
    refine ⟨311971865694632476692690689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207981243796421651128460459 311971865694632476692690689)
    ·
      refine ⟨233978899270974357519518017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 311971865694632476692690689 233978899270974357519518017)
      ·
        refine ⟨175484174453230768139638513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 233978899270974357519518017 175484174453230768139638513)
        ·
          refine ⟨131613130839923076104728885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175484174453230768139638513 131613130839923076104728885)
          ·
            refine ⟨12338731016242788384818333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 131613130839923076104728885 12338731016242788384818333)
            ·
              refine ⟨4627024131091045644306875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12338731016242788384818333 4627024131091045644306875)
              ·
                refine ⟨6940536196636568466460313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4627024131091045644306875 6940536196636568466460313)
                ·
                  refine ⟨5205402147477426349845235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6940536196636568466460313 5205402147477426349845235)
                  ·
                    refine ⟨7808103221216139524767853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5205402147477426349845235 7808103221216139524767853)
                    ·
                      refine ⟨2928038707956052321787945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7808103221216139524767853 2928038707956052321787945)
                      ·
                        rfl

theorem cell23_5702335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 3, 1, 2, 1, 3].length) (baseStart_5702335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5702335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5702335 prefixEnd_5702335 := by exact prefixLift 5702335
  have htrace : WordTrace (prefixWord ++ tailWord_5702335) baseStart_5702335 baseEnd_5702335 := by
    simpa [prefixWord, tailWord_5702335, baseEnd_5702335] using wordTrace_append hprefix tailTrace_5702335
  have hstable : (prefixWord ++ tailWord_5702335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5702335).length < 2 ^ (prefixWord ++ tailWord_5702335).sum := by decide
  have hdescent : baseEnd_5702335 < baseStart_5702335 := by decide
  rcases family_descends (prefixWord ++ tailWord_5702335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5702342 : List Nat := [6, 1, 2, 1, 2, 2, 2, 7]
def baseStart_5702342 : Nat := 118140960795 + 5702342 * 2 ^ 59
def prefixEnd_5702342 : Nat := 4983230072969 + 3 ^ 40 * 5702342 * 2
def baseEnd_5702342 : Nat := 108446011197060510903719

theorem tailTrace_5702342 : CollatzResearch.WordTrace tailWord_5702342 prefixEnd_5702342 108446011197060510903719 := by
  unfold tailWord_5702342
  simp only [CollatzResearch.WordTrace]
  refine ⟨6499421847106134103873915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 138654332738264194215976853 6499421847106134103873915)
  ·
    refine ⟨9749132770659201155810873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6499421847106134103873915 9749132770659201155810873)
    ·
      refine ⟨7311849577994400866858155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9749132770659201155810873 7311849577994400866858155)
      ·
        refine ⟨10967774366991601300287233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7311849577994400866858155 10967774366991601300287233)
        ·
          refine ⟨8225830775243700975215425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10967774366991601300287233 8225830775243700975215425)
          ·
            refine ⟨6169373081432775731411569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8225830775243700975215425 6169373081432775731411569)
            ·
              refine ⟨4627029811074581798558677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6169373081432775731411569 4627029811074581798558677)
              ·
                refine ⟨108446011197060510903719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4627029811074581798558677 108446011197060510903719)
                ·
                  rfl

theorem cell23_5702342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 2, 7].length) (baseStart_5702342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5702342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5702342 prefixEnd_5702342 := by exact prefixLift 5702342
  have htrace : WordTrace (prefixWord ++ tailWord_5702342) baseStart_5702342 baseEnd_5702342 := by
    simpa [prefixWord, tailWord_5702342, baseEnd_5702342] using wordTrace_append hprefix tailTrace_5702342
  have hstable : (prefixWord ++ tailWord_5702342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5702342).length < 2 ^ (prefixWord ++ tailWord_5702342).sum := by decide
  have hdescent : baseEnd_5702342 < baseStart_5702342 := by decide
  rcases family_descends (prefixWord ++ tailWord_5702342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5702394 : List Nat := [3, 1, 1, 1, 1, 3, 2, 1, 3, 7]
def baseStart_5702394 : Nat := 118140960795 + 5702394 * 2 ^ 59
def prefixEnd_5702394 : Nat := 4983230072969 + 3 ^ 40 * 5702394 * 2
def baseEnd_5702394 : Nat := 976023001104889196983391

theorem tailTrace_5702394 : CollatzResearch.WordTrace tailWord_5702394 prefixEnd_5702394 976023001104889196983391 := by
  unfold tailWord_5702394
  simp only [CollatzResearch.WordTrace]
  refine ⟨51995848925801976051214559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138655597135471936136572157 51995848925801976051214559)
  ·
    refine ⟨77993773388702964076821839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51995848925801976051214559 77993773388702964076821839)
    ·
      refine ⟨116990660083054446115232759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77993773388702964076821839 116990660083054446115232759)
      ·
        refine ⟨175485990124581669172849139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116990660083054446115232759 175485990124581669172849139)
        ·
          refine ⟨263228985186872503759273709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175485990124581669172849139 263228985186872503759273709)
          ·
            refine ⟨98710869445077188909727641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 263228985186872503759273709 98710869445077188909727641)
            ·
              refine ⟨74033152083807891682295731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98710869445077188909727641 74033152083807891682295731)
              ·
                refine ⟨111049728125711837523443597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74033152083807891682295731 111049728125711837523443597)
                ·
                  refine ⟨41643648047141939071291349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 111049728125711837523443597 41643648047141939071291349)
                  ·
                    refine ⟨976023001104889196983391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41643648047141939071291349 976023001104889196983391)
                    ·
                      rfl

theorem cell23_5702394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 3, 7].length) (baseStart_5702394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5702394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5702394 prefixEnd_5702394 := by exact prefixLift 5702394
  have htrace : WordTrace (prefixWord ++ tailWord_5702394) baseStart_5702394 baseEnd_5702394 := by
    simpa [prefixWord, tailWord_5702394, baseEnd_5702394] using wordTrace_append hprefix tailTrace_5702394
  have hstable : (prefixWord ++ tailWord_5702394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5702394).length < 2 ^ (prefixWord ++ tailWord_5702394).sum := by decide
  have hdescent : baseEnd_5702394 < baseStart_5702394 := by decide
  rcases family_descends (prefixWord ++ tailWord_5702394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5702462 : List Nat := [4, 2, 1, 2, 4, 1, 1, 1, 2, 5]
def baseStart_5702462 : Nat := 118140960795 + 5702462 * 2 ^ 59
def prefixEnd_5702462 : Nat := 4983230072969 + 3 ^ 40 * 5702462 * 2
def baseEnd_5702462 : Nat := 976034639999724441633287

theorem tailTrace_5702462 : CollatzResearch.WordTrace tailWord_5702462 prefixEnd_5702462 976034639999724441633287 := by
  unfold tailWord_5702462
  simp only [CollatzResearch.WordTrace]
  refine ⟨25998234483370193977291705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138657250577974367878889093 25998234483370193977291705)
  ·
    refine ⟨19498675862527645482968779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25998234483370193977291705 19498675862527645482968779)
    ·
      refine ⟨29248013793791468224453169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19498675862527645482968779 29248013793791468224453169)
      ·
        refine ⟨21936010345343601168339877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29248013793791468224453169 21936010345343601168339877)
        ·
          refine ⟨4113001939751925219063727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21936010345343601168339877 4113001939751925219063727)
          ·
            refine ⟨6169502909627887828595591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4113001939751925219063727 6169502909627887828595591)
            ·
              refine ⟨9254254364441831742893387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6169502909627887828595591 9254254364441831742893387)
              ·
                refine ⟨13881381546662747614340081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9254254364441831742893387 13881381546662747614340081)
                ·
                  refine ⟨10411036159997060710755061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13881381546662747614340081 10411036159997060710755061)
                  ·
                    refine ⟨976034639999724441633287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10411036159997060710755061 976034639999724441633287)
                    ·
                      rfl

theorem cell23_5702462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 1, 2, 5].length) (baseStart_5702462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5702462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5702462 prefixEnd_5702462 := by exact prefixLift 5702462
  have htrace : WordTrace (prefixWord ++ tailWord_5702462) baseStart_5702462 baseEnd_5702462 := by
    simpa [prefixWord, tailWord_5702462, baseEnd_5702462] using wordTrace_append hprefix tailTrace_5702462
  have hstable : (prefixWord ++ tailWord_5702462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5702462).length < 2 ^ (prefixWord ++ tailWord_5702462).sum := by decide
  have hdescent : baseEnd_5702462 < baseStart_5702462 := by decide
  rcases family_descends (prefixWord ++ tailWord_5702462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5702465 : List Nat := [1, 2, 5, 3, 1, 1, 1, 1, 1, 3, 4]
def baseStart_5702465 : Nat := 118140960795 + 5702465 * 2 ^ 59
def prefixEnd_5702465 : Nat := 4983230072969 + 3 ^ 40 * 5702465 * 2
def baseEnd_5702465 : Nat := 2928105460441136813162347

theorem tailTrace_5702465 : CollatzResearch.WordTrace tailWord_5702465 prefixEnd_5702465 2928105460441136813162347 := by
  unfold tailWord_5702465
  simp only [CollatzResearch.WordTrace]
  refine ⟨207985985285950683330692849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138657323523967122220461899 207985985285950683330692849)
  ·
    refine ⟨155989488964463012498019637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207985985285950683330692849 155989488964463012498019637)
    ·
      refine ⟨14624014590418407421689341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 155989488964463012498019637 14624014590418407421689341)
      ·
        refine ⟨5484005471406902783133503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14624014590418407421689341 5484005471406902783133503)
        ·
          refine ⟨8226008207110354174700255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5484005471406902783133503 8226008207110354174700255)
          ·
            refine ⟨12339012310665531262050383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8226008207110354174700255 12339012310665531262050383)
            ·
              refine ⟨18508518465998296893075575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12339012310665531262050383 18508518465998296893075575)
              ·
                refine ⟨27762777698997445339613363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18508518465998296893075575 27762777698997445339613363)
                ·
                  refine ⟨41644166548496168009420045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27762777698997445339613363 41644166548496168009420045)
                  ·
                    refine ⟨15616562455686063003532517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41644166548496168009420045 15616562455686063003532517)
                    ·
                      refine ⟨2928105460441136813162347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15616562455686063003532517 2928105460441136813162347)
                      ·
                        rfl

theorem cell23_5702465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_5702465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5702465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5702465 prefixEnd_5702465 := by exact prefixLift 5702465
  have htrace : WordTrace (prefixWord ++ tailWord_5702465) baseStart_5702465 baseEnd_5702465 := by
    simpa [prefixWord, tailWord_5702465, baseEnd_5702465] using wordTrace_append hprefix tailTrace_5702465
  have hstable : (prefixWord ++ tailWord_5702465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5702465).length < 2 ^ (prefixWord ++ tailWord_5702465).sum := by decide
  have hdescent : baseEnd_5702465 < baseStart_5702465 := by decide
  rcases family_descends (prefixWord ++ tailWord_5702465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5702492 : List Nat := [2, 2, 4, 2, 1, 1, 2, 4, 1, 4]
def baseStart_5702492 : Nat := 118140960795 + 5702492 * 2 ^ 59
def prefixEnd_5702492 : Nat := 4983230072969 + 3 ^ 40 * 5702492 * 2
def baseEnd_5702492 : Nat := 976039774806269402508241

theorem tailTrace_5702492 : CollatzResearch.WordTrace tailWord_5702492 prefixEnd_5702492 976039774806269402508241 := by
  unfold tailWord_5702492
  simp only [CollatzResearch.WordTrace]
  refine ⟨103993485028426433470962865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138657980037901911294617153 103993485028426433470962865)
  ·
    refine ⟨77995113771319825103222149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103993485028426433470962865 77995113771319825103222149)
    ·
      refine ⟨14624083832122467206854153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77995113771319825103222149 14624083832122467206854153)
      ·
        refine ⟨10968062874091850405140615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14624083832122467206854153 10968062874091850405140615)
        ·
          refine ⟨16452094311137775607710923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10968062874091850405140615 16452094311137775607710923)
          ·
            refine ⟨24678141466706663411566385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16452094311137775607710923 24678141466706663411566385)
            ·
              refine ⟨18508606100029997558674789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24678141466706663411566385 18508606100029997558674789)
              ·
                refine ⟨3470363643755624542251523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18508606100029997558674789 3470363643755624542251523)
                ·
                  refine ⟨5205545465633436813377285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3470363643755624542251523 5205545465633436813377285)
                  ·
                    refine ⟨976039774806269402508241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5205545465633436813377285 976039774806269402508241)
                    ·
                      rfl

theorem cell23_5702492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 4, 1, 4].length) (baseStart_5702492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5702492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5702492 prefixEnd_5702492 := by exact prefixLift 5702492
  have htrace : WordTrace (prefixWord ++ tailWord_5702492) baseStart_5702492 baseEnd_5702492 := by
    simpa [prefixWord, tailWord_5702492, baseEnd_5702492] using wordTrace_append hprefix tailTrace_5702492
  have hstable : (prefixWord ++ tailWord_5702492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5702492).length < 2 ^ (prefixWord ++ tailWord_5702492).sum := by decide
  have hdescent : baseEnd_5702492 < baseStart_5702492 := by decide
  rcases family_descends (prefixWord ++ tailWord_5702492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5702501 : List Nat := [1, 3, 1, 3, 1, 1, 2, 1, 5, 5]
def baseStart_5702501 : Nat := 118140960795 + 5702501 * 2 ^ 59
def prefixEnd_5702501 : Nat := 4983230072969 + 3 ^ 40 * 5702501 * 2
def baseEnd_5702501 : Nat := 976041315248232890770727

theorem tailTrace_5702501 : CollatzResearch.WordTrace tailWord_5702501 prefixEnd_5702501 976041315248232890770727 := by
  unfold tailWord_5702501
  simp only [CollatzResearch.WordTrace]
  refine ⟨207987298313820261479003357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138658198875880174319335571 207987298313820261479003357)
  ·
    refine ⟨77995236867682598054626259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207987298313820261479003357 77995236867682598054626259)
    ·
      refine ⟨116992855301523897081939389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77995236867682598054626259 116992855301523897081939389)
      ·
        refine ⟨43872320738071461405727271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116992855301523897081939389 43872320738071461405727271)
        ·
          refine ⟨65808481107107192108590907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43872320738071461405727271 65808481107107192108590907)
          ·
            refine ⟨98712721660660788162886361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65808481107107192108590907 98712721660660788162886361)
            ·
              refine ⟨74034541245495591122164771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98712721660660788162886361 74034541245495591122164771)
              ·
                refine ⟨111051811868243386683247157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74034541245495591122164771 111051811868243386683247157)
                ·
                  refine ⟨10411107362647817501554421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 111051811868243386683247157 10411107362647817501554421)
                  ·
                    refine ⟨976041315248232890770727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10411107362647817501554421 976041315248232890770727)
                    ·
                      rfl

theorem cell23_5702501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 5, 5].length) (baseStart_5702501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5702501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5702501 prefixEnd_5702501 := by exact prefixLift 5702501
  have htrace : WordTrace (prefixWord ++ tailWord_5702501) baseStart_5702501 baseEnd_5702501 := by
    simpa [prefixWord, tailWord_5702501, baseEnd_5702501] using wordTrace_append hprefix tailTrace_5702501
  have hstable : (prefixWord ++ tailWord_5702501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5702501).length < 2 ^ (prefixWord ++ tailWord_5702501).sum := by decide
  have hdescent : baseEnd_5702501 < baseStart_5702501 := by decide
  rcases family_descends (prefixWord ++ tailWord_5702501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5702508 : List Nat := [2, 2, 1, 1, 4, 1, 1, 1, 3, 5, 2]
def baseStart_5702508 : Nat := 118140960795 + 5702508 * 2 ^ 59
def prefixEnd_5702508 : Nat := 4983230072969 + 3 ^ 40 * 5702508 * 2
def baseEnd_5702508 : Nat := 2928127540109280144924649

theorem tailTrace_5702508 : CollatzResearch.WordTrace tailWord_5702508 prefixEnd_5702508 2928127540109280144924649 := by
  unfold tailWord_5702508
  simp only [CollatzResearch.WordTrace]
  refine ⟨103993776812397450837254089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138658369083196601116338785 103993776812397450837254089)
  ·
    refine ⟨77995332609298088127940567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103993776812397450837254089 77995332609298088127940567)
    ·
      refine ⟨116992998913947132191910851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77995332609298088127940567 116992998913947132191910851)
      ·
        refine ⟨175489498370920698287866277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116992998913947132191910851 175489498370920698287866277)
        ·
          refine ⟨32904280944547630928974927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 175489498370920698287866277 32904280944547630928974927)
          ·
            refine ⟨49356421416821446393462391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32904280944547630928974927 49356421416821446393462391)
            ·
              refine ⟨74034632125232169590193587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49356421416821446393462391 74034632125232169590193587)
              ·
                refine ⟨111051948187848254385290381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74034632125232169590193587 111051948187848254385290381)
                ·
                  refine ⟨41644480570443095394483893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 111051948187848254385290381 41644480570443095394483893)
                  ·
                    refine ⟨3904170053479040193232865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41644480570443095394483893 3904170053479040193232865)
                    ·
                      refine ⟨2928127540109280144924649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3904170053479040193232865 2928127540109280144924649)
                      ·
                        rfl

theorem cell23_5702508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 5, 2].length) (baseStart_5702508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5702508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5702508 prefixEnd_5702508 := by exact prefixLift 5702508
  have htrace : WordTrace (prefixWord ++ tailWord_5702508) baseStart_5702508 baseEnd_5702508 := by
    simpa [prefixWord, tailWord_5702508, baseEnd_5702508] using wordTrace_append hprefix tailTrace_5702508
  have hstable : (prefixWord ++ tailWord_5702508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5702508).length < 2 ^ (prefixWord ++ tailWord_5702508).sum := by decide
  have hdescent : baseEnd_5702508 < baseStart_5702508 := by decide
  rcases family_descends (prefixWord ++ tailWord_5702508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5702526 : List Nat := [4, 2, 3, 1, 2, 2, 1, 3, 1, 4]
def baseStart_5702526 : Nat := 118140960795 + 5702526 * 2 ^ 59
def prefixEnd_5702526 : Nat := 4983230072969 + 3 ^ 40 * 5702526 * 2
def baseEnd_5702526 : Nat := 976045594253687024833189

theorem tailTrace_5702526 : CollatzResearch.WordTrace tailWord_5702526 prefixEnd_5702526 976045594253687024833189 := by
  unfold tailWord_5702526
  simp only [CollatzResearch.WordTrace]
  refine ⟨25998526267341211343582929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138658806759153127165775621 25998526267341211343582929)
  ·
    refine ⟨19498894700505908507687197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25998526267341211343582929 19498894700505908507687197)
    ·
      refine ⟨7312085512689715690382699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19498894700505908507687197 7312085512689715690382699)
      ·
        refine ⟨10968128269034573535574049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7312085512689715690382699 10968128269034573535574049)
        ·
          refine ⟨8226096201775930151680537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10968128269034573535574049 8226096201775930151680537)
          ·
            refine ⟨6169572151331947613760403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8226096201775930151680537 6169572151331947613760403)
            ·
              refine ⟨9254358226997921420640605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6169572151331947613760403 9254358226997921420640605)
              ·
                refine ⟨3470384335124220532740227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9254358226997921420640605 3470384335124220532740227)
                ·
                  refine ⟨5205576502686330799110341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3470384335124220532740227 5205576502686330799110341)
                  ·
                    refine ⟨976045594253687024833189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5205576502686330799110341 976045594253687024833189)
                    ·
                      rfl

theorem cell23_5702526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_5702526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5702526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5702526 prefixEnd_5702526 := by exact prefixLift 5702526
  have htrace : WordTrace (prefixWord ++ tailWord_5702526) baseStart_5702526 baseEnd_5702526 := by
    simpa [prefixWord, tailWord_5702526, baseEnd_5702526] using wordTrace_append hprefix tailTrace_5702526
  have hstable : (prefixWord ++ tailWord_5702526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5702526).length < 2 ^ (prefixWord ++ tailWord_5702526).sum := by decide
  have hdescent : baseEnd_5702526 < baseStart_5702526 := by decide
  rcases family_descends (prefixWord ++ tailWord_5702526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5702531 : List Nat := [1, 1, 1, 3, 4, 1, 2, 1, 3, 6]
def baseStart_5702531 : Nat := 118140960795 + 5702531 * 2 ^ 59
def prefixEnd_5702531 : Nat := 4983230072969 + 3 ^ 40 * 5702531 * 2
def baseEnd_5702531 : Nat := 976046450054777851645681

theorem tailTrace_5702531 : CollatzResearch.WordTrace tailWord_5702531 prefixEnd_5702531 976046450054777851645681 := by
  unfold tailWord_5702531
  simp only [CollatzResearch.WordTrace]
  refine ⟨207988392503711576602595447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138658928335807717735063631 207988392503711576602595447)
  ·
    refine ⟨311982588755567364903893171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207988392503711576602595447 311982588755567364903893171)
    ·
      refine ⟨467973883133351047355839757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 311982588755567364903893171 467973883133351047355839757)
      ·
        refine ⟨175490206175006642758439909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 467973883133351047355839757 175490206175006642758439909)
        ·
          refine ⟨32904413657813745517207483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 175490206175006642758439909 32904413657813745517207483)
          ·
            refine ⟨49356620486720618275811225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32904413657813745517207483 49356620486720618275811225)
            ·
              refine ⟨37017465365040463706858419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49356620486720618275811225 37017465365040463706858419)
              ·
                refine ⟨55526198047560695560287629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37017465365040463706858419 55526198047560695560287629)
                ·
                  refine ⟨20822324267835260835107861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55526198047560695560287629 20822324267835260835107861)
                  ·
                    refine ⟨976046450054777851645681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20822324267835260835107861 976046450054777851645681)
                    ·
                      rfl

theorem cell23_5702531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 1, 3, 6].length) (baseStart_5702531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5702531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5702531 prefixEnd_5702531 := by exact prefixLift 5702531
  have htrace : WordTrace (prefixWord ++ tailWord_5702531) baseStart_5702531 baseEnd_5702531 := by
    simpa [prefixWord, tailWord_5702531, baseEnd_5702531] using wordTrace_append hprefix tailTrace_5702531
  have hstable : (prefixWord ++ tailWord_5702531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5702531).length < 2 ^ (prefixWord ++ tailWord_5702531).sum := by decide
  have hdescent : baseEnd_5702531 < baseStart_5702531 := by decide
  rcases family_descends (prefixWord ++ tailWord_5702531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5702549 : List Nat := [1, 3, 2, 1, 1, 5, 3, 2, 1, 1, 3]
def baseStart_5702549 : Nat := 118140960795 + 5702549 * 2 ^ 59
def prefixEnd_5702549 : Nat := 4983230072969 + 3 ^ 40 * 5702549 * 2
def baseEnd_5702549 : Nat := 2928148592816114484511961

theorem tailTrace_5702549 : CollatzResearch.WordTrace tailWord_5702549 prefixEnd_5702549 2928148592816114484511961 := by
  unfold tailWord_5702549
  simp only [CollatzResearch.WordTrace]
  refine ⟨207989049017646365676750701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138659366011764243784500467 207989049017646365676750701)
  ·
    refine ⟨77995893381617387128781513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207989049017646365676750701 77995893381617387128781513)
    ·
      refine ⟨58496920036213040346586135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77995893381617387128781513 58496920036213040346586135)
      ·
        refine ⟨87745380054319560519879203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58496920036213040346586135 87745380054319560519879203)
        ·
          refine ⟨131618070081479340779818805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87745380054319560519879203 131618070081479340779818805)
          ·
            refine ⟨12339194070138688198108013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 131618070081479340779818805 12339194070138688198108013)
            ·
              refine ⟨4627197776302008074290505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12339194070138688198108013 4627197776302008074290505)
              ·
                refine ⟨3470398332226506055717879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4627197776302008074290505 3470398332226506055717879)
                ·
                  refine ⟨5205597498339759083576819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3470398332226506055717879 5205597498339759083576819)
                  ·
                    refine ⟨7808396247509638625365229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5205597498339759083576819 7808396247509638625365229)
                    ·
                      refine ⟨2928148592816114484511961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7808396247509638625365229 2928148592816114484511961)
                      ·
                        rfl

theorem cell23_5702549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 3, 2, 1, 1, 3].length) (baseStart_5702549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5702549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5702549 prefixEnd_5702549 := by exact prefixLift 5702549
  have htrace : WordTrace (prefixWord ++ tailWord_5702549) baseStart_5702549 baseEnd_5702549 := by
    simpa [prefixWord, tailWord_5702549, baseEnd_5702549] using wordTrace_append hprefix tailTrace_5702549
  have hstable : (prefixWord ++ tailWord_5702549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5702549).length < 2 ^ (prefixWord ++ tailWord_5702549).sum := by decide
  have hdescent : baseEnd_5702549 < baseStart_5702549 := by decide
  rcases family_descends (prefixWord ++ tailWord_5702549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5702551 : List Nat := [1, 1, 3, 3, 1, 2, 1, 1, 3, 1, 6]
def baseStart_5702551 : Nat := 118140960795 + 5702551 * 2 ^ 59
def prefixEnd_5702551 : Nat := 4983230072969 + 3 ^ 40 * 5702551 * 2
def baseEnd_5702551 : Nat := 2928149619777423476686951

theorem tailTrace_5702551 : CollatzResearch.WordTrace tailWord_5702551 prefixEnd_5702551 2928149619777423476686951 := by
  unfold tailWord_5702551
  simp only [CollatzResearch.WordTrace]
  refine ⟨207989121963639120018323507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138659414642426080012215671 207989121963639120018323507)
  ·
    refine ⟨311983682945458680027485261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207989121963639120018323507 311983682945458680027485261)
    ·
      refine ⟨116993881104547005010306973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 311983682945458680027485261 116993881104547005010306973)
      ·
        refine ⟨43872705414205126878865115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116993881104547005010306973 43872705414205126878865115)
        ·
          refine ⟨65809058121307690318297673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43872705414205126878865115 65809058121307690318297673)
          ·
            refine ⟨49356793590980767738723255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65809058121307690318297673 49356793590980767738723255)
            ·
              refine ⟨74035190386471151608084883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49356793590980767738723255 74035190386471151608084883)
              ·
                refine ⟨111052785579706727412127325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74035190386471151608084883 111052785579706727412127325)
                ·
                  refine ⟨41644794592390022779547747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 111052785579706727412127325 41644794592390022779547747)
                  ·
                    refine ⟨62467191888585034169321621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41644794592390022779547747 62467191888585034169321621)
                    ·
                      refine ⟨2928149619777423476686951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62467191888585034169321621 2928149619777423476686951)
                      ·
                        rfl

theorem cell23_5702551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_5702551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5702551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5702551 prefixEnd_5702551 := by exact prefixLift 5702551
  have htrace : WordTrace (prefixWord ++ tailWord_5702551) baseStart_5702551 baseEnd_5702551 := by
    simpa [prefixWord, tailWord_5702551, baseEnd_5702551] using wordTrace_append hprefix tailTrace_5702551
  have hstable : (prefixWord ++ tailWord_5702551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5702551).length < 2 ^ (prefixWord ++ tailWord_5702551).sum := by decide
  have hdescent : baseEnd_5702551 < baseStart_5702551 := by decide
  rcases family_descends (prefixWord ++ tailWord_5702551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5702592 : List Nat := [2, 1, 1, 2, 3, 4, 3, 1, 1, 2, 3]
def baseStart_5702592 : Nat := 118140960795 + 5702592 * 2 ^ 59
def prefixEnd_5702592 : Nat := 4983230072969 + 3 ^ 40 * 5702592 * 2
def baseEnd_5702592 : Nat := 2928170672484257816274263

theorem tailTrace_5702592 : CollatzResearch.WordTrace tailWord_5702592 prefixEnd_5702592 2928170672484257816274263 := by
  unfold tailWord_5702592
  simp only [CollatzResearch.WordTrace]
  refine ⟨103995308678245292010283015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138660411570993722680377353 103995308678245292010283015)
  ·
    refine ⟨155992963017367938015424523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103995308678245292010283015 155992963017367938015424523)
    ·
      refine ⟨233989444526051907023136785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155992963017367938015424523 233989444526051907023136785)
      ·
        refine ⟨175492083394538930267352589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 233989444526051907023136785 175492083394538930267352589)
        ·
          refine ⟨65809531272952098850257221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 175492083394538930267352589 65809531272952098850257221)
          ·
            refine ⟨12339287113678518534423229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65809531272952098850257221 12339287113678518534423229)
            ·
              refine ⟨4627232667629444450408711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12339287113678518534423229 4627232667629444450408711)
              ·
                refine ⟨6940849001444166675613067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4627232667629444450408711 6940849001444166675613067)
                ·
                  refine ⟨10411273502166250013419601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6940849001444166675613067 10411273502166250013419601)
                  ·
                    refine ⟨7808455126624687510064701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10411273502166250013419601 7808455126624687510064701)
                    ·
                      refine ⟨2928170672484257816274263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7808455126624687510064701 2928170672484257816274263)
                      ·
                        rfl

theorem cell23_5702592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 3, 1, 1, 2, 3].length) (baseStart_5702592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5702592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5702592 prefixEnd_5702592 := by exact prefixLift 5702592
  have htrace : WordTrace (prefixWord ++ tailWord_5702592) baseStart_5702592 baseEnd_5702592 := by
    simpa [prefixWord, tailWord_5702592, baseEnd_5702592] using wordTrace_append hprefix tailTrace_5702592
  have hstable : (prefixWord ++ tailWord_5702592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5702592).length < 2 ^ (prefixWord ++ tailWord_5702592).sum := by decide
  have hdescent : baseEnd_5702592 < baseStart_5702592 := by decide
  rcases family_descends (prefixWord ++ tailWord_5702592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5702606 : List Nat := [4, 1, 1, 1, 2, 3, 4, 2, 1, 2, 2]
def baseStart_5702606 : Nat := 118140960795 + 5702606 * 2 ^ 59
def prefixEnd_5702606 : Nat := 4983230072969 + 3 ^ 40 * 5702606 * 2
def baseEnd_5702606 : Nat := 2928177861213420761499199

theorem tailTrace_5702606 : CollatzResearch.WordTrace tailWord_5702606 prefixEnd_5702606 2928177861213420761499199 := by
  unfold tailWord_5702606
  simp only [CollatzResearch.WordTrace]
  refine ⟨25998890997304983051446959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138660751985626576274383781 25998890997304983051446959)
  ·
    refine ⟨38998336495957474577170439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25998890997304983051446959 38998336495957474577170439)
    ·
      refine ⟨58497504743936211865755659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38998336495957474577170439 58497504743936211865755659)
      ·
        refine ⟨87746257115904317798633489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58497504743936211865755659 87746257115904317798633489)
        ·
          refine ⟨65809692836928238348975117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87746257115904317798633489 65809692836928238348975117)
          ·
            refine ⟨24678634813848089380865669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65809692836928238348975117 24678634813848089380865669)
            ·
              refine ⟨4627244027596516758912313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24678634813848089380865669 4627244027596516758912313)
              ·
                refine ⟨3470433020697387569184235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4627244027596516758912313 3470433020697387569184235)
                ·
                  refine ⟨5205649531046081353776353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3470433020697387569184235 5205649531046081353776353)
                  ·
                    refine ⟨3904237148284561015332265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5205649531046081353776353 3904237148284561015332265)
                    ·
                      refine ⟨2928177861213420761499199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3904237148284561015332265 2928177861213420761499199)
                      ·
                        rfl

theorem cell23_5702606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 4, 2, 1, 2, 2].length) (baseStart_5702606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5702606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5702606 prefixEnd_5702606 := by exact prefixLift 5702606
  have htrace : WordTrace (prefixWord ++ tailWord_5702606) baseStart_5702606 baseEnd_5702606 := by
    simpa [prefixWord, tailWord_5702606, baseEnd_5702606] using wordTrace_append hprefix tailTrace_5702606
  have hstable : (prefixWord ++ tailWord_5702606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5702606).length < 2 ^ (prefixWord ++ tailWord_5702606).sum := by decide
  have hdescent : baseEnd_5702606 < baseStart_5702606 := by decide
  rcases family_descends (prefixWord ++ tailWord_5702606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5702651 : List Nat := [1, 1, 1, 1, 1, 3, 3, 1, 11]
def baseStart_5702651 : Nat := 118140960795 + 5702651 * 2 ^ 59
def prefixEnd_5702651 : Nat := 4983230072969 + 3 ^ 40 * 5702651 * 2
def baseEnd_5702651 : Nat := 325355663093652565048499

theorem tailTrace_5702651 : CollatzResearch.WordTrace tailWord_5702651 prefixEnd_5702651 325355663093652565048499 := by
  unfold tailWord_5702651
  simp only [CollatzResearch.WordTrace]
  refine ⟨207992769263276837096963807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138661846175517891397975871 207992769263276837096963807)
  ·
    refine ⟨311989153894915255645445711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207992769263276837096963807 311989153894915255645445711)
    ·
      refine ⟨467983730842372883468168567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 311989153894915255645445711 467983730842372883468168567)
      ·
        refine ⟨701975596263559325202252851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 467983730842372883468168567 701975596263559325202252851)
        ·
          refine ⟨1052963394395338987803379277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 701975596263559325202252851 1052963394395338987803379277)
          ·
            refine ⟨394861272898252120426267229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1052963394395338987803379277 394861272898252120426267229)
            ·
              refine ⟨148072977336844545159850211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 394861272898252120426267229 148072977336844545159850211)
              ·
                refine ⟨222109466005266817739775317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 148072977336844545159850211 222109466005266817739775317)
                ·
                  refine ⟨325355663093652565048499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 222109466005266817739775317 325355663093652565048499)
                  ·
                    rfl

theorem cell23_5702651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 11].length) (baseStart_5702651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5702651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5702651 prefixEnd_5702651 := by exact prefixLift 5702651
  have htrace : WordTrace (prefixWord ++ tailWord_5702651) baseStart_5702651 baseEnd_5702651 := by
    simpa [prefixWord, tailWord_5702651, baseEnd_5702651] using wordTrace_append hprefix tailTrace_5702651
  have hstable : (prefixWord ++ tailWord_5702651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5702651).length < 2 ^ (prefixWord ++ tailWord_5702651).sum := by decide
  have hdescent : baseEnd_5702651 < baseStart_5702651 := by decide
  rcases family_descends (prefixWord ++ tailWord_5702651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5702668 : List Nat := [2, 2, 1, 2, 3, 2, 1, 3, 7]
def baseStart_5702668 : Nat := 118140960795 + 5702668 * 2 ^ 59
def prefixEnd_5702668 : Nat := 4983230072969 + 3 ^ 40 * 5702668 * 2
def baseEnd_5702668 : Nat := 325356633001555502102657

theorem tailTrace_5702668 : CollatzResearch.WordTrace tailWord_5702668 prefixEnd_5702668 325356633001555502102657 := by
  unfold tailWord_5702668
  simp only [CollatzResearch.WordTrace]
  refine ⟨103996694652107624500166329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138662259536143499333555105 103996694652107624500166329)
  ·
    refine ⟨77997520989080718375124747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103996694652107624500166329 77997520989080718375124747)
    ·
      refine ⟨116996281483621077562687121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77997520989080718375124747 116996281483621077562687121)
      ·
        refine ⟨87747211112715808172015341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116996281483621077562687121 87747211112715808172015341)
        ·
          refine ⟨32905204167268428064505753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87747211112715808172015341 32905204167268428064505753)
          ·
            refine ⟨24678903125451321048379315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32905204167268428064505753 24678903125451321048379315)
            ·
              refine ⟨37018354688176981572568973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24678903125451321048379315 37018354688176981572568973)
              ·
                refine ⟨13881883008066368089713365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37018354688176981572568973 13881883008066368089713365)
                ·
                  refine ⟨325356633001555502102657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13881883008066368089713365 325356633001555502102657)
                  ·
                    rfl

theorem cell23_5702668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 3, 7].length) (baseStart_5702668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5702668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5702668 prefixEnd_5702668 := by exact prefixLift 5702668
  have htrace : WordTrace (prefixWord ++ tailWord_5702668) baseStart_5702668 baseEnd_5702668 := by
    simpa [prefixWord, tailWord_5702668, baseEnd_5702668] using wordTrace_append hprefix tailTrace_5702668
  have hstable : (prefixWord ++ tailWord_5702668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5702668).length < 2 ^ (prefixWord ++ tailWord_5702668).sum := by decide
  have hdescent : baseEnd_5702668 < baseStart_5702668 := by decide
  rcases family_descends (prefixWord ++ tailWord_5702668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5702679 : List Nat := [1, 1, 3, 5, 1, 3, 1, 1, 1, 4, 2]
def baseStart_5702679 : Nat := 118140960795 + 5702679 * 2 ^ 59
def prefixEnd_5702679 : Nat := 4983230072969 + 3 ^ 40 * 5702679 * 2
def baseEnd_5702679 : Nat := 2928215345301198975886363

theorem tailTrace_5702679 : CollatzResearch.WordTrace tailWord_5702679 prefixEnd_5702679 2928215345301198975886363 := by
  unfold tailWord_5702679
  simp only [CollatzResearch.WordTrace]
  refine ⟨207993790507175397878983091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138662527004783598585988727 207993790507175397878983091)
  ·
    refine ⟨311990685760763096818474637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207993790507175397878983091 311990685760763096818474637)
    ·
      refine ⟨116996507160286161306927989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 311990685760763096818474637 116996507160286161306927989)
      ·
        refine ⟨10968422546276827622524499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 116996507160286161306927989 10968422546276827622524499)
        ·
          refine ⟨16452633819415241433786749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10968422546276827622524499 16452633819415241433786749)
          ·
            refine ⟨6169737682280715537670031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16452633819415241433786749 6169737682280715537670031)
            ·
              refine ⟨9254606523421073306505047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6169737682280715537670031 9254606523421073306505047)
              ·
                refine ⟨13881909785131609959757571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9254606523421073306505047 13881909785131609959757571)
                ·
                  refine ⟨20822864677697414939636357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13881909785131609959757571 20822864677697414939636357)
                  ·
                    refine ⟨3904287127068265301181817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20822864677697414939636357 3904287127068265301181817)
                    ·
                      refine ⟨2928215345301198975886363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3904287127068265301181817 2928215345301198975886363)
                      ·
                        rfl

theorem cell23_5702679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 1, 1, 4, 2].length) (baseStart_5702679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5702679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5702679 prefixEnd_5702679 := by exact prefixLift 5702679
  have htrace : WordTrace (prefixWord ++ tailWord_5702679) baseStart_5702679 baseEnd_5702679 := by
    simpa [prefixWord, tailWord_5702679, baseEnd_5702679] using wordTrace_append hprefix tailTrace_5702679
  have hstable : (prefixWord ++ tailWord_5702679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5702679).length < 2 ^ (prefixWord ++ tailWord_5702679).sum := by decide
  have hdescent : baseEnd_5702679 < baseStart_5702679 := by decide
  rcases family_descends (prefixWord ++ tailWord_5702679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5702749 : List Nat := [1, 4, 4, 1, 2, 1, 2, 1, 2, 5]
def baseStart_5702749 : Nat := 118140960795 + 5702749 * 2 ^ 59
def prefixEnd_5702749 : Nat := 4983230072969 + 3 ^ 40 * 5702749 * 2
def baseEnd_5702749 : Nat := 976083762982337900670347

theorem tailTrace_5702749 : CollatzResearch.WordTrace tailWord_5702749 prefixEnd_5702749 976083762982337900670347 := by
  unfold tailWord_5702749
  simp only [CollatzResearch.WordTrace]
  refine ⟨207996343616921799834031301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138664229077947866556020867 207996343616921799834031301)
  ·
    refine ⟨38999314428172837468880869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 207996343616921799834031301 38999314428172837468880869)
    ·
      refine ⟨7312371455282407025415163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38999314428172837468880869 7312371455282407025415163)
      ·
        refine ⟨10968557182923610538122745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7312371455282407025415163 10968557182923610538122745)
        ·
          refine ⟨8226417887192707903592059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10968557182923610538122745 8226417887192707903592059)
          ·
            refine ⟨12339626830789061855388089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8226417887192707903592059 12339626830789061855388089)
            ·
              refine ⟨9254720123091796391541067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12339626830789061855388089 9254720123091796391541067)
              ·
                refine ⟨13882080184637694587311601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9254720123091796391541067 13882080184637694587311601)
                ·
                  refine ⟨10411560138478270940483701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13882080184637694587311601 10411560138478270940483701)
                  ·
                    refine ⟨976083762982337900670347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10411560138478270940483701 976083762982337900670347)
                    ·
                      rfl

theorem cell23_5702749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_5702749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5702749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5702749 prefixEnd_5702749 := by exact prefixLift 5702749
  have htrace : WordTrace (prefixWord ++ tailWord_5702749) baseStart_5702749 baseEnd_5702749 := by
    simpa [prefixWord, tailWord_5702749, baseEnd_5702749] using wordTrace_append hprefix tailTrace_5702749
  have hstable : (prefixWord ++ tailWord_5702749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5702749).length < 2 ^ (prefixWord ++ tailWord_5702749).sum := by decide
  have hdescent : baseEnd_5702749 < baseStart_5702749 := by decide
  rcases family_descends (prefixWord ++ tailWord_5702749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5702775 : List Nat := [1, 1, 3, 1, 1, 4, 4, 2, 6]
def baseStart_5702775 : Nat := 118140960795 + 5702775 * 2 ^ 59
def prefixEnd_5702775 : Nat := 4983230072969 + 3 ^ 40 * 5702775 * 2
def baseEnd_5702775 : Nat := 325362737716003400031769

theorem tailTrace_5702775 : CollatzResearch.WordTrace tailWord_5702775 prefixEnd_5702775 325362737716003400031769 := by
  unfold tailWord_5702775
  simp only [CollatzResearch.WordTrace]
  refine ⟨207997291914827606274477779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138664861276551737516318519 207997291914827606274477779)
  ·
    refine ⟨311995937872241409411716669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207997291914827606274477779 311995937872241409411716669)
    ·
      refine ⟨116998476702090528529393751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 311995937872241409411716669 116998476702090528529393751)
      ·
        refine ⟨175497715053135792794090627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116998476702090528529393751 175497715053135792794090627)
        ·
          refine ⟨263246572579703689191135941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175497715053135792794090627 263246572579703689191135941)
          ·
            refine ⟨49358732358694441723337989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 263246572579703689191135941 49358732358694441723337989)
            ·
              refine ⟨9254762317255207823125873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49358732358694441723337989 9254762317255207823125873)
              ·
                refine ⟨6941071737941405867344405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9254762317255207823125873 6941071737941405867344405)
                ·
                  refine ⟨325362737716003400031769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6941071737941405867344405 325362737716003400031769)
                  ·
                    rfl

theorem cell23_5702775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 2, 6].length) (baseStart_5702775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5702775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5702775 prefixEnd_5702775 := by exact prefixLift 5702775
  have htrace : WordTrace (prefixWord ++ tailWord_5702775) baseStart_5702775 baseEnd_5702775 := by
    simpa [prefixWord, tailWord_5702775, baseEnd_5702775] using wordTrace_append hprefix tailTrace_5702775
  have hstable : (prefixWord ++ tailWord_5702775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5702775).length < 2 ^ (prefixWord ++ tailWord_5702775).sum := by decide
  have hdescent : baseEnd_5702775 < baseStart_5702775 := by decide
  rcases family_descends (prefixWord ++ tailWord_5702775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5702845 : List Nat := [1, 4, 1, 2, 1, 1, 3, 1, 3, 1, 5]
def baseStart_5702845 : Nat := 118140960795 + 5702845 * 2 ^ 59
def prefixEnd_5702845 : Nat := 4983230072969 + 3 ^ 40 * 5702845 * 2
def baseEnd_5702845 : Nat := 2928300583089845326410599

theorem tailTrace_5702845 : CollatzResearch.WordTrace tailWord_5702845 prefixEnd_5702845 2928300583089845326410599 := by
  unfold tailWord_5702845
  simp only [CollatzResearch.WordTrace]
  refine ⟨207999845024574008229525989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138666563349716005486350659 207999845024574008229525989)
  ·
    refine ⟨38999970942107626543036123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 207999845024574008229525989 38999970942107626543036123)
    ·
      refine ⟨58499956413161439814554185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38999970942107626543036123 58499956413161439814554185)
      ·
        refine ⟨43874967309871079860915639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58499956413161439814554185 43874967309871079860915639)
        ·
          refine ⟨65812450964806619791373459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43874967309871079860915639 65812450964806619791373459)
          ·
            refine ⟨98718676447209929687060189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65812450964806619791373459 98718676447209929687060189)
            ·
              refine ⟨37019503667703723632647571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 98718676447209929687060189 37019503667703723632647571)
              ·
                refine ⟨55529255501555585448971357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37019503667703723632647571 55529255501555585448971357)
                ·
                  refine ⟨20823470813083344543364259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55529255501555585448971357 20823470813083344543364259)
                  ·
                    refine ⟨31235206219625016815046389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20823470813083344543364259 31235206219625016815046389)
                    ·
                      refine ⟨2928300583089845326410599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31235206219625016815046389 2928300583089845326410599)
                      ·
                        rfl

theorem cell23_5702845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 1, 3, 1, 5].length) (baseStart_5702845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5702845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5702845 prefixEnd_5702845 := by exact prefixLift 5702845
  have htrace : WordTrace (prefixWord ++ tailWord_5702845) baseStart_5702845 baseEnd_5702845 := by
    simpa [prefixWord, tailWord_5702845, baseEnd_5702845] using wordTrace_append hprefix tailTrace_5702845
  have hstable : (prefixWord ++ tailWord_5702845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5702845).length < 2 ^ (prefixWord ++ tailWord_5702845).sum := by decide
  have hdescent : baseEnd_5702845 < baseStart_5702845 := by decide
  rcases family_descends (prefixWord ++ tailWord_5702845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5702893 : List Nat := [1, 5, 1, 2, 2, 3, 1, 1, 3, 2, 2]
def baseStart_5702893 : Nat := 118140960795 + 5702893 * 2 ^ 59
def prefixEnd_5702893 : Nat := 4983230072969 + 3 ^ 40 * 5702893 * 2
def baseEnd_5702893 : Nat := 2928325230161261138610379

theorem tailTrace_5702893 : CollatzResearch.WordTrace tailWord_5702893 prefixEnd_5702893 2928325230161261138610379 := by
  unfold tailWord_5702893
  simp only [CollatzResearch.WordTrace]
  refine ⟨208001595728400112427273333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138667730485600074951515555 208001595728400112427273333)
  ·
    refine ⟨19500149599537510540056875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 208001595728400112427273333 19500149599537510540056875)
    ·
      refine ⟨29250224399306265810085313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19500149599537510540056875 29250224399306265810085313)
      ·
        refine ⟨21937668299479699357563985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29250224399306265810085313 21937668299479699357563985)
        ·
          refine ⟨16453251224609774518172989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21937668299479699357563985 16453251224609774518172989)
          ·
            refine ⟨6169969209228665444314871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16453251224609774518172989 6169969209228665444314871)
            ·
              refine ⟨9254953813842998166472307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6169969209228665444314871 9254953813842998166472307)
              ·
                refine ⟨13882430720764497249708461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9254953813842998166472307 13882430720764497249708461)
                ·
                  refine ⟨5205911520286686468640673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13882430720764497249708461 5205911520286686468640673)
                  ·
                    refine ⟨3904433640215014851480505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5205911520286686468640673 3904433640215014851480505)
                    ·
                      refine ⟨2928325230161261138610379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3904433640215014851480505 2928325230161261138610379)
                      ·
                        rfl

theorem cell23_5702893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 1, 3, 2, 2].length) (baseStart_5702893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5702893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5702893 prefixEnd_5702893 := by exact prefixLift 5702893
  have htrace : WordTrace (prefixWord ++ tailWord_5702893) baseStart_5702893 baseEnd_5702893 := by
    simpa [prefixWord, tailWord_5702893, baseEnd_5702893] using wordTrace_append hprefix tailTrace_5702893
  have hstable : (prefixWord ++ tailWord_5702893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5702893).length < 2 ^ (prefixWord ++ tailWord_5702893).sum := by decide
  have hdescent : baseEnd_5702893 < baseStart_5702893 := by decide
  rcases family_descends (prefixWord ++ tailWord_5702893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5702930 : List Nat := [3, 2, 4, 2, 1, 1, 3, 1, 1, 2, 3]
def baseStart_5702930 : Nat := 118140960795 + 5702930 * 2 ^ 59
def prefixEnd_5702930 : Nat := 4983230072969 + 3 ^ 40 * 5702930 * 2
def baseEnd_5702930 : Nat := 2928344228945477493847709

theorem tailTrace_5702930 : CollatzResearch.WordTrace tailWord_5702930 prefixEnd_5702930 2928344228945477493847709 := by
  unfold tailWord_5702930
  simp only [CollatzResearch.WordTrace]
  refine ⟨52000736307316516936592561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138668630152844045164246829 52000736307316516936592561)
  ·
    refine ⟨39000552230487387702444421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52000736307316516936592561 39000552230487387702444421)
    ·
      refine ⟨7312603543216385194208329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39000552230487387702444421 7312603543216385194208329)
      ·
        refine ⟨5484452657412288895656247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7312603543216385194208329 5484452657412288895656247)
        ·
          refine ⟨8226678986118433343484371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5484452657412288895656247 8226678986118433343484371)
          ·
            refine ⟨12340018479177650015226557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8226678986118433343484371 12340018479177650015226557)
            ·
              refine ⟨4627506929691618755709959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12340018479177650015226557 4627506929691618755709959)
              ·
                refine ⟨6941260394537428133564939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4627506929691618755709959 6941260394537428133564939)
                ·
                  refine ⟨10411890591806142200347409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6941260394537428133564939 10411890591806142200347409)
                  ·
                    refine ⟨7808917943854606650260557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10411890591806142200347409 7808917943854606650260557)
                    ·
                      refine ⟨2928344228945477493847709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7808917943854606650260557 2928344228945477493847709)
                      ·
                        rfl

theorem cell23_5702930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_5702930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5702930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5702930 prefixEnd_5702930 := by exact prefixLift 5702930
  have htrace : WordTrace (prefixWord ++ tailWord_5702930) baseStart_5702930 baseEnd_5702930 := by
    simpa [prefixWord, tailWord_5702930, baseEnd_5702930] using wordTrace_append hprefix tailTrace_5702930
  have hstable : (prefixWord ++ tailWord_5702930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5702930).length < 2 ^ (prefixWord ++ tailWord_5702930).sum := by decide
  have hdescent : baseEnd_5702930 < baseStart_5702930 := by decide
  rcases family_descends (prefixWord ++ tailWord_5702930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5702945 : List Nat := [1, 2, 3, 2, 1, 1, 1, 1, 2, 3, 6]
def baseStart_5702945 : Nat := 118140960795 + 5702945 * 2 ^ 59
def prefixEnd_5702945 : Nat := 4983230072969 + 3 ^ 40 * 5702945 * 2
def baseEnd_5702945 : Nat := 2928351931155294935160139

theorem tailTrace_5702945 : CollatzResearch.WordTrace tailWord_5702945 prefixEnd_5702945 2928351931155294935160139 := by
  unfold tailWord_5702945
  simp only [CollatzResearch.WordTrace]
  refine ⟨208003492324211725308166289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138668994882807816872110859 208003492324211725308166289)
  ·
    refine ⟨156002619243158793981124717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208003492324211725308166289 156002619243158793981124717)
    ·
      refine ⟨58500982216184547742921769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156002619243158793981124717 58500982216184547742921769)
      ·
        refine ⟨43875736662138410807191327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58500982216184547742921769 43875736662138410807191327)
        ·
          refine ⟨65813604993207616210786991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43875736662138410807191327 65813604993207616210786991)
          ·
            refine ⟨98720407489811424316180487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65813604993207616210786991 98720407489811424316180487)
            ·
              refine ⟨148080611234717136474270731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98720407489811424316180487 148080611234717136474270731)
              ·
                refine ⟨222120916852075704711406097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 148080611234717136474270731 222120916852075704711406097)
                ·
                  refine ⟨166590687639056778533554573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 222120916852075704711406097 166590687639056778533554573)
                  ·
                    refine ⟨62471507864646291950082965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 166590687639056778533554573 62471507864646291950082965)
                    ·
                      refine ⟨2928351931155294935160139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62471507864646291950082965 2928351931155294935160139)
                      ·
                        rfl

theorem cell23_5702945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_5702945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5702945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5702945 prefixEnd_5702945 := by exact prefixLift 5702945
  have htrace : WordTrace (prefixWord ++ tailWord_5702945) baseStart_5702945 baseEnd_5702945 := by
    simpa [prefixWord, tailWord_5702945, baseEnd_5702945] using wordTrace_append hprefix tailTrace_5702945
  have hstable : (prefixWord ++ tailWord_5702945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5702945).length < 2 ^ (prefixWord ++ tailWord_5702945).sum := by decide
  have hdescent : baseEnd_5702945 < baseStart_5702945 := by decide
  rcases family_descends (prefixWord ++ tailWord_5702945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5702962 : List Nat := [3, 2, 1, 1, 4, 1, 1, 1, 1, 4, 4]
def baseStart_5702962 : Nat := 118140960795 + 5702962 * 2 ^ 59
def prefixEnd_5702962 : Nat := 4983230072969 + 3 ^ 40 * 5702962 * 2
def baseEnd_5702962 : Nat := 2928360660326421368647561

theorem tailTrace_5702962 : CollatzResearch.WordTrace tailWord_5702962 prefixEnd_5702962 2928360660326421368647561 := by
  unfold tailWord_5702962
  simp only [CollatzResearch.WordTrace]
  refine ⟨52001028091287534302883785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138669408243433424807690093 52001028091287534302883785)
  ·
    refine ⟨39000771068465650727162839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52001028091287534302883785 39000771068465650727162839)
    ·
      refine ⟨58501156602698476090744259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39000771068465650727162839 58501156602698476090744259)
      ·
        refine ⟨87751734904047714136116389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58501156602698476090744259 87751734904047714136116389)
        ·
          refine ⟨16453450294508946400521823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87751734904047714136116389 16453450294508946400521823)
          ·
            refine ⟨24680175441763419600782735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16453450294508946400521823 24680175441763419600782735)
            ·
              refine ⟨37020263162645129401174103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24680175441763419600782735 37020263162645129401174103)
              ·
                refine ⟨55530394743967694101761155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37020263162645129401174103 55530394743967694101761155)
                ·
                  refine ⟨83295592115951541152641733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55530394743967694101761155 83295592115951541152641733)
                  ·
                    refine ⟨15617923521740913966120325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 83295592115951541152641733 15617923521740913966120325)
                    ·
                      refine ⟨2928360660326421368647561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15617923521740913966120325 2928360660326421368647561)
                      ·
                        rfl

theorem cell23_5702962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 1, 1, 4, 4].length) (baseStart_5702962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5702962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5702962 prefixEnd_5702962 := by exact prefixLift 5702962
  have htrace : WordTrace (prefixWord ++ tailWord_5702962) baseStart_5702962 baseEnd_5702962 := by
    simpa [prefixWord, tailWord_5702962, baseEnd_5702962] using wordTrace_append hprefix tailTrace_5702962
  have hstable : (prefixWord ++ tailWord_5702962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5702962).length < 2 ^ (prefixWord ++ tailWord_5702962).sum := by decide
  have hdescent : baseEnd_5702962 < baseStart_5702962 := by decide
  rcases family_descends (prefixWord ++ tailWord_5702962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5702972 : List Nat := [2, 2, 2, 2, 1, 4, 1, 2, 7]
def baseStart_5702972 : Nat := 118140960795 + 5702972 * 2 ^ 59
def prefixEnd_5702972 : Nat := 4983230072969 + 3 ^ 40 * 5702972 * 2
def baseEnd_5702972 : Nat := 325373977236996258835835

theorem tailTrace_5702972 : CollatzResearch.WordTrace tailWord_5702972 prefixEnd_5702972 325373977236996258835835 := by
  unfold tailWord_5702972
  simp only [CollatzResearch.WordTrace]
  refine ⟨104002238547556954459699585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138669651396742605946266113 104002238547556954459699585)
  ·
    refine ⟨78001678910667715844774689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104002238547556954459699585 78001678910667715844774689)
    ·
      refine ⟨58501259183000786883581017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78001678910667715844774689 58501259183000786883581017)
      ·
        refine ⟨43875944387250590162685763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58501259183000786883581017 43875944387250590162685763)
        ·
          refine ⟨65813916580875885244028645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43875944387250590162685763 65813916580875885244028645)
          ·
            refine ⟨12340109358914228483255371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65813916580875885244028645 12340109358914228483255371)
            ·
              refine ⟨18510164038371342724883057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12340109358914228483255371 18510164038371342724883057)
              ·
                refine ⟨13882623028778507043662293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18510164038371342724883057 13882623028778507043662293)
                ·
                  refine ⟨325373977236996258835835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13882623028778507043662293 325373977236996258835835)
                  ·
                    rfl

theorem cell23_5702972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 2, 7].length) (baseStart_5702972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5702972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5702972 prefixEnd_5702972 := by exact prefixLift 5702972
  have htrace : WordTrace (prefixWord ++ tailWord_5702972) baseStart_5702972 baseEnd_5702972 := by
    simpa [prefixWord, tailWord_5702972, baseEnd_5702972] using wordTrace_append hprefix tailTrace_5702972
  have hstable : (prefixWord ++ tailWord_5702972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5702972).length < 2 ^ (prefixWord ++ tailWord_5702972).sum := by decide
  have hdescent : baseEnd_5702972 < baseStart_5702972 := by decide
  rcases family_descends (prefixWord ++ tailWord_5702972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5703002 : List Nat := [3, 1, 1, 2, 1, 2, 2, 4, 2, 5]
def baseStart_5703002 : Nat := 118140960795 + 5703002 * 2 ^ 59
def prefixEnd_5703002 : Nat := 4983230072969 + 3 ^ 40 * 5703002 * 2
def baseEnd_5703002 : Nat := 976127066517533737382459

theorem tailTrace_5703002 : CollatzResearch.WordTrace tailWord_5703002 prefixEnd_5703002 976127066517533737382459 := by
  unfold tailWord_5703002
  simp only [CollatzResearch.WordTrace]
  refine ⟨52001392821251306010747815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138670380856670149361994173 52001392821251306010747815)
  ·
    refine ⟨78002089231876959016121723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52001392821251306010747815 78002089231876959016121723)
    ·
      refine ⟨117003133847815438524182585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78002089231876959016121723 117003133847815438524182585)
      ·
        refine ⟨87752350385861578893136939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117003133847815438524182585 87752350385861578893136939)
        ·
          refine ⟨131628525578792368339705409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87752350385861578893136939 131628525578792368339705409)
          ·
            refine ⟨98721394184094276254779057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131628525578792368339705409 98721394184094276254779057)
            ·
              refine ⟨74041045638070707191084293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98721394184094276254779057 74041045638070707191084293)
              ·
                refine ⟨13882696057138257598328305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74041045638070707191084293 13882696057138257598328305)
                ·
                  refine ⟨10412022042853693198746229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13882696057138257598328305 10412022042853693198746229)
                  ·
                    refine ⟨976127066517533737382459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10412022042853693198746229 976127066517533737382459)
                    ·
                      rfl

theorem cell23_5703002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 4, 2, 5].length) (baseStart_5703002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5703002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5703002 prefixEnd_5703002 := by exact prefixLift 5703002
  have htrace : WordTrace (prefixWord ++ tailWord_5703002) baseStart_5703002 baseEnd_5703002 := by
    simpa [prefixWord, tailWord_5703002, baseEnd_5703002] using wordTrace_append hprefix tailTrace_5703002
  have hstable : (prefixWord ++ tailWord_5703002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5703002).length < 2 ^ (prefixWord ++ tailWord_5703002).sum := by decide
  have hdescent : baseEnd_5703002 < baseStart_5703002 := by decide
  rcases family_descends (prefixWord ++ tailWord_5703002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5703079 : List Nat := [1, 1, 6, 1, 1, 1, 3, 3, 6]
def baseStart_5703079 : Nat := 118140960795 + 5703079 * 2 ^ 59
def prefixEnd_5703079 : Nat := 4983230072969 + 3 ^ 40 * 5703079 * 2
def baseEnd_5703079 : Nat := 325380081951444156764947

theorem tailTrace_5703079 : CollatzResearch.WordTrace tailWord_5703079 prefixEnd_5703079 325380081951444156764947 := by
  unfold tailWord_5703079
  simp only [CollatzResearch.WordTrace]
  refine ⟨208008379705726266193544291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138672253137150844129029527 208008379705726266193544291)
  ·
    refine ⟨312012569558589399290316437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208008379705726266193544291 312012569558589399290316437)
    ·
      refine ⟨14625589198058878091733583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 312012569558589399290316437 14625589198058878091733583)
      ·
        refine ⟨21938383797088317137600375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14625589198058878091733583 21938383797088317137600375)
        ·
          refine ⟨32907575695632475706400563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21938383797088317137600375 32907575695632475706400563)
          ·
            refine ⟨49361363543448713559600845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32907575695632475706400563 49361363543448713559600845)
            ·
              refine ⟨18510511328793267584850317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49361363543448713559600845 18510511328793267584850317)
              ·
                refine ⟨6941441748297475344318869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18510511328793267584850317 6941441748297475344318869)
                ·
                  refine ⟨325380081951444156764947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6941441748297475344318869 325380081951444156764947)
                  ·
                    rfl

theorem cell23_5703079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 3, 6].length) (baseStart_5703079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5703079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5703079 prefixEnd_5703079 := by exact prefixLift 5703079
  have htrace : WordTrace (prefixWord ++ tailWord_5703079) baseStart_5703079 baseEnd_5703079 := by
    simpa [prefixWord, tailWord_5703079, baseEnd_5703079] using wordTrace_append hprefix tailTrace_5703079
  have hstable : (prefixWord ++ tailWord_5703079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5703079).length < 2 ^ (prefixWord ++ tailWord_5703079).sum := by decide
  have hdescent : baseEnd_5703079 < baseStart_5703079 := by decide
  rcases family_descends (prefixWord ++ tailWord_5703079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5703126 : List Nat := [5, 2, 1, 1, 1, 2, 1, 2, 3, 5]
def baseStart_5703126 : Nat := 118140960795 + 5703126 * 2 ^ 59
def prefixEnd_5703126 : Nat := 4983230072969 + 3 ^ 40 * 5703126 * 2
def baseEnd_5703126 : Nat := 976148290384586242332269

theorem tailTrace_5703126 : CollatzResearch.WordTrace tailWord_5703126 prefixEnd_5703126 976148290384586242332269 := by
  unfold tailWord_5703126
  simp only [CollatzResearch.WordTrace]
  refine ⟨13000630871034749576281577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 138673395957703995480336821 13000630871034749576281577)
  ·
    refine ⟨9750473153276062182211183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13000630871034749576281577 9750473153276062182211183)
    ·
      refine ⟨14625709729914093273316775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9750473153276062182211183 14625709729914093273316775)
      ·
        refine ⟨21938564594871139909975163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14625709729914093273316775 21938564594871139909975163)
        ·
          refine ⟨32907846892306709864962745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21938564594871139909975163 32907846892306709864962745)
          ·
            refine ⟨24680885169230032398722059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32907846892306709864962745 24680885169230032398722059)
            ·
              refine ⟨37021327753845048598083089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24680885169230032398722059 37021327753845048598083089)
              ·
                refine ⟨27765995815383786448562317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37021327753845048598083089 27765995815383786448562317)
                ·
                  refine ⟨10412248430768919918210869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27765995815383786448562317 10412248430768919918210869)
                  ·
                    refine ⟨976148290384586242332269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10412248430768919918210869 976148290384586242332269)
                    ·
                      rfl

theorem cell23_5703126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_5703126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5703126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5703126 prefixEnd_5703126 := by exact prefixLift 5703126
  have htrace : WordTrace (prefixWord ++ tailWord_5703126) baseStart_5703126 baseEnd_5703126 := by
    simpa [prefixWord, tailWord_5703126, baseEnd_5703126] using wordTrace_append hprefix tailTrace_5703126
  have hstable : (prefixWord ++ tailWord_5703126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5703126).length < 2 ^ (prefixWord ++ tailWord_5703126).sum := by decide
  have hdescent : baseEnd_5703126 < baseStart_5703126 := by decide
  rcases family_descends (prefixWord ++ tailWord_5703126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5703129 : List Nat := [1, 2, 1, 2, 4, 2, 1, 2, 3, 1, 4]
def baseStart_5703129 : Nat := 118140960795 + 5703129 * 2 ^ 59
def prefixEnd_5703129 : Nat := 4983230072969 + 3 ^ 40 * 5703129 * 2
def baseEnd_5703129 : Nat := 2928446411595722215259293

theorem tailTrace_5703129 : CollatzResearch.WordTrace tailWord_5703129 prefixEnd_5703129 2928446411595722215259293 := by
  unfold tailWord_5703129
  simp only [CollatzResearch.WordTrace]
  refine ⟨208010203355545124732864441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138673468903696749821909627 208010203355545124732864441)
  ·
    refine ⟨156007652516658843549648331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208010203355545124732864441 156007652516658843549648331)
    ·
      refine ⟨234011478774988265324472497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156007652516658843549648331 234011478774988265324472497)
      ·
        refine ⟨175508609081241198993354373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 234011478774988265324472497 175508609081241198993354373)
        ·
          refine ⟨32907864202732724811253945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 175508609081241198993354373 32907864202732724811253945)
          ·
            refine ⟨24680898152049543608440459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32907864202732724811253945 24680898152049543608440459)
            ·
              refine ⟨37021347228074315412660689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24680898152049543608440459 37021347228074315412660689)
              ·
                refine ⟨27766010421055736559495517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37021347228074315412660689 27766010421055736559495517)
                ·
                  refine ⟨10412253907895901209810819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27766010421055736559495517 10412253907895901209810819)
                  ·
                    refine ⟨15618380861843851814716229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10412253907895901209810819 15618380861843851814716229)
                    ·
                      refine ⟨2928446411595722215259293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15618380861843851814716229 2928446411595722215259293)
                      ·
                        rfl

theorem cell23_5703129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 2, 3, 1, 4].length) (baseStart_5703129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5703129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5703129 prefixEnd_5703129 := by exact prefixLift 5703129
  have htrace : WordTrace (prefixWord ++ tailWord_5703129) baseStart_5703129 baseEnd_5703129 := by
    simpa [prefixWord, tailWord_5703129, baseEnd_5703129] using wordTrace_append hprefix tailTrace_5703129
  have hstable : (prefixWord ++ tailWord_5703129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5703129).length < 2 ^ (prefixWord ++ tailWord_5703129).sum := by decide
  have hdescent : baseEnd_5703129 < baseStart_5703129 := by decide
  rcases family_descends (prefixWord ++ tailWord_5703129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5703139 : List Nat := [1, 1, 1, 6, 2, 1, 1, 3, 1, 6]
def baseStart_5703139 : Nat := 118140960795 + 5703139 * 2 ^ 59
def prefixEnd_5703139 : Nat := 4983230072969 + 3 ^ 40 * 5703139 * 2
def baseEnd_5703139 : Nat := 976150515467422392044749

theorem tailTrace_5703139 : CollatzResearch.WordTrace tailWord_5703139 prefixEnd_5703139 976150515467422392044749 := by
  unfold tailWord_5703139
  simp only [CollatzResearch.WordTrace]
  refine ⟨208010568085508896440728471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138673712057005930960485647 208010568085508896440728471)
  ·
    refine ⟨312015852128263344661092707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208010568085508896440728471 312015852128263344661092707)
    ·
      refine ⟨468023778192395016991639061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312015852128263344661092707 468023778192395016991639061)
      ·
        refine ⟨21938614602768516421483081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 468023778192395016991639061 21938614602768516421483081)
        ·
          refine ⟨16453960952076387316112311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21938614602768516421483081 16453960952076387316112311)
          ·
            refine ⟨24680941428114580974168467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16453960952076387316112311 24680941428114580974168467)
            ·
              refine ⟨37021412142171871461252701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24680941428114580974168467 37021412142171871461252701)
              ·
                refine ⟨13883029553314451797969763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37021412142171871461252701 13883029553314451797969763)
                ·
                  refine ⟨20824544329971677696954645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13883029553314451797969763 20824544329971677696954645)
                  ·
                    refine ⟨976150515467422392044749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20824544329971677696954645 976150515467422392044749)
                    ·
                      rfl

theorem cell23_5703139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 3, 1, 6].length) (baseStart_5703139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5703139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5703139 prefixEnd_5703139 := by exact prefixLift 5703139
  have htrace : WordTrace (prefixWord ++ tailWord_5703139) baseStart_5703139 baseEnd_5703139 := by
    simpa [prefixWord, tailWord_5703139, baseEnd_5703139] using wordTrace_append hprefix tailTrace_5703139
  have hstable : (prefixWord ++ tailWord_5703139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5703139).length < 2 ^ (prefixWord ++ tailWord_5703139).sum := by decide
  have hdescent : baseEnd_5703139 < baseStart_5703139 := by decide
  rcases family_descends (prefixWord ++ tailWord_5703139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5703157 : List Nat := [1, 3, 5, 1, 1, 2, 2, 3, 1, 1, 3]
def baseStart_5703157 : Nat := 118140960795 + 5703157 * 2 ^ 59
def prefixEnd_5703157 : Nat := 4983230072969 + 3 ^ 40 * 5703157 * 2
def baseEnd_5703157 : Nat := 2928460789054048105709165

theorem tailTrace_5703157 : CollatzResearch.WordTrace tailWord_5703157 prefixEnd_5703157 2928460789054048105709165 := by
  unfold tailWord_5703157
  simp only [CollatzResearch.WordTrace]
  refine ⟨208011224599443685514883725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138674149732962457009922483 208011224599443685514883725)
  ·
    refine ⟨78004209224791382068081397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208011224599443685514883725 78004209224791382068081397)
    ·
      refine ⟨7312894614824192068882631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 78004209224791382068081397 7312894614824192068882631)
      ·
        refine ⟨10969341922236288103323947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7312894614824192068882631 10969341922236288103323947)
        ·
          refine ⟨16454012883354432154985921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10969341922236288103323947 16454012883354432154985921)
          ·
            refine ⟨12340509662515824116239441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16454012883354432154985921 12340509662515824116239441)
            ·
              refine ⟨9255382246886868087179581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12340509662515824116239441 9255382246886868087179581)
              ·
                refine ⟨3470768342582575532692343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9255382246886868087179581 3470768342582575532692343)
                ·
                  refine ⟨5206152513873863299038515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3470768342582575532692343 5206152513873863299038515)
                  ·
                    refine ⟨7809228770810794948557773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5206152513873863299038515 7809228770810794948557773)
                    ·
                      refine ⟨2928460789054048105709165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7809228770810794948557773 2928460789054048105709165)
                      ·
                        rfl

theorem cell23_5703157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 3, 1, 1, 3].length) (baseStart_5703157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5703157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5703157 prefixEnd_5703157 := by exact prefixLift 5703157
  have htrace : WordTrace (prefixWord ++ tailWord_5703157) baseStart_5703157 baseEnd_5703157 := by
    simpa [prefixWord, tailWord_5703157, baseEnd_5703157] using wordTrace_append hprefix tailTrace_5703157
  have hstable : (prefixWord ++ tailWord_5703157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5703157).length < 2 ^ (prefixWord ++ tailWord_5703157).sum := by decide
  have hdescent : baseEnd_5703157 < baseStart_5703157 := by decide
  rcases family_descends (prefixWord ++ tailWord_5703157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5703169 : List Nat := [1, 2, 4, 1, 4, 1, 10]
def baseStart_5703169 : Nat := 118140960795 + 5703169 * 2 ^ 59
def prefixEnd_5703169 : Nat := 4983230072969 + 3 ^ 40 * 5703169 * 2
def baseEnd_5703169 : Nat := 36153912973109901959989

theorem tailTrace_5703169 : CollatzResearch.WordTrace tailWord_5703169 prefixEnd_5703169 36153912973109901959989 := by
  unfold tailWord_5703169
  simp only [CollatzResearch.WordTrace]
  refine ⟨208011662275400211564320561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138674441516933474376213707 208011662275400211564320561)
  ·
    refine ⟨156008746706550158673240421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208011662275400211564320561 156008746706550158673240421)
    ·
      refine ⟨29251640007478154751232579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 156008746706550158673240421 29251640007478154751232579)
      ·
        refine ⟨43877460011217232126848869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29251640007478154751232579 43877460011217232126848869)
        ·
          refine ⟨8227023752103231023784163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43877460011217232126848869 8227023752103231023784163)
          ·
            refine ⟨12340535628154846535676245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8227023752103231023784163 12340535628154846535676245)
            ·
              refine ⟨36153912973109901959989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 12340535628154846535676245 36153912973109901959989)
              ·
                rfl

theorem cell23_5703169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 10].length) (baseStart_5703169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5703169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5703169 prefixEnd_5703169 := by exact prefixLift 5703169
  have htrace : WordTrace (prefixWord ++ tailWord_5703169) baseStart_5703169 baseEnd_5703169 := by
    simpa [prefixWord, tailWord_5703169, baseEnd_5703169] using wordTrace_append hprefix tailTrace_5703169
  have hstable : (prefixWord ++ tailWord_5703169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5703169).length < 2 ^ (prefixWord ++ tailWord_5703169).sum := by decide
  have hdescent : baseEnd_5703169 < baseStart_5703169 := by decide
  rcases family_descends (prefixWord ++ tailWord_5703169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5703174 : List Nat := [6, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3]
def baseStart_5703174 : Nat := 118140960795 + 5703174 * 2 ^ 59
def prefixEnd_5703174 : Nat := 4983230072969 + 3 ^ 40 * 5703174 * 2
def baseEnd_5703174 : Nat := 2928469518225174539196587

theorem tailTrace_5703174 : CollatzResearch.WordTrace tailWord_5703174 prefixEnd_5703174 2928469518225174539196587 := by
  unfold tailWord_5703174
  simp only [CollatzResearch.WordTrace]
  refine ⟨6500370145011940544320393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 138674563093588064945501717 6500370145011940544320393)
  ·
    refine ⟨4875277608758955408240295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6500370145011940544320393 4875277608758955408240295)
    ·
      refine ⟨7312916413138433112360443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4875277608758955408240295 7312916413138433112360443)
      ·
        refine ⟨10969374619707649668540665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7312916413138433112360443 10969374619707649668540665)
        ·
          refine ⟨8227030964780737251405499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10969374619707649668540665 8227030964780737251405499)
          ·
            refine ⟨12340546447171105877108249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8227030964780737251405499 12340546447171105877108249)
            ·
              refine ⟨9255409835378329407831187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12340546447171105877108249 9255409835378329407831187)
              ·
                refine ⟨13883114753067494111746781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9255409835378329407831187 13883114753067494111746781)
                ·
                  refine ⟨5206168032400310291905043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13883114753067494111746781 5206168032400310291905043)
                  ·
                    refine ⟨7809252048600465437857565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5206168032400310291905043 7809252048600465437857565)
                    ·
                      refine ⟨2928469518225174539196587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7809252048600465437857565 2928469518225174539196587)
                      ·
                        rfl

theorem cell23_5703174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_5703174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5703174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5703174 prefixEnd_5703174 := by exact prefixLift 5703174
  have htrace : WordTrace (prefixWord ++ tailWord_5703174) baseStart_5703174 baseEnd_5703174 := by
    simpa [prefixWord, tailWord_5703174, baseEnd_5703174] using wordTrace_append hprefix tailTrace_5703174
  have hstable : (prefixWord ++ tailWord_5703174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5703174).length < 2 ^ (prefixWord ++ tailWord_5703174).sum := by decide
  have hdescent : baseEnd_5703174 < baseStart_5703174 := by decide
  rcases family_descends (prefixWord ++ tailWord_5703174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5703180 : List Nat := [2, 2, 1, 2, 5, 1, 2, 1, 3, 2, 2]
def baseStart_5703180 : Nat := 118140960795 + 5703180 * 2 ^ 59
def prefixEnd_5703180 : Nat := 4983230072969 + 3 ^ 40 * 5703180 * 2
def baseEnd_5703180 : Nat := 2928472599109101515721559

theorem tailTrace_5703180 : CollatzResearch.WordTrace tailWord_5703180 prefixEnd_5703180 2928472599109101515721559 := by
  unfold tailWord_5703180
  simp only [CollatzResearch.WordTrace]
  refine ⟨104006031739180180221485497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138674708985573573628647329 104006031739180180221485497)
  ·
    refine ⟨78004523804385135166114123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104006031739180180221485497 78004523804385135166114123)
    ·
      refine ⟨117006785706577702749171185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78004523804385135166114123 117006785706577702749171185)
      ·
        refine ⟨87755089279933277061878389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117006785706577702749171185 87755089279933277061878389)
        ·
          refine ⟨8227039619993744724551099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 87755089279933277061878389 8227039619993744724551099)
          ·
            refine ⟨12340559429990617086826649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8227039619993744724551099 12340559429990617086826649)
            ·
              refine ⟨9255419572492962815119987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12340559429990617086826649 9255419572492962815119987)
              ·
                refine ⟨13883129358739444222679981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9255419572492962815119987 13883129358739444222679981)
                ·
                  refine ⟨5206173509527291583504993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13883129358739444222679981 5206173509527291583504993)
                  ·
                    refine ⟨3904630132145468687628745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5206173509527291583504993 3904630132145468687628745)
                    ·
                      refine ⟨2928472599109101515721559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3904630132145468687628745 2928472599109101515721559)
                      ·
                        rfl

theorem cell23_5703180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 1, 3, 2, 2].length) (baseStart_5703180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5703180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5703180 prefixEnd_5703180 := by exact prefixLift 5703180
  have htrace : WordTrace (prefixWord ++ tailWord_5703180) baseStart_5703180 baseEnd_5703180 := by
    simpa [prefixWord, tailWord_5703180, baseEnd_5703180] using wordTrace_append hprefix tailTrace_5703180
  have hstable : (prefixWord ++ tailWord_5703180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5703180).length < 2 ^ (prefixWord ++ tailWord_5703180).sum := by decide
  have hdescent : baseEnd_5703180 < baseStart_5703180 := by decide
  rcases family_descends (prefixWord ++ tailWord_5703180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5703203 : List Nat := [1, 1, 1, 4, 6, 1, 2, 7]
def baseStart_5703203 : Nat := 118140960795 + 5703203 * 2 ^ 59
def prefixEnd_5703203 : Nat := 4983230072969 + 3 ^ 40 * 5703203 * 2
def baseEnd_5703203 : Nat := 108462385524598330582739

theorem tailTrace_5703203 : CollatzResearch.WordTrace tailWord_5703203 prefixEnd_5703203 108462385524598330582739 := by
  unfold tailWord_5703203
  simp only [CollatzResearch.WordTrace]
  refine ⟨208012902357277035371058263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138675268238184690247372175 208012902357277035371058263)
  ·
    refine ⟨312019353535915553056587395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208012902357277035371058263 312019353535915553056587395)
    ·
      refine ⟨468029030303873329584881093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312019353535915553056587395 468029030303873329584881093)
      ·
        refine ⟨87755443181976249297165205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 468029030303873329584881093 87755443181976249297165205)
        ·
          refine ⟨4113536399155136685804619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 87755443181976249297165205 4113536399155136685804619)
          ·
            refine ⟨6170304598732705028706929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4113536399155136685804619 6170304598732705028706929)
            ·
              refine ⟨4627728449049528771530197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6170304598732705028706929 4627728449049528771530197)
              ·
                refine ⟨108462385524598330582739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4627728449049528771530197 108462385524598330582739)
                ·
                  rfl

theorem cell23_5703203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 2, 7].length) (baseStart_5703203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5703203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5703203 prefixEnd_5703203 := by exact prefixLift 5703203
  have htrace : WordTrace (prefixWord ++ tailWord_5703203) baseStart_5703203 baseEnd_5703203 := by
    simpa [prefixWord, tailWord_5703203, baseEnd_5703203] using wordTrace_append hprefix tailTrace_5703203
  have hstable : (prefixWord ++ tailWord_5703203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5703203).length < 2 ^ (prefixWord ++ tailWord_5703203).sum := by decide
  have hdescent : baseEnd_5703203 < baseStart_5703203 := by decide
  rcases family_descends (prefixWord ++ tailWord_5703203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5703214 : List Nat := [4, 1, 3, 1, 2, 3, 1, 3, 1, 2, 2]
def baseStart_5703214 : Nat := 118140960795 + 5703214 * 2 ^ 59
def prefixEnd_5703214 : Nat := 4983230072969 + 3 ^ 40 * 5703214 * 2
def baseEnd_5703214 : Nat := 2928490057451354382696403

theorem tailTrace_5703214 : CollatzResearch.WordTrace tailWord_5703214 prefixEnd_5703214 2928490057451354382696403 := by
  unfold tailWord_5703214
  simp only [CollatzResearch.WordTrace]
  refine ⟨26001662945029648031213587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138675535706824789499805797 26001662945029648031213587)
  ·
    refine ⟨39002494417544472046820381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26001662945029648031213587 39002494417544472046820381)
    ·
      refine ⟨14625935406579177017557643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39002494417544472046820381 14625935406579177017557643)
      ·
        refine ⟨21938903109868765526336465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14625935406579177017557643 21938903109868765526336465)
        ·
          refine ⟨16454177332401574144752349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21938903109868765526336465 16454177332401574144752349)
          ·
            refine ⟨6170316499650590304282131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16454177332401574144752349 6170316499650590304282131)
            ·
              refine ⟨9255474749475885456423197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6170316499650590304282131 9255474749475885456423197)
              ·
                refine ⟨3470803031053457046158699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9255474749475885456423197 3470803031053457046158699)
                ·
                  refine ⟨5206204546580185569238049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3470803031053457046158699 5206204546580185569238049)
                  ·
                    refine ⟨3904653409935139176928537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5206204546580185569238049 3904653409935139176928537)
                    ·
                      refine ⟨2928490057451354382696403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3904653409935139176928537 2928490057451354382696403)
                      ·
                        rfl

theorem cell23_5703214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 3, 1, 2, 2].length) (baseStart_5703214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5703214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5703214 prefixEnd_5703214 := by exact prefixLift 5703214
  have htrace : WordTrace (prefixWord ++ tailWord_5703214) baseStart_5703214 baseEnd_5703214 := by
    simpa [prefixWord, tailWord_5703214, baseEnd_5703214] using wordTrace_append hprefix tailTrace_5703214
  have hstable : (prefixWord ++ tailWord_5703214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5703214).length < 2 ^ (prefixWord ++ tailWord_5703214).sum := by decide
  have hdescent : baseEnd_5703214 < baseStart_5703214 := by decide
  rcases family_descends (prefixWord ++ tailWord_5703214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5703223 : List Nat := [1, 1, 3, 1, 2, 4, 2, 3, 1, 3, 2]
def baseStart_5703223 : Nat := 118140960795 + 5703223 * 2 ^ 59
def prefixEnd_5703223 : Nat := 4983230072969 + 3 ^ 40 * 5703223 * 2
def baseEnd_5703223 : Nat := 2928494678777244847483861

theorem tailTrace_5703223 : CollatzResearch.WordTrace tailWord_5703223 prefixEnd_5703223 2928494678777244847483861 := by
  unfold tailWord_5703223
  simp only [CollatzResearch.WordTrace]
  refine ⟨208013631817204578786786323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138675754544803052524524215 208013631817204578786786323)
  ·
    refine ⟨312020447725806868180179485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208013631817204578786786323 312020447725806868180179485)
    ·
      refine ⟨117007667897177575567567307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 312020447725806868180179485 117007667897177575567567307)
      ·
        refine ⟨175511501845766363351350961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117007667897177575567567307 175511501845766363351350961)
        ·
          refine ⟨131633626384324772513513221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175511501845766363351350961 131633626384324772513513221)
          ·
            refine ⟨24681304947060894846283729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 131633626384324772513513221 24681304947060894846283729)
            ·
              refine ⟨18510978710295671134712797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24681304947060894846283729 18510978710295671134712797)
              ·
                refine ⟨6941617016360876675517299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18510978710295671134712797 6941617016360876675517299)
                ·
                  refine ⟨10412425524541315013275949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6941617016360876675517299 10412425524541315013275949)
                  ·
                    refine ⟨3904659571702993129978481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10412425524541315013275949 3904659571702993129978481)
                    ·
                      refine ⟨2928494678777244847483861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3904659571702993129978481 2928494678777244847483861)
                      ·
                        rfl

theorem cell23_5703223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 3, 1, 3, 2].length) (baseStart_5703223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5703223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5703223 prefixEnd_5703223 := by exact prefixLift 5703223
  have htrace : WordTrace (prefixWord ++ tailWord_5703223) baseStart_5703223 baseEnd_5703223 := by
    simpa [prefixWord, tailWord_5703223, baseEnd_5703223] using wordTrace_append hprefix tailTrace_5703223
  have hstable : (prefixWord ++ tailWord_5703223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5703223).length < 2 ^ (prefixWord ++ tailWord_5703223).sum := by decide
  have hdescent : baseEnd_5703223 < baseStart_5703223 := by decide
  rcases family_descends (prefixWord ++ tailWord_5703223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5703249 : List Nat := [1, 2, 2, 1, 3, 2, 2, 1, 1, 4, 4]
def baseStart_5703249 : Nat := 118140960795 + 5703249 * 2 ^ 59
def prefixEnd_5703249 : Nat := 4983230072969 + 3 ^ 40 * 5703249 * 2
def baseEnd_5703249 : Nat := 2928508029274261745758741

theorem tailTrace_5703249 : CollatzResearch.WordTrace tailWord_5703249 prefixEnd_5703249 2928508029274261745758741 := by
  unfold tailWord_5703249
  simp only [CollatzResearch.WordTrace]
  refine ⟨208014580115110385227232801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138676386743406923484821867 208014580115110385227232801)
  ·
    refine ⟨156010935086332788920424601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208014580115110385227232801 156010935086332788920424601)
    ·
      refine ⟨117008201314749591690318451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156010935086332788920424601 117008201314749591690318451)
      ·
        refine ⟨175512301972124387535477677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117008201314749591690318451 175512301972124387535477677)
        ·
          refine ⟨65817113239546645325804129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 175512301972124387535477677 65817113239546645325804129)
          ·
            refine ⟨49362834929659983994353097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65817113239546645325804129 49362834929659983994353097)
            ·
              refine ⟨37022126197244987995764823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49362834929659983994353097 37022126197244987995764823)
              ·
                refine ⟨55533189295867481993647235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37022126197244987995764823 55533189295867481993647235)
                ·
                  refine ⟨83299783943801222990470853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55533189295867481993647235 83299783943801222990470853)
                  ·
                    refine ⟨15618709489462729310713285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 83299783943801222990470853 15618709489462729310713285)
                    ·
                      refine ⟨2928508029274261745758741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15618709489462729310713285 2928508029274261745758741)
                      ·
                        rfl

theorem cell23_5703249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 1, 1, 4, 4].length) (baseStart_5703249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5703249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5703249 prefixEnd_5703249 := by exact prefixLift 5703249
  have htrace : WordTrace (prefixWord ++ tailWord_5703249) baseStart_5703249 baseEnd_5703249 := by
    simpa [prefixWord, tailWord_5703249, baseEnd_5703249] using wordTrace_append hprefix tailTrace_5703249
  have hstable : (prefixWord ++ tailWord_5703249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5703249).length < 2 ^ (prefixWord ++ tailWord_5703249).sum := by decide
  have hdescent : baseEnd_5703249 < baseStart_5703249 := by decide
  rcases family_descends (prefixWord ++ tailWord_5703249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5703276 : List Nat := [2, 2, 1, 1, 3, 1, 1, 7, 5]
def baseStart_5703276 : Nat := 118140960795 + 5703276 * 2 ^ 59
def prefixEnd_5703276 : Nat := 4983230072969 + 3 ^ 40 * 5703276 * 2
def baseEnd_5703276 : Nat := 325391321472437015569013

theorem tailTrace_5703276 : CollatzResearch.WordTrace tailWord_5703276 prefixEnd_5703276 325391321472437015569013 := by
  unfold tailWord_5703276
  simp only [CollatzResearch.WordTrace]
  refine ⟨104007782443006284419232841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138677043257341712558977121 104007782443006284419232841)
  ·
    refine ⟨78005836832254713314424631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104007782443006284419232841 78005836832254713314424631)
    ·
      refine ⟨117008755248382069971636947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78005836832254713314424631 117008755248382069971636947)
      ·
        refine ⟨175513132872573104957455421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117008755248382069971636947 175513132872573104957455421)
        ·
          refine ⟨65817424827214914359045783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 175513132872573104957455421 65817424827214914359045783)
          ·
            refine ⟨98726137240822371538568675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65817424827214914359045783 98726137240822371538568675)
            ·
              refine ⟨148089205861233557307853013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98726137240822371538568675 148089205861233557307853013)
              ·
                refine ⟨3470840762372661499402805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 148089205861233557307853013 3470840762372661499402805)
                ·
                  refine ⟨325391321472437015569013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3470840762372661499402805 325391321472437015569013)
                  ·
                    rfl

theorem cell23_5703276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 7, 5].length) (baseStart_5703276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5703276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5703276 prefixEnd_5703276 := by exact prefixLift 5703276
  have htrace : WordTrace (prefixWord ++ tailWord_5703276) baseStart_5703276 baseEnd_5703276 := by
    simpa [prefixWord, tailWord_5703276, baseEnd_5703276] using wordTrace_append hprefix tailTrace_5703276
  have hstable : (prefixWord ++ tailWord_5703276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5703276).length < 2 ^ (prefixWord ++ tailWord_5703276).sum := by decide
  have hdescent : baseEnd_5703276 < baseStart_5703276 := by decide
  rcases family_descends (prefixWord ++ tailWord_5703276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5703293 : List Nat := [1, 4, 1, 1, 4, 2, 1, 4, 5]
def baseStart_5703293 : Nat := 118140960795 + 5703293 * 2 ^ 59
def prefixEnd_5703293 : Nat := 4983230072969 + 3 ^ 40 * 5703293 * 2
def baseEnd_5703293 : Nat := 325392291380339952623171

theorem tailTrace_5703293 : CollatzResearch.WordTrace tailWord_5703293 prefixEnd_5703293 325392291380339952623171 := by
  unfold tailWord_5703293
  simp only [CollatzResearch.WordTrace]
  refine ⟨208016184926950980741834533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138677456617967320494556355 208016184926950980741834533)
  ·
    refine ⟨39003034673803308889093975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 208016184926950980741834533 39003034673803308889093975)
    ·
      refine ⟨58504552010704963333640963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39003034673803308889093975 58504552010704963333640963)
      ·
        refine ⟨87756828016057445000461445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58504552010704963333640963 87756828016057445000461445)
        ·
          refine ⟨16454405253010770937586521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87756828016057445000461445 16454405253010770937586521)
          ·
            refine ⟨12340803939758078203189891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16454405253010770937586521 12340803939758078203189891)
            ·
              refine ⟨18511205909637117304784837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12340803939758078203189891 18511205909637117304784837)
              ·
                refine ⟨3470851108056959494647157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18511205909637117304784837 3470851108056959494647157)
                ·
                  refine ⟨325392291380339952623171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3470851108056959494647157 325392291380339952623171)
                  ·
                    rfl

theorem cell23_5703293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 4, 5].length) (baseStart_5703293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5703293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5703293 prefixEnd_5703293 := by exact prefixLift 5703293
  have htrace : WordTrace (prefixWord ++ tailWord_5703293) baseStart_5703293 baseEnd_5703293 := by
    simpa [prefixWord, tailWord_5703293, baseEnd_5703293] using wordTrace_append hprefix tailTrace_5703293
  have hstable : (prefixWord ++ tailWord_5703293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5703293).length < 2 ^ (prefixWord ++ tailWord_5703293).sum := by decide
  have hdescent : baseEnd_5703293 < baseStart_5703293 := by decide
  rcases family_descends (prefixWord ++ tailWord_5703293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5703296 : List Nat := [2, 1, 1, 2, 1, 4, 1, 1, 1, 7, 2]
def baseStart_5703296 : Nat := 118140960795 + 5703296 * 2 ^ 59
def prefixEnd_5703296 : Nat := 4983230072969 + 3 ^ 40 * 5703296 * 2
def baseEnd_5703296 : Nat := 2928532162865023061871025

theorem tailTrace_5703296 : CollatzResearch.WordTrace tailWord_5703296 prefixEnd_5703296 2928532162865023061871025 := by
  unfold tailWord_5703296
  simp only [CollatzResearch.WordTrace]
  refine ⟨104008147172970056127096871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138677529563960074836129161 104008147172970056127096871)
  ·
    refine ⟨156012220759455084190645307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104008147172970056127096871 156012220759455084190645307)
    ·
      refine ⟨234018331139182626285967961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156012220759455084190645307 234018331139182626285967961)
      ·
        refine ⟨175513748354386969714475971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 234018331139182626285967961 175513748354386969714475971)
        ·
          refine ⟨263270622531580454571713957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175513748354386969714475971 263270622531580454571713957)
          ·
            refine ⟨49363241724671335232196367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 263270622531580454571713957 49363241724671335232196367)
            ·
              refine ⟨74044862587007002848294551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49363241724671335232196367 74044862587007002848294551)
              ·
                refine ⟨111067293880510504272441827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74044862587007002848294551 111067293880510504272441827)
                ·
                  refine ⟨166600940820765756408662741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 111067293880510504272441827 166600940820765756408662741)
                  ·
                    refine ⟨3904709550486697415828033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 166600940820765756408662741 3904709550486697415828033)
                    ·
                      refine ⟨2928532162865023061871025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3904709550486697415828033 2928532162865023061871025)
                      ·
                        rfl

theorem cell23_5703296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 1, 7, 2].length) (baseStart_5703296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5703296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5703296 prefixEnd_5703296 := by exact prefixLift 5703296
  have htrace : WordTrace (prefixWord ++ tailWord_5703296) baseStart_5703296 baseEnd_5703296 := by
    simpa [prefixWord, tailWord_5703296, baseEnd_5703296] using wordTrace_append hprefix tailTrace_5703296
  have hstable : (prefixWord ++ tailWord_5703296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5703296).length < 2 ^ (prefixWord ++ tailWord_5703296).sum := by decide
  have hdescent : baseEnd_5703296 < baseStart_5703296 := by decide
  rcases family_descends (prefixWord ++ tailWord_5703296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5703403 : List Nat := [1, 1, 1, 1, 2, 4, 3, 1, 4, 3, 2]
def baseStart_5703403 : Nat := 118140960795 + 5703403 * 2 ^ 59
def prefixEnd_5703403 : Nat := 4983230072969 + 3 ^ 40 * 5703403 * 2
def baseEnd_5703403 : Nat := 2928587105295054143233033

theorem tailTrace_5703403 : CollatzResearch.WordTrace tailWord_5703403 prefixEnd_5703403 2928587105295054143233033 := by
  unfold tailWord_5703403
  simp only [CollatzResearch.WordTrace]
  refine ⟨208020196956552469528338863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138680131304368313018892575 208020196956552469528338863)
  ·
    refine ⟨312030295434828704292508295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208020196956552469528338863 312030295434828704292508295)
    ·
      refine ⟨468045443152243056438762443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312030295434828704292508295 468045443152243056438762443)
      ·
        refine ⟨702068164728364584658143665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 468045443152243056438762443 702068164728364584658143665)
        ·
          refine ⟨526551123546273438493607749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 702068164728364584658143665 526551123546273438493607749)
          ·
            refine ⟨98728335664926269717551453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 526551123546273438493607749 98728335664926269717551453)
            ·
              refine ⟨37023125874347351144081795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 98728335664926269717551453 37023125874347351144081795)
              ·
                refine ⟨55534688811521026716122693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37023125874347351144081795 55534688811521026716122693)
                ·
                  refine ⟨10412754152160192509273005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55534688811521026716122693 10412754152160192509273005)
                  ·
                    refine ⟨3904782807060072190977377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10412754152160192509273005 3904782807060072190977377)
                    ·
                      refine ⟨2928587105295054143233033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3904782807060072190977377 2928587105295054143233033)
                      ·
                        rfl

theorem cell23_5703403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 1, 4, 3, 2].length) (baseStart_5703403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5703403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5703403 prefixEnd_5703403 := by exact prefixLift 5703403
  have htrace : WordTrace (prefixWord ++ tailWord_5703403) baseStart_5703403 baseEnd_5703403 := by
    simpa [prefixWord, tailWord_5703403, baseEnd_5703403] using wordTrace_append hprefix tailTrace_5703403
  have hstable : (prefixWord ++ tailWord_5703403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5703403).length < 2 ^ (prefixWord ++ tailWord_5703403).sum := by decide
  have hdescent : baseEnd_5703403 < baseStart_5703403 := by decide
  rcases family_descends (prefixWord ++ tailWord_5703403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5703436 : List Nat := [2, 2, 1, 2, 2, 1, 2, 2, 3, 1, 5]
def baseStart_5703436 : Nat := 118140960795 + 5703436 * 2 ^ 59
def prefixEnd_5703436 : Nat := 4983230072969 + 3 ^ 40 * 5703436 * 2
def baseEnd_5703436 : Nat := 2928604050156652514120381

theorem tailTrace_5703436 : CollatzResearch.WordTrace tailWord_5703436 prefixEnd_5703436 2928604050156652514120381 := by
  unfold tailWord_5703436
  simp only [CollatzResearch.WordTrace]
  refine ⟨104010700282716458082145081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138680933710288610776193441 104010700282716458082145081)
  ·
    refine ⟨78008025212037343561608811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104010700282716458082145081 78008025212037343561608811)
    ·
      refine ⟨117012037818056015342413217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78008025212037343561608811 117012037818056015342413217)
      ·
        refine ⟨87759028363542011506809913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117012037818056015342413217 87759028363542011506809913)
        ·
          refine ⟨65819271272656508630107435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87759028363542011506809913 65819271272656508630107435)
          ·
            refine ⟨98728906908984762945161153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65819271272656508630107435 98728906908984762945161153)
            ·
              refine ⟨74046680181738572208870865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98728906908984762945161153 74046680181738572208870865)
              ·
                refine ⟨55535010136303929156653149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74046680181738572208870865 55535010136303929156653149)
                ·
                  refine ⟨20825628801113973433744931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55535010136303929156653149 20825628801113973433744931)
                  ·
                    refine ⟨31238443201670960150617397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20825628801113973433744931 31238443201670960150617397)
                    ·
                      refine ⟨2928604050156652514120381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31238443201670960150617397 2928604050156652514120381)
                      ·
                        rfl

theorem cell23_5703436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 2, 3, 1, 5].length) (baseStart_5703436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5703436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5703436 prefixEnd_5703436 := by exact prefixLift 5703436
  have htrace : WordTrace (prefixWord ++ tailWord_5703436) baseStart_5703436 baseEnd_5703436 := by
    simpa [prefixWord, tailWord_5703436, baseEnd_5703436] using wordTrace_append hprefix tailTrace_5703436
  have hstable : (prefixWord ++ tailWord_5703436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5703436).length < 2 ^ (prefixWord ++ tailWord_5703436).sum := by decide
  have hdescent : baseEnd_5703436 < baseStart_5703436 := by decide
  rcases family_descends (prefixWord ++ tailWord_5703436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5703460 : List Nat := [2, 3, 1, 3, 2, 1, 1, 4, 2, 4]
def baseStart_5703460 : Nat := 118140960795 + 5703460 * 2 ^ 59
def prefixEnd_5703460 : Nat := 4983230072969 + 3 ^ 40 * 5703460 * 2
def baseEnd_5703460 : Nat := 976205457897453473406757

theorem tailTrace_5703460 : CollatzResearch.WordTrace tailWord_5703460 prefixEnd_5703460 976205457897453473406757 := by
  unfold tailWord_5703460
  simp only [CollatzResearch.WordTrace]
  refine ⟨104011137958672984131581917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138681517278230645508775889 104011137958672984131581917)
  ·
    refine ⟨39004176734502369049343219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104011137958672984131581917 39004176734502369049343219)
    ·
      refine ⟨58506265101753553574014829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39004176734502369049343219 58506265101753553574014829)
      ·
        refine ⟨21939849413157582590255561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58506265101753553574014829 21939849413157582590255561)
        ·
          refine ⟨16454887059868186942691671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21939849413157582590255561 16454887059868186942691671)
          ·
            refine ⟨24682330589802280414037507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16454887059868186942691671 24682330589802280414037507)
            ·
              refine ⟨37023495884703420621056261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24682330589802280414037507 37023495884703420621056261)
              ·
                refine ⟨6941905478381891366448049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37023495884703420621056261 6941905478381891366448049)
                ·
                  refine ⟨5206429108786418524836037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6941905478381891366448049 5206429108786418524836037)
                  ·
                    refine ⟨976205457897453473406757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5206429108786418524836037 976205457897453473406757)
                    ·
                      rfl

theorem cell23_5703460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 4, 2, 4].length) (baseStart_5703460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5703460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5703460 prefixEnd_5703460 := by exact prefixLift 5703460
  have htrace : WordTrace (prefixWord ++ tailWord_5703460) baseStart_5703460 baseEnd_5703460 := by
    simpa [prefixWord, tailWord_5703460, baseEnd_5703460] using wordTrace_append hprefix tailTrace_5703460
  have hstable : (prefixWord ++ tailWord_5703460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5703460).length < 2 ^ (prefixWord ++ tailWord_5703460).sum := by decide
  have hdescent : baseEnd_5703460 < baseStart_5703460 := by decide
  rcases family_descends (prefixWord ++ tailWord_5703460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5703473 : List Nat := [1, 2, 2, 3, 2, 4, 1, 8]
def baseStart_5703473 : Nat := 118140960795 + 5703473 * 2 ^ 59
def prefixEnd_5703473 : Nat := 4983230072969 + 3 ^ 40 * 5703473 * 2
def baseEnd_5703473 : Nat := 108467520331143291457693

theorem tailTrace_5703473 : CollatzResearch.WordTrace tailWord_5703473 prefixEnd_5703473 108467520331143291457693 := by
  unfold tailWord_5703473
  simp only [CollatzResearch.WordTrace]
  refine ⟨208022750066298871483387073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138681833377532580988924715 208022750066298871483387073)
  ·
    refine ⟨156017062549724153612540305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208022750066298871483387073 156017062549724153612540305)
    ·
      refine ⟨117012796912293115209405229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156017062549724153612540305 117012796912293115209405229)
      ·
        refine ⟨43879798842109918203526961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117012796912293115209405229 43879798842109918203526961)
        ·
          refine ⟨32909849131582438652645221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43879798842109918203526961 32909849131582438652645221)
          ·
            refine ⟨6170596712171707247370979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32909849131582438652645221 6170596712171707247370979)
            ·
              refine ⟨9255895068257560871056469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6170596712171707247370979 9255895068257560871056469)
              ·
                refine ⟨108467520331143291457693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9255895068257560871056469 108467520331143291457693)
                ·
                  rfl

theorem cell23_5703473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 8].length) (baseStart_5703473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5703473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5703473 prefixEnd_5703473 := by exact prefixLift 5703473
  have htrace : WordTrace (prefixWord ++ tailWord_5703473) baseStart_5703473 baseEnd_5703473 := by
    simpa [prefixWord, tailWord_5703473, baseEnd_5703473] using wordTrace_append hprefix tailTrace_5703473
  have hstable : (prefixWord ++ tailWord_5703473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5703473).length < 2 ^ (prefixWord ++ tailWord_5703473).sum := by decide
  have hdescent : baseEnd_5703473 < baseStart_5703473 := by decide
  rcases family_descends (prefixWord ++ tailWord_5703473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5703501 : List Nat := [1, 6, 1, 2, 1, 1, 1, 5, 1, 2, 2]
def baseStart_5703501 : Nat := 118140960795 + 5703501 * 2 ^ 59
def prefixEnd_5703501 : Nat := 4983230072969 + 3 ^ 40 * 5703501 * 2
def baseEnd_5703501 : Nat := 2928637426399194759807583

theorem tailTrace_5703501 : CollatzResearch.WordTrace tailWord_5703501 prefixEnd_5703501 2928637426399194759807583 := by
  unfold tailWord_5703501
  simp only [CollatzResearch.WordTrace]
  refine ⟨208023771310197432265406357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138682514206798288176937571 208023771310197432265406357)
  ·
    refine ⟨9751114280165504637440923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 208023771310197432265406357 9751114280165504637440923)
    ·
      refine ⟨14626671420248256956161385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9751114280165504637440923 14626671420248256956161385)
      ·
        refine ⟨10970003565186192717121039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14626671420248256956161385 10970003565186192717121039)
        ·
          refine ⟨16455005347779289075681559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10970003565186192717121039 16455005347779289075681559)
          ·
            refine ⟨24682508021668933613522339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16455005347779289075681559 24682508021668933613522339)
            ·
              refine ⟨37023762032503400420283509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24682508021668933613522339 37023762032503400420283509)
              ·
                refine ⟨3470977690547193789401579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37023762032503400420283509 3470977690547193789401579)
                ·
                  refine ⟨5206466535820790684102369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3470977690547193789401579 5206466535820790684102369)
                  ·
                    refine ⟨3904849901865593013076777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5206466535820790684102369 3904849901865593013076777)
                    ·
                      refine ⟨2928637426399194759807583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3904849901865593013076777 2928637426399194759807583)
                      ·
                        rfl

theorem cell23_5703501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 5, 1, 2, 2].length) (baseStart_5703501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5703501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5703501 prefixEnd_5703501 := by exact prefixLift 5703501
  have htrace : WordTrace (prefixWord ++ tailWord_5703501) baseStart_5703501 baseEnd_5703501 := by
    simpa [prefixWord, tailWord_5703501, baseEnd_5703501] using wordTrace_append hprefix tailTrace_5703501
  have hstable : (prefixWord ++ tailWord_5703501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5703501).length < 2 ^ (prefixWord ++ tailWord_5703501).sum := by decide
  have hdescent : baseEnd_5703501 < baseStart_5703501 := by decide
  rcases family_descends (prefixWord ++ tailWord_5703501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5703533 : List Nat := [1, 5, 1, 1, 1, 1, 4, 1, 2, 6]
def baseStart_5703533 : Nat := 118140960795 + 5703533 * 2 ^ 59
def prefixEnd_5703533 : Nat := 4983230072969 + 3 ^ 40 * 5703533 * 2
def baseEnd_5703533 : Nat := 976217952593379544869145

theorem tailTrace_5703533 : CollatzResearch.WordTrace tailWord_5703533 prefixEnd_5703533 976217952593379544869145 := by
  unfold tailWord_5703533
  simp only [CollatzResearch.WordTrace]
  refine ⟨208024938446081501730571253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138683292297387667820380835 208024938446081501730571253)
  ·
    refine ⟨19502337979320140787241055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 208024938446081501730571253 19502337979320140787241055)
    ·
      refine ⟨29253506968980211180861583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19502337979320140787241055 29253506968980211180861583)
      ·
        refine ⟨43880260453470316771292375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29253506968980211180861583 43880260453470316771292375)
        ·
          refine ⟨65820390680205475156938563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43880260453470316771292375 65820390680205475156938563)
          ·
            refine ⟨98730586020308212735407845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65820390680205475156938563 98730586020308212735407845)
            ·
              refine ⟨18511984878807789887888971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 98730586020308212735407845 18511984878807789887888971)
              ·
                refine ⟨27767977318211684831833457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18511984878807789887888971 27767977318211684831833457)
                ·
                  refine ⟨20825982988658763623875093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27767977318211684831833457 20825982988658763623875093)
                  ·
                    refine ⟨976217952593379544869145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20825982988658763623875093 976217952593379544869145)
                    ·
                      rfl

theorem cell23_5703533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 1, 2, 6].length) (baseStart_5703533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5703533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5703533 prefixEnd_5703533 := by exact prefixLift 5703533
  have htrace : WordTrace (prefixWord ++ tailWord_5703533) baseStart_5703533 baseEnd_5703533 := by
    simpa [prefixWord, tailWord_5703533, baseEnd_5703533] using wordTrace_append hprefix tailTrace_5703533
  have hstable : (prefixWord ++ tailWord_5703533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5703533).length < 2 ^ (prefixWord ++ tailWord_5703533).sum := by decide
  have hdescent : baseEnd_5703533 < baseStart_5703533 := by decide
  rcases family_descends (prefixWord ++ tailWord_5703533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5703560 : List Nat := [2, 1, 3, 3, 3, 1, 1, 1, 2, 1, 5]
def baseStart_5703560 : Nat := 118140960795 + 5703560 * 2 ^ 59
def prefixEnd_5703560 : Nat := 4983230072969 + 3 ^ 40 * 5703560 * 2
def baseEnd_5703560 : Nat := 2928667721757810028969811

theorem tailTrace_5703560 : CollatzResearch.WordTrace tailWord_5703560 prefixEnd_5703560 2928667721757810028969811 := by
  unfold tailWord_5703560
  simp only [CollatzResearch.WordTrace]
  refine ⟨104012961608491842670902067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138683948811322456894536089 104012961608491842670902067)
  ·
    refine ⟨156019442412737764006353101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104012961608491842670902067 156019442412737764006353101)
    ·
      refine ⟨58507290904776661502382413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156019442412737764006353101 58507290904776661502382413)
      ·
        refine ⟨21940234089291248063393405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58507290904776661502382413 21940234089291248063393405)
        ·
          refine ⟨8227587783484218023772527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21940234089291248063393405 8227587783484218023772527)
          ·
            refine ⟨12341381675226327035658791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8227587783484218023772527 12341381675226327035658791)
            ·
              refine ⟨18512072512839490553488187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12341381675226327035658791 18512072512839490553488187)
              ·
                refine ⟨27768108769259235830232281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18512072512839490553488187 27768108769259235830232281)
                ·
                  refine ⟨20826081576944426872674211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27768108769259235830232281 20826081576944426872674211)
                  ·
                    refine ⟨31239122365416640309011317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20826081576944426872674211 31239122365416640309011317)
                    ·
                      refine ⟨2928667721757810028969811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31239122365416640309011317 2928667721757810028969811)
                      ·
                        rfl

theorem cell23_5703560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 1, 2, 1, 5].length) (baseStart_5703560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5703560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5703560 prefixEnd_5703560 := by exact prefixLift 5703560
  have htrace : WordTrace (prefixWord ++ tailWord_5703560) baseStart_5703560 baseEnd_5703560 := by
    simpa [prefixWord, tailWord_5703560, baseEnd_5703560] using wordTrace_append hprefix tailTrace_5703560
  have hstable : (prefixWord ++ tailWord_5703560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5703560).length < 2 ^ (prefixWord ++ tailWord_5703560).sum := by decide
  have hdescent : baseEnd_5703560 < baseStart_5703560 := by decide
  rcases family_descends (prefixWord ++ tailWord_5703560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5703580 : List Nat := [2, 2, 3, 3, 1, 1, 3, 1, 7]
def baseStart_5703580 : Nat := 118140960795 + 5703580 * 2 ^ 59
def prefixEnd_5703580 : Nat := 4983230072969 + 3 ^ 40 * 5703580 * 2
def baseEnd_5703580 : Nat := 325408665707877772302191

theorem tailTrace_5703580 : CollatzResearch.WordTrace tailWord_5703580 prefixEnd_5703580 325408665707877772302191 := by
  unfold tailWord_5703580
  simp only [CollatzResearch.WordTrace]
  refine ⟨104013326338455614378766097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138684435117940819171688129 104013326338455614378766097)
  ·
    refine ⟨78009994753841710784074573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104013326338455614378766097 78009994753841710784074573)
    ·
      refine ⟨29253748032690641544027965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78009994753841710784074573 29253748032690641544027965)
      ·
        refine ⟨10970155512258990579010487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29253748032690641544027965 10970155512258990579010487)
        ·
          refine ⟨16455233268388485868515731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10970155512258990579010487 16455233268388485868515731)
          ·
            refine ⟨24682849902582728802773597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16455233268388485868515731 24682849902582728802773597)
            ·
              refine ⟨9256068713468523301040099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24682849902582728802773597 9256068713468523301040099)
              ·
                refine ⟨13884103070202784951560149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9256068713468523301040099 13884103070202784951560149)
                ·
                  refine ⟨325408665707877772302191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13884103070202784951560149 325408665707877772302191)
                  ·
                    rfl

theorem cell23_5703580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 1, 7].length) (baseStart_5703580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5703580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5703580 prefixEnd_5703580 := by exact prefixLift 5703580
  have htrace : WordTrace (prefixWord ++ tailWord_5703580) baseStart_5703580 baseEnd_5703580 := by
    simpa [prefixWord, tailWord_5703580, baseEnd_5703580] using wordTrace_append hprefix tailTrace_5703580
  have hstable : (prefixWord ++ tailWord_5703580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5703580).length < 2 ^ (prefixWord ++ tailWord_5703580).sum := by decide
  have hdescent : baseEnd_5703580 < baseStart_5703580 := by decide
  rcases family_descends (prefixWord ++ tailWord_5703580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5703591 : List Nat := [1, 1, 6, 1, 2, 1, 4, 1, 2, 2, 2]
def baseStart_5703591 : Nat := 118140960795 + 5703591 * 2 ^ 59
def prefixEnd_5703591 : Nat := 4983230072969 + 3 ^ 40 * 5703591 * 2
def baseEnd_5703591 : Nat := 2928683639658099407682169

theorem tailTrace_5703591 : CollatzResearch.WordTrace tailWord_5703591 prefixEnd_5703591 2928683639658099407682169 := by
  unfold tailWord_5703591
  simp only [CollatzResearch.WordTrace]
  refine ⟨208027053879871377636182627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138684702586580918424121751 208027053879871377636182627)
  ·
    refine ⟨312040580819807066454273941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208027053879871377636182627 312040580819807066454273941)
    ·
      refine ⟨14626902225928456240044091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 312040580819807066454273941 14626902225928456240044091)
      ·
        refine ⟨21940353338892684360066137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14626902225928456240044091 21940353338892684360066137)
        ·
          refine ⟨16455265004169513270049603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21940353338892684360066137 16455265004169513270049603)
          ·
            refine ⟨24682897506254269905074405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16455265004169513270049603 24682897506254269905074405)
            ·
              refine ⟨4628043282422675607201451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24682897506254269905074405 4628043282422675607201451)
              ·
                refine ⟨6942064923634013410802177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4628043282422675607201451 6942064923634013410802177)
                ·
                  refine ⟨5206548692725510058101633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6942064923634013410802177 5206548692725510058101633)
                  ·
                    refine ⟨3904911519544132543576225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5206548692725510058101633 3904911519544132543576225)
                    ·
                      refine ⟨2928683639658099407682169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3904911519544132543576225 2928683639658099407682169)
                      ·
                        rfl

theorem cell23_5703591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 4, 1, 2, 2, 2].length) (baseStart_5703591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5703591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5703591 prefixEnd_5703591 := by exact prefixLift 5703591
  have htrace : WordTrace (prefixWord ++ tailWord_5703591) baseStart_5703591 baseEnd_5703591 := by
    simpa [prefixWord, tailWord_5703591, baseEnd_5703591] using wordTrace_append hprefix tailTrace_5703591
  have hstable : (prefixWord ++ tailWord_5703591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5703591).length < 2 ^ (prefixWord ++ tailWord_5703591).sum := by decide
  have hdescent : baseEnd_5703591 < baseStart_5703591 := by decide
  rcases family_descends (prefixWord ++ tailWord_5703591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5703630 : List Nat := [4, 1, 1, 1, 2, 2, 1, 4, 2, 1, 4]
def baseStart_5703630 : Nat := 118140960795 + 5703630 * 2 ^ 59
def prefixEnd_5703630 : Nat := 4983230072969 + 3 ^ 40 * 5703630 * 2
def baseEnd_5703630 : Nat := 2928703665403624755094489

theorem tailTrace_5703630 : CollatzResearch.WordTrace tailWord_5703630 prefixEnd_5703630 2928703665403624755094489 := by
  unfold tailWord_5703630
  simp only [CollatzResearch.WordTrace]
  refine ⟨26003559540841260912106543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138685650884486724864568229 26003559540841260912106543)
  ·
    refine ⟨39005339311261891368159815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26003559540841260912106543 39005339311261891368159815)
    ·
      refine ⟨58508008966892837052239723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39005339311261891368159815 58508008966892837052239723)
      ·
        refine ⟨87762013450339255578359585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58508008966892837052239723 87762013450339255578359585)
        ·
          refine ⟨65821510087754441683769689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87762013450339255578359585 65821510087754441683769689)
          ·
            refine ⟨49366132565815831262827267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65821510087754441683769689 49366132565815831262827267)
            ·
              refine ⟨74049198848723746894240901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49366132565815831262827267 74049198848723746894240901)
              ·
                refine ⟨13884224784135702542670169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74049198848723746894240901 13884224784135702542670169)
                ·
                  refine ⟨10413168588101776907002627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13884224784135702542670169 10413168588101776907002627)
                  ·
                    refine ⟨15619752882152665360503941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10413168588101776907002627 15619752882152665360503941)
                    ·
                      refine ⟨2928703665403624755094489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15619752882152665360503941 2928703665403624755094489)
                      ·
                        rfl

theorem cell23_5703630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 4, 2, 1, 4].length) (baseStart_5703630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5703630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5703630 prefixEnd_5703630 := by exact prefixLift 5703630
  have htrace : WordTrace (prefixWord ++ tailWord_5703630) baseStart_5703630 baseEnd_5703630 := by
    simpa [prefixWord, tailWord_5703630, baseEnd_5703630] using wordTrace_append hprefix tailTrace_5703630
  have hstable : (prefixWord ++ tailWord_5703630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5703630).length < 2 ^ (prefixWord ++ tailWord_5703630).sum := by decide
  have hdescent : baseEnd_5703630 < baseStart_5703630 := by decide
  rcases family_descends (prefixWord ++ tailWord_5703630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5703640 : List Nat := [2, 1, 2, 2, 2, 2, 2, 3, 3, 4]
def baseStart_5703640 : Nat := 118140960795 + 5703640 * 2 ^ 59
def prefixEnd_5703640 : Nat := 4983230072969 + 3 ^ 40 * 5703640 * 2
def baseEnd_5703640 : Nat := 976236266736723238656481

theorem tailTrace_5703640 : CollatzResearch.WordTrace tailWord_5703640 prefixEnd_5703640 976236266736723238656481 := by
  unfold tailWord_5703640
  simp only [CollatzResearch.WordTrace]
  refine ⟨104014420528346929502358187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138685894037795906003144249 104014420528346929502358187)
  ·
    refine ⟨156021630792520394253537281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104014420528346929502358187 156021630792520394253537281)
    ·
      refine ⟨117016223094390295690152961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156021630792520394253537281 117016223094390295690152961)
      ·
        refine ⟨87762167320792721767614721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117016223094390295690152961 87762167320792721767614721)
        ·
          refine ⟨65821625490594541325711041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87762167320792721767614721 65821625490594541325711041)
          ·
            refine ⟨49366219117945905994283281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65821625490594541325711041 49366219117945905994283281)
            ·
              refine ⟨37024664338459429495712461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49366219117945905994283281 37024664338459429495712461)
              ·
                refine ⟨13884249126922286060892173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37024664338459429495712461 13884249126922286060892173)
                ·
                  refine ⟨5206593422595857272834565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13884249126922286060892173 5206593422595857272834565)
                  ·
                    refine ⟨976236266736723238656481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5206593422595857272834565 976236266736723238656481)
                    ·
                      rfl

theorem cell23_5703640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 3, 3, 4].length) (baseStart_5703640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5703640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5703640 prefixEnd_5703640 := by exact prefixLift 5703640
  have htrace : WordTrace (prefixWord ++ tailWord_5703640) baseStart_5703640 baseEnd_5703640 := by
    simpa [prefixWord, tailWord_5703640, baseEnd_5703640] using wordTrace_append hprefix tailTrace_5703640
  have hstable : (prefixWord ++ tailWord_5703640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5703640).length < 2 ^ (prefixWord ++ tailWord_5703640).sum := by decide
  have hdescent : baseEnd_5703640 < baseStart_5703640 := by decide
  rcases family_descends (prefixWord ++ tailWord_5703640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5703647 : List Nat := [1, 1, 2, 3, 4, 2, 1, 1, 2, 4, 2]
def baseStart_5703647 : Nat := 118140960795 + 5703647 * 2 ^ 59
def prefixEnd_5703647 : Nat := 4983230072969 + 3 ^ 40 * 5703647 * 2
def baseEnd_5703647 : Nat := 2928712394574751188581911

theorem tailTrace_5703647 : CollatzResearch.WordTrace tailWord_5703647 prefixEnd_5703647 2928712394574751188581911 := by
  unfold tailWord_5703647
  simp only [CollatzResearch.WordTrace]
  refine ⟨208029096367668499200221195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138686064245112332800147463 208029096367668499200221195)
  ·
    refine ⟨312043644551502748800331793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208029096367668499200221195 312043644551502748800331793)
    ·
      refine ⟨234032733413627061600248845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 312043644551502748800331793 234032733413627061600248845)
      ·
        refine ⟨87762275030110148100093317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 234032733413627061600248845 87762275030110148100093317)
        ·
          refine ⟨16455426568145652768767497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87762275030110148100093317 16455426568145652768767497)
          ·
            refine ⟨12341569926109239576575623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16455426568145652768767497 12341569926109239576575623)
            ·
              refine ⟨18512354889163859364863435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12341569926109239576575623 18512354889163859364863435)
              ·
                refine ⟨27768532333745789047295153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18512354889163859364863435 27768532333745789047295153)
                ·
                  refine ⟨20826399250309341785471365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27768532333745789047295153 20826399250309341785471365)
                  ·
                    refine ⟨3904949859433001584775881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20826399250309341785471365 3904949859433001584775881)
                    ·
                      refine ⟨2928712394574751188581911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3904949859433001584775881 2928712394574751188581911)
                      ·
                        rfl

theorem cell23_5703647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 1, 2, 4, 2].length) (baseStart_5703647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5703647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5703647 prefixEnd_5703647 := by exact prefixLift 5703647
  have htrace : WordTrace (prefixWord ++ tailWord_5703647) baseStart_5703647 baseEnd_5703647 := by
    simpa [prefixWord, tailWord_5703647, baseEnd_5703647] using wordTrace_append hprefix tailTrace_5703647
  have hstable : (prefixWord ++ tailWord_5703647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5703647).length < 2 ^ (prefixWord ++ tailWord_5703647).sum := by decide
  have hdescent : baseEnd_5703647 < baseStart_5703647 := by decide
  rcases family_descends (prefixWord ++ tailWord_5703647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5703661 : List Nat := [1, 5, 1, 4, 2, 1, 1, 1, 2, 5]
def baseStart_5703661 : Nat := 118140960795 + 5703661 * 2 ^ 59
def prefixEnd_5703661 : Nat := 4983230072969 + 3 ^ 40 * 5703661 * 2
def baseEnd_5703661 : Nat := 976239861101304711268949

theorem tailTrace_5703661 : CollatzResearch.WordTrace tailWord_5703661 prefixEnd_5703661 976239861101304711268949 := by
  unfold tailWord_5703661
  simp only [CollatzResearch.WordTrace]
  refine ⟨208029606989617779591230837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138686404659745186394153891 208029606989617779591230837)
  ·
    refine ⟨19502775655276666836677891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 208029606989617779591230837 19502775655276666836677891)
    ·
      refine ⟨29254163482915000255016837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19502775655276666836677891 29254163482915000255016837)
      ·
        refine ⟨5485155653046562547815657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29254163482915000255016837 5485155653046562547815657)
        ·
          refine ⟨4113866739784921910861743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5485155653046562547815657 4113866739784921910861743)
          ·
            refine ⟨6170800109677382866292615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4113866739784921910861743 6170800109677382866292615)
            ·
              refine ⟨9256200164516074299438923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6170800109677382866292615 9256200164516074299438923)
              ·
                refine ⟨13884300246774111449158385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9256200164516074299438923 13884300246774111449158385)
                ·
                  refine ⟨10413225185080583586868789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13884300246774111449158385 10413225185080583586868789)
                  ·
                    refine ⟨976239861101304711268949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10413225185080583586868789 976239861101304711268949)
                    ·
                      rfl

theorem cell23_5703661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 1, 2, 5].length) (baseStart_5703661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5703661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5703661 prefixEnd_5703661 := by exact prefixLift 5703661
  have htrace : WordTrace (prefixWord ++ tailWord_5703661) baseStart_5703661 baseEnd_5703661 := by
    simpa [prefixWord, tailWord_5703661, baseEnd_5703661] using wordTrace_append hprefix tailTrace_5703661
  have hstable : (prefixWord ++ tailWord_5703661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5703661).length < 2 ^ (prefixWord ++ tailWord_5703661).sum := by decide
  have hdescent : baseEnd_5703661 < baseStart_5703661 := by decide
  rcases family_descends (prefixWord ++ tailWord_5703661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5703687 : List Nat := [1, 1, 4, 3, 1, 4, 1, 2, 6]
def baseStart_5703687 : Nat := 118140960795 + 5703687 * 2 ^ 59
def prefixEnd_5703687 : Nat := 4983230072969 + 3 ^ 40 * 5703687 * 2
def baseEnd_5703687 : Nat := 325414770422325670231303

theorem tailTrace_5703687 : CollatzResearch.WordTrace tailWord_5703687 prefixEnd_5703687 325414770422325670231303 := by
  unfold tailWord_5703687
  simp only [CollatzResearch.WordTrace]
  refine ⟨208030555287523586031677315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138687036858349057354451543 208030555287523586031677315)
  ·
    refine ⟨312045832931285379047515973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208030555287523586031677315 312045832931285379047515973)
    ·
      refine ⟨58508593674616008571409245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 312045832931285379047515973 58508593674616008571409245)
      ·
        refine ⟨21940722627981003214278467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58508593674616008571409245 21940722627981003214278467)
        ·
          refine ⟨32911083941971504821417701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21940722627981003214278467 32911083941971504821417701)
          ·
            refine ⟨6170828239119657154015819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32911083941971504821417701 6170828239119657154015819)
            ·
              refine ⟨9256242358679485731023729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6170828239119657154015819 9256242358679485731023729)
              ·
                refine ⟨6942181769009614298267797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9256242358679485731023729 6942181769009614298267797)
                ·
                  refine ⟨325414770422325670231303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6942181769009614298267797 325414770422325670231303)
                  ·
                    rfl

theorem cell23_5703687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 2, 6].length) (baseStart_5703687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5703687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5703687 prefixEnd_5703687 := by exact prefixLift 5703687
  have htrace : WordTrace (prefixWord ++ tailWord_5703687) baseStart_5703687 baseEnd_5703687 := by
    simpa [prefixWord, tailWord_5703687, baseEnd_5703687] using wordTrace_append hprefix tailTrace_5703687
  have hstable : (prefixWord ++ tailWord_5703687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5703687).length < 2 ^ (prefixWord ++ tailWord_5703687).sum := by decide
  have hdescent : baseEnd_5703687 < baseStart_5703687 := by decide
  rcases family_descends (prefixWord ++ tailWord_5703687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5703717 : List Nat := [1, 3, 1, 2, 2, 4, 2, 2, 1, 5]
def baseStart_5703717 : Nat := 118140960795 + 5703717 * 2 ^ 59
def prefixEnd_5703717 : Nat := 4983230072969 + 3 ^ 40 * 5703717 * 2
def baseEnd_5703717 : Nat := 976249446073521971568863

theorem tailTrace_5703717 : CollatzResearch.WordTrace tailWord_5703717 prefixEnd_5703717 976249446073521971568863 := by
  unfold tailWord_5703717
  simp only [CollatzResearch.WordTrace]
  refine ⟨208031649477414901155269405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138687766318276600770179603 208031649477414901155269405)
  ·
    refine ⟨78011868554030587933226027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208031649477414901155269405 78011868554030587933226027)
    ·
      refine ⟨117017802831045881899839041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78011868554030587933226027 117017802831045881899839041)
      ·
        refine ⟨87763352123284411424879281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117017802831045881899839041 87763352123284411424879281)
        ·
          refine ⟨65822514092463308568659461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87763352123284411424879281 65822514092463308568659461)
          ·
            refine ⟨12341721392336870356623649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65822514092463308568659461 12341721392336870356623649)
            ·
              refine ⟨9256291044252652767467737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12341721392336870356623649 9256291044252652767467737)
              ·
                refine ⟨6942218283189489575600803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9256291044252652767467737 6942218283189489575600803)
                ·
                  refine ⟨10413327424784234363401205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6942218283189489575600803 10413327424784234363401205)
                  ·
                    refine ⟨976249446073521971568863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10413327424784234363401205 976249446073521971568863)
                    ·
                      rfl

theorem cell23_5703717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 2, 1, 5].length) (baseStart_5703717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5703717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5703717 prefixEnd_5703717 := by exact prefixLift 5703717
  have htrace : WordTrace (prefixWord ++ tailWord_5703717) baseStart_5703717 baseEnd_5703717 := by
    simpa [prefixWord, tailWord_5703717, baseEnd_5703717] using wordTrace_append hprefix tailTrace_5703717
  have hstable : (prefixWord ++ tailWord_5703717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5703717).length < 2 ^ (prefixWord ++ tailWord_5703717).sum := by decide
  have hdescent : baseEnd_5703717 < baseStart_5703717 := by decide
  rcases family_descends (prefixWord ++ tailWord_5703717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5703743 : List Nat := [1, 1, 2, 2, 3, 1, 13]
def baseStart_5703743 : Nat := 118140960795 + 5703743 * 2 ^ 59
def prefixEnd_5703743 : Nat := 4983230072969 + 3 ^ 40 * 5703743 * 2
def baseEnd_5703743 : Nat := 36157551712562750777549

theorem tailTrace_5703743 : CollatzResearch.WordTrace tailWord_5703743 prefixEnd_5703743 36157551712562750777549 := by
  unfold tailWord_5703743
  simp only [CollatzResearch.WordTrace]
  refine ⟨208032597775320707595715883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138688398516880471730477255 208032597775320707595715883)
  ·
    refine ⟨312048896662981061393573825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208032597775320707595715883 312048896662981061393573825)
    ·
      refine ⟨234036672497235796045180369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 312048896662981061393573825 234036672497235796045180369)
      ·
        refine ⟨175527504372926847033885277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 234036672497235796045180369 175527504372926847033885277)
        ·
          refine ⟨65822814139847567637706979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 175527504372926847033885277 65822814139847567637706979)
          ·
            refine ⟨98734221209771351456560469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65822814139847567637706979 98734221209771351456560469)
            ·
              refine ⟨36157551712562750777549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 98734221209771351456560469 36157551712562750777549)
              ·
                rfl

theorem cell23_5703743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 13].length) (baseStart_5703743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5703743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5703743 prefixEnd_5703743 := by exact prefixLift 5703743
  have htrace : WordTrace (prefixWord ++ tailWord_5703743) baseStart_5703743 baseEnd_5703743 := by
    simpa [prefixWord, tailWord_5703743, baseEnd_5703743] using wordTrace_append hprefix tailTrace_5703743
  have hstable : (prefixWord ++ tailWord_5703743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5703743).length < 2 ^ (prefixWord ++ tailWord_5703743).sum := by decide
  have hdescent : baseEnd_5703743 < baseStart_5703743 := by decide
  rcases family_descends (prefixWord ++ tailWord_5703743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5703757 : List Nat := [1, 6, 1, 1, 1, 1, 1, 4, 1, 1, 5]
def baseStart_5703757 : Nat := 118140960795 + 5703757 * 2 ^ 59
def prefixEnd_5703757 : Nat := 4983230072969 + 3 ^ 40 * 5703757 * 2
def baseEnd_5703757 : Nat := 2928768877446745758206405

theorem tailTrace_5703757 : CollatzResearch.WordTrace tailWord_5703757 prefixEnd_5703757 2928768877446745758206405 := by
  unfold tailWord_5703757
  simp only [CollatzResearch.WordTrace]
  refine ⟨208033108397269987986725525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138688738931513325324483683 208033108397269987986725525)
  ·
    refine ⟨9751551956122030686877759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 208033108397269987986725525 9751551956122030686877759)
    ·
      refine ⟨14627327934183046030316639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9751551956122030686877759 14627327934183046030316639)
      ·
        refine ⟨21940991901274569045474959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14627327934183046030316639 21940991901274569045474959)
        ·
          refine ⟨32911487851911853568212439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21940991901274569045474959 32911487851911853568212439)
          ·
            refine ⟨49367231777867780352318659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32911487851911853568212439 49367231777867780352318659)
            ·
              refine ⟨74050847666801670528477989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49367231777867780352318659 74050847666801670528477989)
              ·
                refine ⟨13884533937525313224089623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74050847666801670528477989 13884533937525313224089623)
                ·
                  refine ⟨20826800906287969836134435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13884533937525313224089623 20826800906287969836134435)
                  ·
                    refine ⟨31240201359431954754201653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20826800906287969836134435 31240201359431954754201653)
                    ·
                      refine ⟨2928768877446745758206405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31240201359431954754201653 2928768877446745758206405)
                      ·
                        rfl

theorem cell23_5703757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_5703757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5703757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5703757 prefixEnd_5703757 := by exact prefixLift 5703757
  have htrace : WordTrace (prefixWord ++ tailWord_5703757) baseStart_5703757 baseEnd_5703757 := by
    simpa [prefixWord, tailWord_5703757, baseEnd_5703757] using wordTrace_append hprefix tailTrace_5703757
  have hstable : (prefixWord ++ tailWord_5703757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5703757).length < 2 ^ (prefixWord ++ tailWord_5703757).sum := by decide
  have hdescent : baseEnd_5703757 < baseStart_5703757 := by decide
  rcases family_descends (prefixWord ++ tailWord_5703757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5703804 : List Nat := [2, 2, 2, 1, 1, 4, 1, 4, 2, 1, 3]
def baseStart_5703804 : Nat := 118140960795 + 5703804 * 2 ^ 59
def prefixEnd_5703804 : Nat := 4983230072969 + 3 ^ 40 * 5703804 * 2
def baseEnd_5703804 : Nat := 2928793011037507074318689

theorem tailTrace_5703804 : CollatzResearch.WordTrace tailWord_5703804 prefixEnd_5703804 2928793011037507074318689 := by
  unfold tailWord_5703804
  simp only [CollatzResearch.WordTrace]
  refine ⟨104017411314049857506843233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138689881752066476675790977 104017411314049857506843233)
  ·
    refine ⟨78013058485537393130132425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104017411314049857506843233 78013058485537393130132425)
    ·
      refine ⟨58509793864153044847599319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78013058485537393130132425 58509793864153044847599319)
      ·
        refine ⟨87764690796229567271398979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58509793864153044847599319 87764690796229567271398979)
        ·
          refine ⟨131647036194344350907098469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87764690796229567271398979 131647036194344350907098469)
          ·
            refine ⟨24683819286439565795080963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 131647036194344350907098469 24683819286439565795080963)
            ·
              refine ⟨37025728929659348692621445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24683819286439565795080963 37025728929659348692621445)
              ·
                refine ⟨6942324174311127879866521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37025728929659348692621445 6942324174311127879866521)
                ·
                  refine ⟨5206743130733345909899891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6942324174311127879866521 5206743130733345909899891)
                  ·
                    refine ⟨7810114696100018864849837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5206743130733345909899891 7810114696100018864849837)
                    ·
                      refine ⟨2928793011037507074318689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7810114696100018864849837 2928793011037507074318689)
                      ·
                        rfl

theorem cell23_5703804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 4, 2, 1, 3].length) (baseStart_5703804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5703804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5703804 prefixEnd_5703804 := by exact prefixLift 5703804
  have htrace : WordTrace (prefixWord ++ tailWord_5703804) baseStart_5703804 baseEnd_5703804 := by
    simpa [prefixWord, tailWord_5703804, baseEnd_5703804] using wordTrace_append hprefix tailTrace_5703804
  have hstable : (prefixWord ++ tailWord_5703804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5703804).length < 2 ^ (prefixWord ++ tailWord_5703804).sum := by decide
  have hdescent : baseEnd_5703804 < baseStart_5703804 := by decide
  rcases family_descends (prefixWord ++ tailWord_5703804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5703805 : List Nat := [1, 4, 1, 1, 3, 4, 2, 2, 1, 2, 2]
def baseStart_5703805 : Nat := 118140960795 + 5703805 * 2 ^ 59
def prefixEnd_5703805 : Nat := 4983230072969 + 3 ^ 40 * 5703805 * 2
def baseEnd_5703805 : Nat := 2928793524518161570406185

theorem tailTrace_5703805 : CollatzResearch.WordTrace tailWord_5703805 prefixEnd_5703805 2928793524518161570406185 := by
  unfold tailWord_5703805
  simp only [CollatzResearch.WordTrace]
  refine ⟨208034859101096092184472869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138689906067397394789648579 208034859101096092184472869)
  ·
    refine ⟨39006536081455517284588663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 208034859101096092184472869 39006536081455517284588663)
    ·
      refine ⟨58509804122183275926882995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39006536081455517284588663 58509804122183275926882995)
      ·
        refine ⟨87764706183274913890324493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58509804122183275926882995 87764706183274913890324493)
        ·
          refine ⟨32911764818728092708871685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87764706183274913890324493 32911764818728092708871685)
          ·
            refine ⟨6170955903511517382913441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32911764818728092708871685 6170955903511517382913441)
            ·
              refine ⟨4628216927633638037185081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6170955903511517382913441 4628216927633638037185081)
              ·
                refine ⟨3471162695725228527888811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4628216927633638037185081 3471162695725228527888811)
                ·
                  refine ⟨5206744043587842791833217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3471162695725228527888811 5206744043587842791833217)
                  ·
                    refine ⟨3905058032690882093874913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5206744043587842791833217 3905058032690882093874913)
                    ·
                      refine ⟨2928793524518161570406185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3905058032690882093874913 2928793524518161570406185)
                      ·
                        rfl

theorem cell23_5703805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 2, 2, 1, 2, 2].length) (baseStart_5703805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5703805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5703805 prefixEnd_5703805 := by exact prefixLift 5703805
  have htrace : WordTrace (prefixWord ++ tailWord_5703805) baseStart_5703805 baseEnd_5703805 := by
    simpa [prefixWord, tailWord_5703805, baseEnd_5703805] using wordTrace_append hprefix tailTrace_5703805
  have hstable : (prefixWord ++ tailWord_5703805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5703805).length < 2 ^ (prefixWord ++ tailWord_5703805).sum := by decide
  have hdescent : baseEnd_5703805 < baseStart_5703805 := by decide
  rcases family_descends (prefixWord ++ tailWord_5703805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5703867 : List Nat := [1, 1, 1, 1, 1, 2, 5, 6, 5]
def baseStart_5703867 : Nat := 118140960795 + 5703867 * 2 ^ 59
def prefixEnd_5703867 : Nat := 4983230072969 + 3 ^ 40 * 5703867 * 2
def baseEnd_5703867 : Nat := 325425040035415591981211

theorem tailTrace_5703867 : CollatzResearch.WordTrace tailWord_5703867 prefixEnd_5703867 325425040035415591981211 := by
  unfold tailWord_5703867
  simp only [CollatzResearch.WordTrace]
  refine ⟨208037120426871476773229855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138691413617914317848819903 208037120426871476773229855)
  ·
    refine ⟨312055680640307215159844783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208037120426871476773229855 312055680640307215159844783)
    ·
      refine ⟨468083520960460822739767175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312055680640307215159844783 468083520960460822739767175)
      ·
        refine ⟨702125281440691234109650763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 468083520960460822739767175 702125281440691234109650763)
        ·
          refine ⟨1053187922161036851164476145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 702125281440691234109650763 1053187922161036851164476145)
          ·
            refine ⟨789890941620777638373357109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1053187922161036851164476145 789890941620777638373357109)
            ·
              refine ⟨74052275776947903597502229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 789890941620777638373357109 74052275776947903597502229)
              ·
                refine ⟨3471200427044432981132917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 74052275776947903597502229 3471200427044432981132917)
                ·
                  refine ⟨325425040035415591981211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3471200427044432981132917 325425040035415591981211)
                  ·
                    rfl

theorem cell23_5703867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 6, 5].length) (baseStart_5703867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5703867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5703867 prefixEnd_5703867 := by exact prefixLift 5703867
  have htrace : WordTrace (prefixWord ++ tailWord_5703867) baseStart_5703867 baseEnd_5703867 := by
    simpa [prefixWord, tailWord_5703867, baseEnd_5703867] using wordTrace_append hprefix tailTrace_5703867
  have hstable : (prefixWord ++ tailWord_5703867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5703867).length < 2 ^ (prefixWord ++ tailWord_5703867).sum := by decide
  have hdescent : baseEnd_5703867 < baseStart_5703867 := by decide
  rcases family_descends (prefixWord ++ tailWord_5703867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5703877 : List Nat := [1, 3, 1, 1, 1, 1, 6, 1, 2, 3, 3]
def baseStart_5703877 : Nat := 118140960795 + 5703877 * 2 ^ 59
def prefixEnd_5703877 : Nat := 4983230072969 + 3 ^ 40 * 5703877 * 2
def baseEnd_5703877 : Nat := 2928830495125285288705853

theorem tailTrace_5703877 : CollatzResearch.WordTrace tailWord_5703877 prefixEnd_5703877 2928830495125285288705853 := by
  unfold tailWord_5703877
  simp only [CollatzResearch.WordTrace]
  refine ⟨208037485156835248481093885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138691656771223498987395923 208037485156835248481093885)
  ·
    refine ⟨78014056933813218180410207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208037485156835248481093885 78014056933813218180410207)
    ·
      refine ⟨117021085400719827270615311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78014056933813218180410207 117021085400719827270615311)
      ·
        refine ⟨175531628101079740905922967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117021085400719827270615311 175531628101079740905922967)
        ·
          refine ⟨263297442151619611358884451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175531628101079740905922967 263297442151619611358884451)
          ·
            refine ⟨394946163227429417038326677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 263297442151619611358884451 394946163227429417038326677)
            ·
              refine ⟨18513101401285753923671563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 394946163227429417038326677 18513101401285753923671563)
              ·
                refine ⟨27769652101928630885507345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18513101401285753923671563 27769652101928630885507345)
                ·
                  refine ⟨20827239076446473164130509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27769652101928630885507345 20827239076446473164130509)
                  ·
                    refine ⟨7810214653667427436548941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20827239076446473164130509 7810214653667427436548941)
                    ·
                      refine ⟨2928830495125285288705853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7810214653667427436548941 2928830495125285288705853)
                      ·
                        rfl

theorem cell23_5703877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 1, 2, 3, 3].length) (baseStart_5703877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5703877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5703877 prefixEnd_5703877 := by exact prefixLift 5703877
  have htrace : WordTrace (prefixWord ++ tailWord_5703877) baseStart_5703877 baseEnd_5703877 := by
    simpa [prefixWord, tailWord_5703877, baseEnd_5703877] using wordTrace_append hprefix tailTrace_5703877
  have hstable : (prefixWord ++ tailWord_5703877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5703877).length < 2 ^ (prefixWord ++ tailWord_5703877).sum := by decide
  have hdescent : baseEnd_5703877 < baseStart_5703877 := by decide
  rcases family_descends (prefixWord ++ tailWord_5703877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5703901 : List Nat := [1, 4, 3, 2, 1, 1, 3, 3, 5]
def baseStart_5703901 : Nat := 118140960795 + 5703901 * 2 ^ 59
def prefixEnd_5703901 : Nat := 4983230072969 + 3 ^ 40 * 5703901 * 2
def baseEnd_5703901 : Nat := 325426979851221466089527

theorem tailTrace_5703901 : CollatzResearch.WordTrace tailWord_5703901 prefixEnd_5703901 325426979851221466089527 := by
  unfold tailWord_5703901
  simp only [CollatzResearch.WordTrace]
  refine ⟨208038360508748300579967557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138692240339165533719978371 208038360508748300579967557)
  ·
    refine ⟨39007192595390306358743917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 208038360508748300579967557 39007192595390306358743917)
    ·
      refine ⟨14627697223271364884528969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39007192595390306358743917 14627697223271364884528969)
      ·
        refine ⟨10970772917453523663396727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14627697223271364884528969 10970772917453523663396727)
        ·
          refine ⟨16456159376180285495095091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10970772917453523663396727 16456159376180285495095091)
          ·
            refine ⟨24684239064270428242642637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16456159376180285495095091 24684239064270428242642637)
            ·
              refine ⟨9256589649101410590990989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24684239064270428242642637 9256589649101410590990989)
              ·
                refine ⟨3471221118413028971621621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9256589649101410590990989 3471221118413028971621621)
                ·
                  refine ⟨325426979851221466089527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3471221118413028971621621 325426979851221466089527)
                  ·
                    rfl

theorem cell23_5703901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 3, 5].length) (baseStart_5703901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5703901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5703901 prefixEnd_5703901 := by exact prefixLift 5703901
  have htrace : WordTrace (prefixWord ++ tailWord_5703901) baseStart_5703901 baseEnd_5703901 := by
    simpa [prefixWord, tailWord_5703901, baseEnd_5703901] using wordTrace_append hprefix tailTrace_5703901
  have hstable : (prefixWord ++ tailWord_5703901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5703901).length < 2 ^ (prefixWord ++ tailWord_5703901).sum := by decide
  have hdescent : baseEnd_5703901 < baseStart_5703901 := by decide
  rcases family_descends (prefixWord ++ tailWord_5703901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5703934 : List Nat := [4, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4]
def baseStart_5703934 : Nat := 118140960795 + 5703934 * 2 ^ 59
def prefixEnd_5703934 : Nat := 4983230072969 + 3 ^ 40 * 5703934 * 2
def baseEnd_5703934 : Nat := 2928859763522591565693091

theorem tailTrace_5703934 : CollatzResearch.WordTrace tailWord_5703934 prefixEnd_5703934 2928859763522591565693091 := by
  unfold tailWord_5703934
  simp only [CollatzResearch.WordTrace]
  refine ⟨26004945514703593401989857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138693042745085831477279237 26004945514703593401989857)
  ·
    refine ⟨19503709136027695051492393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26004945514703593401989857 19503709136027695051492393)
    ·
      refine ⟨14627781852020771288619295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19503709136027695051492393 14627781852020771288619295)
      ·
        refine ⟨21941672778031156932928943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14627781852020771288619295 21941672778031156932928943)
        ·
          refine ⟨32912509167046735399393415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21941672778031156932928943 32912509167046735399393415)
          ·
            refine ⟨49368763750570103099090123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32912509167046735399393415 49368763750570103099090123)
            ·
              refine ⟨74053145625855154648635185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49368763750570103099090123 74053145625855154648635185)
              ·
                refine ⟨55539859219391365986476389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74053145625855154648635185 55539859219391365986476389)
                ·
                  refine ⟨10413723603635881122464323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55539859219391365986476389 10413723603635881122464323)
                  ·
                    refine ⟨15620585405453821683696485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10413723603635881122464323 15620585405453821683696485)
                    ·
                      refine ⟨2928859763522591565693091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15620585405453821683696485 2928859763522591565693091)
                      ·
                        rfl

theorem cell23_5703934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_5703934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5703934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5703934 prefixEnd_5703934 := by exact prefixLift 5703934
  have htrace : WordTrace (prefixWord ++ tailWord_5703934) baseStart_5703934 baseEnd_5703934 := by
    simpa [prefixWord, tailWord_5703934, baseEnd_5703934] using wordTrace_append hprefix tailTrace_5703934
  have hstable : (prefixWord ++ tailWord_5703934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5703934).length < 2 ^ (prefixWord ++ tailWord_5703934).sum := by decide
  have hdescent : baseEnd_5703934 < baseStart_5703934 := by decide
  rcases family_descends (prefixWord ++ tailWord_5703934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5703987 : List Nat := [1, 1, 1, 2, 5, 1, 1, 1, 5, 5]
def baseStart_5703987 : Nat := 118140960795 + 5703987 * 2 ^ 59
def prefixEnd_5703987 : Nat := 4983230072969 + 3 ^ 40 * 5703987 * 2
def baseEnd_5703987 : Nat := 976295659332426619443449

theorem tailTrace_5703987 : CollatzResearch.WordTrace tailWord_5703987 prefixEnd_5703987 976295659332426619443449 := by
  unfold tailWord_5703987
  simp only [CollatzResearch.WordTrace]
  refine ⟨208041497186436737267598215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138694331457624491511732143 208041497186436737267598215)
  ·
    refine ⟨312062245779655105901397323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208041497186436737267598215 312062245779655105901397323)
    ·
      refine ⟨468093368669482658852095985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312062245779655105901397323 468093368669482658852095985)
      ·
        refine ⟨351070026502111994139071989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 468093368669482658852095985 351070026502111994139071989)
        ·
          refine ⟨32912814984572999450537999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 351070026502111994139071989 32912814984572999450537999)
          ·
            refine ⟨49369222476859499175806999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32912814984572999450537999 49369222476859499175806999)
            ·
              refine ⟨74053833715289248763710499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49369222476859499175806999 74053833715289248763710499)
              ·
                refine ⟨111080750572933873145565749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74053833715289248763710499 111080750572933873145565749)
                ·
                  refine ⟨10413820366212550607396789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 111080750572933873145565749 10413820366212550607396789)
                  ·
                    refine ⟨976295659332426619443449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10413820366212550607396789 976295659332426619443449)
                    ·
                      rfl

theorem cell23_5703987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 5, 5].length) (baseStart_5703987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5703987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5703987 prefixEnd_5703987 := by exact prefixLift 5703987
  have htrace : WordTrace (prefixWord ++ tailWord_5703987) baseStart_5703987 baseEnd_5703987 := by
    simpa [prefixWord, tailWord_5703987, baseEnd_5703987] using wordTrace_append hprefix tailTrace_5703987
  have hstable : (prefixWord ++ tailWord_5703987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5703987).length < 2 ^ (prefixWord ++ tailWord_5703987).sum := by decide
  have hdescent : baseEnd_5703987 < baseStart_5703987 := by decide
  rcases family_descends (prefixWord ++ tailWord_5703987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5704018 : List Nat := [3, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3]
def baseStart_5704018 : Nat := 118140960795 + 5704018 * 2 ^ 59
def prefixEnd_5704018 : Nat := 4983230072969 + 3 ^ 40 * 5704018 * 2
def baseEnd_5704018 : Nat := 2928902895897569237042705

theorem tailTrace_5704018 : CollatzResearch.WordTrace tailWord_5704018 prefixEnd_5704018 2928902895897569237042705 := by
  unfold tailWord_5704018
  simp only [CollatzResearch.WordTrace]
  refine ⟨52010656962331107390494177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138695085232882953041317805 52010656962331107390494177)
  ·
    refine ⟨39007992721748330542870633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52010656962331107390494177 39007992721748330542870633)
    ·
      refine ⟨29255994541311247907152975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39007992721748330542870633 29255994541311247907152975)
      ·
        refine ⟨43883991811966871860729463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29255994541311247907152975 43883991811966871860729463)
        ·
          refine ⟨65825987717950307791094195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43883991811966871860729463 65825987717950307791094195)
          ·
            refine ⟨98738981576925461686641293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65825987717950307791094195 98738981576925461686641293)
            ·
              refine ⟨37027118091347048132490485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 98738981576925461686641293 37027118091347048132490485)
              ·
                refine ⟨3471292321063785762420983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37027118091347048132490485 3471292321063785762420983)
                ·
                  refine ⟨5206938481595678643631475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3471292321063785762420983 5206938481595678643631475)
                  ·
                    refine ⟨7810407722393517965447213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5206938481595678643631475 7810407722393517965447213)
                    ·
                      refine ⟨2928902895897569237042705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7810407722393517965447213 2928902895897569237042705)
                      ·
                        rfl

theorem cell23_5704018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3].length) (baseStart_5704018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5704018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5704018 prefixEnd_5704018 := by exact prefixLift 5704018
  have htrace : WordTrace (prefixWord ++ tailWord_5704018) baseStart_5704018 baseEnd_5704018 := by
    simpa [prefixWord, tailWord_5704018, baseEnd_5704018] using wordTrace_append hprefix tailTrace_5704018
  have hstable : (prefixWord ++ tailWord_5704018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5704018).length < 2 ^ (prefixWord ++ tailWord_5704018).sum := by decide
  have hdescent : baseEnd_5704018 < baseStart_5704018 := by decide
  rcases family_descends (prefixWord ++ tailWord_5704018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5704021 : List Nat := [1, 3, 2, 2, 4, 1, 1, 3, 1, 5]
def baseStart_5704021 : Nat := 118140960795 + 5704021 * 2 ^ 59
def prefixEnd_5704021 : Nat := 4983230072969 + 3 ^ 40 * 5704021 * 2
def baseEnd_5704021 : Nat := 976301478779844241768397

theorem tailTrace_5704021 : CollatzResearch.WordTrace tailWord_5704021 prefixEnd_5704021 976301478779844241768397 := by
  unfold tailWord_5704021
  simp only [CollatzResearch.WordTrace]
  refine ⟨208042737268313561074335917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138695158178875707382890611 208042737268313561074335917)
  ·
    refine ⟨78016026475617585402875969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208042737268313561074335917 78016026475617585402875969)
    ·
      refine ⟨58512019856713189052156977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78016026475617585402875969 58512019856713189052156977)
      ·
        refine ⟨43884014892534891789117733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58512019856713189052156977 43884014892534891789117733)
        ·
          refine ⟨8228252792350292210459575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43884014892534891789117733 8228252792350292210459575)
          ·
            refine ⟨12342379188525438315689363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8228252792350292210459575 12342379188525438315689363)
            ·
              refine ⟨18513568782788157473534045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12342379188525438315689363 18513568782788157473534045)
              ·
                refine ⟨6942588293545559052575267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18513568782788157473534045 6942588293545559052575267)
                ·
                  refine ⟨10413882440318338578862901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6942588293545559052575267 10413882440318338578862901)
                  ·
                    refine ⟨976301478779844241768397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10413882440318338578862901 976301478779844241768397)
                    ·
                      rfl

theorem cell23_5704021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 3, 1, 5].length) (baseStart_5704021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5704021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5704021 prefixEnd_5704021 := by exact prefixLift 5704021
  have htrace : WordTrace (prefixWord ++ tailWord_5704021) baseStart_5704021 baseEnd_5704021 := by
    simpa [prefixWord, tailWord_5704021, baseEnd_5704021] using wordTrace_append hprefix tailTrace_5704021
  have hstable : (prefixWord ++ tailWord_5704021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5704021).length < 2 ^ (prefixWord ++ tailWord_5704021).sum := by decide
  have hdescent : baseEnd_5704021 < baseStart_5704021 := by decide
  rcases family_descends (prefixWord ++ tailWord_5704021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5704061 : List Nat := [1, 4, 1, 1, 2, 3, 1, 4, 1, 2, 3]
def baseStart_5704061 : Nat := 118140960795 + 5704061 * 2 ^ 59
def prefixEnd_5704061 : Nat := 4983230072969 + 3 ^ 40 * 5704061 * 2
def baseEnd_5704061 : Nat := 2928924975565712568805007

theorem tailTrace_5704061 : CollatzResearch.WordTrace tailWord_5704061 prefixEnd_5704061 2928924975565712568805007 := by
  unfold tailWord_5704061
  simp only [CollatzResearch.WordTrace]
  refine ⟨208044196188168647905792037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138696130792112431937194691 208044196188168647905792037)
  ·
    refine ⟨39008286785281621482336007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 208044196188168647905792037 39008286785281621482336007)
    ·
      refine ⟨58512430177922432223504011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39008286785281621482336007 58512430177922432223504011)
      ·
        refine ⟨87768645266883648335256017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58512430177922432223504011 87768645266883648335256017)
        ·
          refine ⟨65826483950162736251442013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87768645266883648335256017 65826483950162736251442013)
          ·
            refine ⟨24684931481311026094290755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65826483950162736251442013 24684931481311026094290755)
            ·
              refine ⟨37027397221966539141436133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24684931481311026094290755 37027397221966539141436133)
              ·
                refine ⟨6942636979118726089019275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37027397221966539141436133 6942636979118726089019275)
                ·
                  refine ⟨10413955468678089133528913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6942636979118726089019275 10413955468678089133528913)
                  ·
                    refine ⟨7810466601508566850146685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10413955468678089133528913 7810466601508566850146685)
                    ·
                      refine ⟨2928924975565712568805007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7810466601508566850146685 2928924975565712568805007)
                      ·
                        rfl

theorem cell23_5704061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 4, 1, 2, 3].length) (baseStart_5704061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5704061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5704061 prefixEnd_5704061 := by exact prefixLift 5704061
  have htrace : WordTrace (prefixWord ++ tailWord_5704061) baseStart_5704061 baseEnd_5704061 := by
    simpa [prefixWord, tailWord_5704061, baseEnd_5704061] using wordTrace_append hprefix tailTrace_5704061
  have hstable : (prefixWord ++ tailWord_5704061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5704061).length < 2 ^ (prefixWord ++ tailWord_5704061).sum := by decide
  have hdescent : baseEnd_5704061 < baseStart_5704061 := by decide
  rcases family_descends (prefixWord ++ tailWord_5704061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5704075 : List Nat := [1, 1, 1, 1, 4, 4, 3, 3, 1, 2, 2]
def baseStart_5704075 : Nat := 118140960795 + 5704075 * 2 ^ 59
def prefixEnd_5704075 : Nat := 4983230072969 + 3 ^ 40 * 5704075 * 2
def baseEnd_5704075 : Nat := 2928932164294875514029943

theorem tailTrace_5704075 : CollatzResearch.WordTrace tailWord_5704075 prefixEnd_5704075 2928932164294875514029943 := by
  unfold tailWord_5704075
  simp only [CollatzResearch.WordTrace]
  refine ⟨208044706810117928296801679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138696471206745285531201119 208044706810117928296801679)
  ·
    refine ⟨312067060215176892445202519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208044706810117928296801679 312067060215176892445202519)
    ·
      refine ⟨468100590322765338667803779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312067060215176892445202519 468100590322765338667803779)
      ·
        refine ⟨702150885484148008001705669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 468100590322765338667803779 702150885484148008001705669)
        ·
          refine ⟨131653291028277751500319813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 702150885484148008001705669 131653291028277751500319813)
          ·
            refine ⟨24684992067802078406309965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 131653291028277751500319813 24684992067802078406309965)
            ·
              refine ⟨9256872025425779402366237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24684992067802078406309965 9256872025425779402366237)
              ·
                refine ⟨3471327009534667275887339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9256872025425779402366237 3471327009534667275887339)
                ·
                  refine ⟨5206990514302000913831009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3471327009534667275887339 5206990514302000913831009)
                  ·
                    refine ⟨3905242885726500685373257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5206990514302000913831009 3905242885726500685373257)
                    ·
                      refine ⟨2928932164294875514029943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3905242885726500685373257 2928932164294875514029943)
                      ·
                        rfl

theorem cell23_5704075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 3, 1, 2, 2].length) (baseStart_5704075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5704075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5704075 prefixEnd_5704075 := by exact prefixLift 5704075
  have htrace : WordTrace (prefixWord ++ tailWord_5704075) baseStart_5704075 baseEnd_5704075 := by
    simpa [prefixWord, tailWord_5704075, baseEnd_5704075] using wordTrace_append hprefix tailTrace_5704075
  have hstable : (prefixWord ++ tailWord_5704075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5704075).length < 2 ^ (prefixWord ++ tailWord_5704075).sum := by decide
  have hdescent : baseEnd_5704075 < baseStart_5704075 := by decide
  rcases family_descends (prefixWord ++ tailWord_5704075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5704078 : List Nat := [4, 1, 1, 4, 1, 1, 2, 3, 1, 2, 3]
def baseStart_5704078 : Nat := 118140960795 + 5704078 * 2 ^ 59
def prefixEnd_5704078 : Nat := 4983230072969 + 3 ^ 40 * 5704078 * 2
def baseEnd_5704078 : Nat := 2928933704736839002292429

theorem tailTrace_5704078 : CollatzResearch.WordTrace tailWord_5704078 prefixEnd_5704078 2928933704736839002292429 := by
  unfold tailWord_5704078
  simp only [CollatzResearch.WordTrace]
  refine ⟨26005602028638382476145111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138696544152738039872773925 26005602028638382476145111)
  ·
    refine ⟨39008403042957573714217667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26005602028638382476145111 39008403042957573714217667)
    ·
      refine ⟨58512604564436360571326501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39008403042957573714217667 58512604564436360571326501)
      ·
        refine ⟨10971113355831817607123719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58512604564436360571326501 10971113355831817607123719)
        ·
          refine ⟨16456670033747726410685579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10971113355831817607123719 16456670033747726410685579)
          ·
            refine ⟨24685005050621589616028369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16456670033747726410685579 24685005050621589616028369)
            ·
              refine ⟨18513753787966192212021277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24685005050621589616028369 18513753787966192212021277)
              ·
                refine ⟨6942657670487322079507979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18513753787966192212021277 6942657670487322079507979)
                ·
                  refine ⟨10413986505730983119261969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6942657670487322079507979 10413986505730983119261969)
                  ·
                    refine ⟨7810489879298237339446477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10413986505730983119261969 7810489879298237339446477)
                    ·
                      refine ⟨2928933704736839002292429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7810489879298237339446477 2928933704736839002292429)
                      ·
                        rfl

theorem cell23_5704078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_5704078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5704078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5704078 prefixEnd_5704078 := by exact prefixLift 5704078
  have htrace : WordTrace (prefixWord ++ tailWord_5704078) baseStart_5704078 baseEnd_5704078 := by
    simpa [prefixWord, tailWord_5704078, baseEnd_5704078] using wordTrace_append hprefix tailTrace_5704078
  have hstable : (prefixWord ++ tailWord_5704078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5704078).length < 2 ^ (prefixWord ++ tailWord_5704078).sum := by decide
  have hdescent : baseEnd_5704078 < baseStart_5704078 := by decide
  rcases family_descends (prefixWord ++ tailWord_5704078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5704086 : List Nat := [5, 3, 1, 2, 2, 1, 1, 1, 3, 1, 3]
def baseStart_5704086 : Nat := 118140960795 + 5704086 * 2 ^ 59
def prefixEnd_5704086 : Nat := 4983230072969 + 3 ^ 40 * 5704086 * 2
def baseEnd_5704086 : Nat := 2928937812582074970992393

theorem tailTrace_5704086 : CollatzResearch.WordTrace tailWord_5704086 prefixEnd_5704086 2928937812582074970992393 := by
  unfold tailWord_5704086
  simp only [CollatzResearch.WordTrace]
  refine ⟨13002819250817379823465757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 138696738675385384783634741 13002819250817379823465757)
  ·
    refine ⟨4876057219056517433799659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13002819250817379823465757 4876057219056517433799659)
    ·
      refine ⟨7314085828584776150699489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4876057219056517433799659 7314085828584776150699489)
      ·
        refine ⟨5485564371438582113024617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7314085828584776150699489 5485564371438582113024617)
        ·
          refine ⟨4114173278578936584768463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5485564371438582113024617 4114173278578936584768463)
          ·
            refine ⟨6171259917868404877152695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4114173278578936584768463 6171259917868404877152695)
            ·
              refine ⟨9256889876802607315729043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6171259917868404877152695 9256889876802607315729043)
              ·
                refine ⟨13885334815203910973593565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9256889876802607315729043 13885334815203910973593565)
                ·
                  refine ⟨5207000555701466615097587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13885334815203910973593565 5207000555701466615097587)
                  ·
                    refine ⟨7810500833552199922646381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5207000555701466615097587 7810500833552199922646381)
                    ·
                      refine ⟨2928937812582074970992393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7810500833552199922646381 2928937812582074970992393)
                      ·
                        rfl

theorem cell23_5704086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_5704086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5704086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5704086 prefixEnd_5704086 := by exact prefixLift 5704086
  have htrace : WordTrace (prefixWord ++ tailWord_5704086) baseStart_5704086 baseEnd_5704086 := by
    simpa [prefixWord, tailWord_5704086, baseEnd_5704086] using wordTrace_append hprefix tailTrace_5704086
  have hstable : (prefixWord ++ tailWord_5704086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5704086).length < 2 ^ (prefixWord ++ tailWord_5704086).sum := by decide
  have hdescent : baseEnd_5704086 < baseStart_5704086 := by decide
  rcases family_descends (prefixWord ++ tailWord_5704086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5704101 : List Nat := [1, 3, 1, 2, 1, 1, 4, 2, 3, 3, 2]
def baseStart_5704101 : Nat := 118140960795 + 5704101 * 2 ^ 59
def prefixEnd_5704101 : Nat := 4983230072969 + 3 ^ 40 * 5704101 * 2
def baseEnd_5704101 : Nat := 2928945514791892412304823

theorem tailTrace_5704101 : CollatzResearch.WordTrace tailWord_5704101 prefixEnd_5704101 2928945514791892412304823 := by
  unfold tailWord_5704101
  simp only [CollatzResearch.WordTrace]
  refine ⟨208045655108023734737248157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138697103405349156491498771 208045655108023734737248157)
  ·
    refine ⟨78017120665508900526468059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208045655108023734737248157 78017120665508900526468059)
    ·
      refine ⟨117025680998263350789702089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78017120665508900526468059 117025680998263350789702089)
      ·
        refine ⟨87769260748697513092276567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117025680998263350789702089 87769260748697513092276567)
        ·
          refine ⟨131653891123046269638414851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87769260748697513092276567 131653891123046269638414851)
          ·
            refine ⟨197480836684569404457622277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131653891123046269638414851 197480836684569404457622277)
            ·
              refine ⟨37027656878356763335804177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 197480836684569404457622277 37027656878356763335804177)
              ·
                refine ⟨27770742658767572501853133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37027656878356763335804177 27770742658767572501853133)
                ·
                  refine ⟨10414028497037839688194925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27770742658767572501853133 10414028497037839688194925)
                  ·
                    refine ⟨3905260686389189883073097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10414028497037839688194925 3905260686389189883073097)
                    ·
                      refine ⟨2928945514791892412304823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3905260686389189883073097 2928945514791892412304823)
                      ·
                        rfl

theorem cell23_5704101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 2, 3, 3, 2].length) (baseStart_5704101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5704101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5704101 prefixEnd_5704101 := by exact prefixLift 5704101
  have htrace : WordTrace (prefixWord ++ tailWord_5704101) baseStart_5704101 baseEnd_5704101 := by
    simpa [prefixWord, tailWord_5704101, baseEnd_5704101] using wordTrace_append hprefix tailTrace_5704101
  have hstable : (prefixWord ++ tailWord_5704101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5704101).length < 2 ^ (prefixWord ++ tailWord_5704101).sum := by decide
  have hdescent : baseEnd_5704101 < baseStart_5704101 := by decide
  rcases family_descends (prefixWord ++ tailWord_5704101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5704129 : List Nat := [1, 2, 7, 1, 1, 1, 3, 1, 1, 2, 3]
def baseStart_5704129 : Nat := 118140960795 + 5704129 * 2 ^ 59
def prefixEnd_5704129 : Nat := 4983230072969 + 3 ^ 40 * 5704129 * 2
def baseEnd_5704129 : Nat := 2928959892250218302754695

theorem tailTrace_5704129 : CollatzResearch.WordTrace tailWord_5704129 prefixEnd_5704129 2928959892250218302754695 := by
  unfold tailWord_5704129
  simp only [CollatzResearch.WordTrace]
  refine ⟨208046676351922295519267441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138697784234614863679511627 208046676351922295519267441)
  ·
    refine ⟨156035007263941721639450581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208046676351922295519267441 156035007263941721639450581)
    ·
      refine ⟨3657070482748634100924623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 156035007263941721639450581 3657070482748634100924623)
      ·
        refine ⟨5485605724122951151386935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3657070482748634100924623 5485605724122951151386935)
        ·
          refine ⟨8228408586184426727080403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5485605724122951151386935 8228408586184426727080403)
          ·
            refine ⟨12342612879276640090620605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8228408586184426727080403 12342612879276640090620605)
            ·
              refine ⟨4628479829728740033982727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12342612879276640090620605 4628479829728740033982727)
              ·
                refine ⟨6942719744593110050974091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4628479829728740033982727 6942719744593110050974091)
                ·
                  refine ⟨10414079616889665076461137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6942719744593110050974091 10414079616889665076461137)
                  ·
                    refine ⟨7810559712667248807345853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10414079616889665076461137 7810559712667248807345853)
                    ·
                      refine ⟨2928959892250218302754695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7810559712667248807345853 2928959892250218302754695)
                      ·
                        rfl

theorem cell23_5704129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_5704129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5704129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5704129 prefixEnd_5704129 := by exact prefixLift 5704129
  have htrace : WordTrace (prefixWord ++ tailWord_5704129) baseStart_5704129 baseEnd_5704129 := by
    simpa [prefixWord, tailWord_5704129, baseEnd_5704129] using wordTrace_append hprefix tailTrace_5704129
  have hstable : (prefixWord ++ tailWord_5704129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5704129).length < 2 ^ (prefixWord ++ tailWord_5704129).sum := by decide
  have hdescent : baseEnd_5704129 < baseStart_5704129 := by decide
  rcases family_descends (prefixWord ++ tailWord_5704129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5704135 : List Nat := [1, 1, 4, 1, 1, 5, 3, 1, 1, 3, 2]
def baseStart_5704135 : Nat := 118140960795 + 5704135 * 2 ^ 59
def prefixEnd_5704135 : Nat := 4983230072969 + 3 ^ 40 * 5704135 * 2
def baseEnd_5704135 : Nat := 2928962973134145279279667

theorem tailTrace_5704135 : CollatzResearch.WordTrace tailWord_5704135 prefixEnd_5704135 2928962973134145279279667 := by
  unfold tailWord_5704135
  simp only [CollatzResearch.WordTrace]
  refine ⟨208046895189900558543985859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138697930126600372362657239 208046895189900558543985859)
  ·
    refine ⟨312070342784850837815978789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208046895189900558543985859 312070342784850837815978789)
    ·
      refine ⟨58513189272159532090496023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 312070342784850837815978789 58513189272159532090496023)
      ·
        refine ⟨87769783908239298135744035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58513189272159532090496023 87769783908239298135744035)
        ·
          refine ⟨131654675862358947203616053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87769783908239298135744035 131654675862358947203616053)
          ·
            refine ⟨12342625862096151300339005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 131654675862358947203616053 12342625862096151300339005)
            ·
              refine ⟨4628484698286056737627127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12342625862096151300339005 4628484698286056737627127)
              ·
                refine ⟨6942727047429085106440691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4628484698286056737627127 6942727047429085106440691)
                ·
                  refine ⟨10414090571143627659661037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6942727047429085106440691 10414090571143627659661037)
                  ·
                    refine ⟨3905283964178860372372889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10414090571143627659661037 3905283964178860372372889)
                    ·
                      refine ⟨2928962973134145279279667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3905283964178860372372889 2928962973134145279279667)
                      ·
                        rfl

theorem cell23_5704135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 3, 1, 1, 3, 2].length) (baseStart_5704135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5704135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5704135 prefixEnd_5704135 := by exact prefixLift 5704135
  have htrace : WordTrace (prefixWord ++ tailWord_5704135) baseStart_5704135 baseEnd_5704135 := by
    simpa [prefixWord, tailWord_5704135, baseEnd_5704135] using wordTrace_append hprefix tailTrace_5704135
  have hstable : (prefixWord ++ tailWord_5704135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5704135).length < 2 ^ (prefixWord ++ tailWord_5704135).sum := by decide
  have hdescent : baseEnd_5704135 < baseStart_5704135 := by decide
  rcases family_descends (prefixWord ++ tailWord_5704135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5704154 : List Nat := [3, 1, 1, 2, 3, 1, 2, 3, 7]
def baseStart_5704154 : Nat := 118140960795 + 5704154 * 2 ^ 59
def prefixEnd_5704154 : Nat := 4983230072969 + 3 ^ 40 * 5704154 * 2
def baseEnd_5704154 : Nat := 325441414362953411660231

theorem tailTrace_5704154 : CollatzResearch.WordTrace tailWord_5704154 prefixEnd_5704154 325441414362953411660231 := by
  unfold tailWord_5704154
  simp only [CollatzResearch.WordTrace]
  refine ⟨52011897044207931197231879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138698392117887816525951677 52011897044207931197231879)
  ·
    refine ⟨78017845566311896795847819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52011897044207931197231879 78017845566311896795847819)
    ·
      refine ⟨117026768349467845193771729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78017845566311896795847819 117026768349467845193771729)
      ·
        refine ⟨87770076262100883895328797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117026768349467845193771729 87770076262100883895328797)
        ·
          refine ⟨32913778598287831460748299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87770076262100883895328797 32913778598287831460748299)
          ·
            refine ⟨49370667897431747191122449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32913778598287831460748299 49370667897431747191122449)
            ·
              refine ⟨37028000923073810393341837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49370667897431747191122449 37028000923073810393341837)
              ·
                refine ⟨13885500346152678897503189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37028000923073810393341837 13885500346152678897503189)
                ·
                  refine ⟨325441414362953411660231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13885500346152678897503189 325441414362953411660231)
                  ·
                    rfl

theorem cell23_5704154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 3, 7].length) (baseStart_5704154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5704154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5704154 prefixEnd_5704154 := by exact prefixLift 5704154
  have htrace : WordTrace (prefixWord ++ tailWord_5704154) baseStart_5704154 baseEnd_5704154 := by
    simpa [prefixWord, tailWord_5704154, baseEnd_5704154] using wordTrace_append hprefix tailTrace_5704154
  have hstable : (prefixWord ++ tailWord_5704154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5704154).length < 2 ^ (prefixWord ++ tailWord_5704154).sum := by decide
  have hdescent : baseEnd_5704154 < baseStart_5704154 := by decide
  rcases family_descends (prefixWord ++ tailWord_5704154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5704165 : List Nat := [1, 3, 1, 5, 2, 1, 2, 1, 1, 4, 2]
def baseStart_5704165 : Nat := 118140960795 + 5704165 * 2 ^ 59
def prefixEnd_5704165 : Nat := 4983230072969 + 3 ^ 40 * 5704165 * 2
def baseEnd_5704165 : Nat := 2928978377553780161904529

theorem tailTrace_5704165 : CollatzResearch.WordTrace tailWord_5704165 prefixEnd_5704165 2928978377553780161904529 := by
  unfold tailWord_5704165
  simp only [CollatzResearch.WordTrace]
  refine ⟨208047989379791873667577949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138698659586527915778385299 208047989379791873667577949)
  ·
    refine ⟨78017996017421952625341731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208047989379791873667577949 78017996017421952625341731)
    ·
      refine ⟨117026994026132928938012597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78017996017421952625341731 117026994026132928938012597)
      ·
        refine ⟨10971280689949962087938681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 117026994026132928938012597 10971280689949962087938681)
        ·
          refine ⟨8228460517462471565954011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10971280689949962087938681 8228460517462471565954011)
          ·
            refine ⟨12342690776193707348931017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8228460517462471565954011 12342690776193707348931017)
            ·
              refine ⟨9257018082145280511698263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12342690776193707348931017 9257018082145280511698263)
              ·
                refine ⟨13885527123217920767547395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9257018082145280511698263 13885527123217920767547395)
                ·
                  refine ⟨20828290684826881151321093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13885527123217920767547395 20828290684826881151321093)
                  ·
                    refine ⟨3905304503405040215872705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20828290684826881151321093 3905304503405040215872705)
                    ·
                      refine ⟨2928978377553780161904529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3905304503405040215872705 2928978377553780161904529)
                      ·
                        rfl

theorem cell23_5704165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 1, 1, 4, 2].length) (baseStart_5704165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5704165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5704165 prefixEnd_5704165 := by exact prefixLift 5704165
  have htrace : WordTrace (prefixWord ++ tailWord_5704165) baseStart_5704165 baseEnd_5704165 := by
    simpa [prefixWord, tailWord_5704165, baseEnd_5704165] using wordTrace_append hprefix tailTrace_5704165
  have hstable : (prefixWord ++ tailWord_5704165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5704165).length < 2 ^ (prefixWord ++ tailWord_5704165).sum := by decide
  have hdescent : baseEnd_5704165 < baseStart_5704165 := by decide
  rcases family_descends (prefixWord ++ tailWord_5704165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5704184 : List Nat := [2, 1, 2, 1, 1, 4, 3, 1, 1, 7]
def baseStart_5704184 : Nat := 118140960795 + 5704184 * 2 ^ 59
def prefixEnd_5704184 : Nat := 4983230072969 + 3 ^ 40 * 5704184 * 2
def baseEnd_5704184 : Nat := 976329377895405195855647

theorem tailTrace_5704184 : CollatzResearch.WordTrace tailWord_5704184 prefixEnd_5704184 976329377895405195855647 := by
  unfold tailWord_5704184
  simp only [CollatzResearch.WordTrace]
  refine ⟨104024341183361519956259803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138699121577815359941679737 104024341183361519956259803)
  ·
    refine ⟨156036511775042279934389705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104024341183361519956259803 156036511775042279934389705)
    ·
      refine ⟨117027383831281709950792279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156036511775042279934389705 117027383831281709950792279)
      ·
        refine ⟨175541075746922564926188419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117027383831281709950792279 175541075746922564926188419)
        ·
          refine ⟨263311613620383847389282629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175541075746922564926188419 263311613620383847389282629)
          ·
            refine ⟨49370927553821971385490493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 263311613620383847389282629 49370927553821971385490493)
            ·
              refine ⟨18514097832683239269558935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49370927553821971385490493 18514097832683239269558935)
              ·
                refine ⟨27771146749024858904338403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18514097832683239269558935 27771146749024858904338403)
                ·
                  refine ⟨41656720123537288356507605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27771146749024858904338403 41656720123537288356507605)
                  ·
                    refine ⟨976329377895405195855647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41656720123537288356507605 976329377895405195855647)
                    ·
                      rfl

theorem cell23_5704184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 1, 1, 7].length) (baseStart_5704184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5704184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5704184 prefixEnd_5704184 := by exact prefixLift 5704184
  have htrace : WordTrace (prefixWord ++ tailWord_5704184) baseStart_5704184 baseEnd_5704184 := by
    simpa [prefixWord, tailWord_5704184, baseEnd_5704184] using wordTrace_append hprefix tailTrace_5704184
  have hstable : (prefixWord ++ tailWord_5704184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5704184).length < 2 ^ (prefixWord ++ tailWord_5704184).sum := by decide
  have hdescent : baseEnd_5704184 < baseStart_5704184 := by decide
  rcases family_descends (prefixWord ++ tailWord_5704184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5704199 : List Nat := [1, 1, 4, 3, 4, 1, 1, 2, 2, 2, 2]
def baseStart_5704199 : Nat := 118140960795 + 5704199 * 2 ^ 59
def prefixEnd_5704199 : Nat := 4983230072969 + 3 ^ 40 * 5704199 * 2
def baseEnd_5704199 : Nat := 2928995835896033028879373

theorem tailTrace_5704199 : CollatzResearch.WordTrace tailWord_5704199 prefixEnd_5704199 2928995835896033028879373 := by
  unfold tailWord_5704199
  simp only [CollatzResearch.WordTrace]
  refine ⟨208049229461668697474315651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138699486307779131649543767 208049229461668697474315651)
  ·
    refine ⟨312073844192503046211473477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208049229461668697474315651 312073844192503046211473477)
    ·
      refine ⟨58513845786094321164651277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 312073844192503046211473477 58513845786094321164651277)
      ·
        refine ⟨21942692169785370436744229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58513845786094321164651277 21942692169785370436744229)
        ·
          refine ⟨4114254781834756956889543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21942692169785370436744229 4114254781834756956889543)
          ·
            refine ⟨6171382172752135435334315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4114254781834756956889543 6171382172752135435334315)
            ·
              refine ⟨9257073259128203153001473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6171382172752135435334315 9257073259128203153001473)
              ·
                refine ⟨6942804944346152364751105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9257073259128203153001473 6942804944346152364751105)
                ·
                  refine ⟨5207103708259614273563329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6942804944346152364751105 5207103708259614273563329)
                  ·
                    refine ⟨3905327781194710705172497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5207103708259614273563329 3905327781194710705172497)
                    ·
                      refine ⟨2928995835896033028879373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3905327781194710705172497 2928995835896033028879373)
                      ·
                        rfl

theorem cell23_5704199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 2, 2, 2, 2].length) (baseStart_5704199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5704199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5704199 prefixEnd_5704199 := by exact prefixLift 5704199
  have htrace : WordTrace (prefixWord ++ tailWord_5704199) baseStart_5704199 baseEnd_5704199 := by
    simpa [prefixWord, tailWord_5704199, baseEnd_5704199] using wordTrace_append hprefix tailTrace_5704199
  have hstable : (prefixWord ++ tailWord_5704199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5704199).length < 2 ^ (prefixWord ++ tailWord_5704199).sum := by decide
  have hdescent : baseEnd_5704199 < baseStart_5704199 := by decide
  rcases family_descends (prefixWord ++ tailWord_5704199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5704205 : List Nat := [1, 7, 1, 1, 1, 2, 2, 1, 7]
def baseStart_5704205 : Nat := 118140960795 + 5704205 * 2 ^ 59
def prefixEnd_5704205 : Nat := 4983230072969 + 3 ^ 40 * 5704205 * 2
def baseEnd_5704205 : Nat := 325444324086662222822705

theorem tailTrace_5704205 : CollatzResearch.WordTrace tailWord_5704205 prefixEnd_5704205 325444324086662222822705 := by
  unfold tailWord_5704205
  simp only [CollatzResearch.WordTrace]
  refine ⟨208049448299646960499034069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138699632199764640332689379 208049448299646960499034069)
  ·
    refine ⟨4876158944522975636696111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 208049448299646960499034069 4876158944522975636696111)
    ·
      refine ⟨7314238416784463455044167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4876158944522975636696111 7314238416784463455044167)
      ·
        refine ⟨10971357625176695182566251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7314238416784463455044167 10971357625176695182566251)
        ·
          refine ⟨16457036437765042773849377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10971357625176695182566251 16457036437765042773849377)
          ·
            refine ⟨12342777328323782080387033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16457036437765042773849377 12342777328323782080387033)
            ·
              refine ⟨9257082996242836560290275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12342777328323782080387033 9257082996242836560290275)
              ·
                refine ⟨13885624494364254840435413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9257082996242836560290275 13885624494364254840435413)
                ·
                  refine ⟨325444324086662222822705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13885624494364254840435413 325444324086662222822705)
                  ·
                    rfl

theorem cell23_5704205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_5704205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5704205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5704205 prefixEnd_5704205 := by exact prefixLift 5704205
  have htrace : WordTrace (prefixWord ++ tailWord_5704205) baseStart_5704205 baseEnd_5704205 := by
    simpa [prefixWord, tailWord_5704205, baseEnd_5704205] using wordTrace_append hprefix tailTrace_5704205
  have hstable : (prefixWord ++ tailWord_5704205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5704205).length < 2 ^ (prefixWord ++ tailWord_5704205).sum := by decide
  have hdescent : baseEnd_5704205 < baseStart_5704205 := by decide
  rcases family_descends (prefixWord ++ tailWord_5704205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5704221 : List Nat := [1, 4, 2, 2, 1, 2, 1, 2, 1, 3, 4]
def baseStart_5704221 : Nat := 118140960795 + 5704221 * 2 ^ 59
def prefixEnd_5704221 : Nat := 4983230072969 + 3 ^ 40 * 5704221 * 2
def baseEnd_5704221 : Nat := 2929007132470431942804271

theorem tailTrace_5704221 : CollatzResearch.WordTrace tailWord_5704221 prefixEnd_5704221 2929007132470431942804271 := by
  unfold tailWord_5704221
  simp only [CollatzResearch.WordTrace]
  refine ⟨208050031867588995231616517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138700021245059330154411011 208050031867588995231616517)
  ·
    refine ⟨39009380975172936605928097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 208050031867588995231616517 39009380975172936605928097)
    ·
      refine ⟨29257035731379702454446073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39009380975172936605928097 29257035731379702454446073)
      ·
        refine ⟨21942776798534776840834555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29257035731379702454446073 21942776798534776840834555)
        ·
          refine ⟨32914165197802165261251833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21942776798534776840834555 32914165197802165261251833)
          ·
            refine ⟨24685623898351623945938875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32914165197802165261251833 24685623898351623945938875)
            ·
              refine ⟨37028435847527435918908313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24685623898351623945938875 37028435847527435918908313)
              ·
                refine ⟨27771326885645576939181235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37028435847527435918908313 27771326885645576939181235)
                ·
                  refine ⟨41656990328468365408771853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27771326885645576939181235 41656990328468365408771853)
                  ·
                    refine ⟨15621371373175637028289445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41656990328468365408771853 15621371373175637028289445)
                    ·
                      refine ⟨2929007132470431942804271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15621371373175637028289445 2929007132470431942804271)
                      ·
                        rfl

theorem cell23_5704221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_5704221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5704221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5704221 prefixEnd_5704221 := by exact prefixLift 5704221
  have htrace : WordTrace (prefixWord ++ tailWord_5704221) baseStart_5704221 baseEnd_5704221 := by
    simpa [prefixWord, tailWord_5704221, baseEnd_5704221] using wordTrace_append hprefix tailTrace_5704221
  have hstable : (prefixWord ++ tailWord_5704221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5704221).length < 2 ^ (prefixWord ++ tailWord_5704221).sum := by decide
  have hdescent : baseEnd_5704221 < baseStart_5704221 := by decide
  rcases family_descends (prefixWord ++ tailWord_5704221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5704241 : List Nat := [1, 2, 2, 3, 1, 1, 4, 1, 1, 4, 3]
def baseStart_5704241 : Nat := 118140960795 + 5704241 * 2 ^ 59
def prefixEnd_5704241 : Nat := 4983230072969 + 3 ^ 40 * 5704241 * 2
def baseEnd_5704241 : Nat := 2929017402083521864554179

theorem tailTrace_5704241 : CollatzResearch.WordTrace tailWord_5704241 prefixEnd_5704241 2929017402083521864554179 := by
  unfold tailWord_5704241
  simp only [CollatzResearch.WordTrace]
  refine ⟨208050761327516538647344577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138700507551677692431563051 208050761327516538647344577)
  ·
    refine ⟨156038070995637403985508433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208050761327516538647344577 156038070995637403985508433)
    ·
      refine ⟨117028553246728052989131325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156038070995637403985508433 117028553246728052989131325)
      ·
        refine ⟨43885707467523019870924247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117028553246728052989131325 43885707467523019870924247)
        ·
          refine ⟨65828561201284529806386371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43885707467523019870924247 65828561201284529806386371)
          ·
            refine ⟨98742841801926794709579557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65828561201284529806386371 98742841801926794709579557)
            ·
              refine ⟨18514282837861274008046167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 98742841801926794709579557 18514282837861274008046167)
              ·
                refine ⟨27771424256791911012069251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18514282837861274008046167 27771424256791911012069251)
                ·
                  refine ⟨41657136385187866518103877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27771424256791911012069251 41657136385187866518103877)
                  ·
                    refine ⟨7810713072222724972144477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41657136385187866518103877 7810713072222724972144477)
                    ·
                      refine ⟨2929017402083521864554179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7810713072222724972144477 2929017402083521864554179)
                      ·
                        rfl

theorem cell23_5704241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 1, 1, 4, 3].length) (baseStart_5704241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5704241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5704241 prefixEnd_5704241 := by exact prefixLift 5704241
  have htrace : WordTrace (prefixWord ++ tailWord_5704241) baseStart_5704241 baseEnd_5704241 := by
    simpa [prefixWord, tailWord_5704241, baseEnd_5704241] using wordTrace_append hprefix tailTrace_5704241
  have hstable : (prefixWord ++ tailWord_5704241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5704241).length < 2 ^ (prefixWord ++ tailWord_5704241).sum := by decide
  have hdescent : baseEnd_5704241 < baseStart_5704241 := by decide
  rcases family_descends (prefixWord ++ tailWord_5704241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5704264 : List Nat := [2, 1, 3, 1, 1, 1, 1, 3, 1, 1, 8]
def baseStart_5704264 : Nat := 118140960795 + 5704264 * 2 ^ 59
def prefixEnd_5704264 : Nat := 4983230072969 + 3 ^ 40 * 5704264 * 2
def baseEnd_5704264 : Nat := 2929029212138575274566573

theorem tailTrace_5704264 : CollatzResearch.WordTrace tailWord_5704264 prefixEnd_5704264 2929029212138575274566573 := by
  unfold tailWord_5704264
  simp only [CollatzResearch.WordTrace]
  refine ⟨104025800103216606787715923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138701066804288809050287897 104025800103216606787715923)
  ·
    refine ⟨156038700154824910181573885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104025800103216606787715923 156038700154824910181573885)
    ·
      refine ⟨58514512558059341318090207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156038700154824910181573885 58514512558059341318090207)
      ·
        refine ⟨87771768837089011977135311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58514512558059341318090207 87771768837089011977135311)
        ·
          refine ⟨131657653255633517965702967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87771768837089011977135311 131657653255633517965702967)
          ·
            refine ⟨197486479883450276948554451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131657653255633517965702967 197486479883450276948554451)
            ·
              refine ⟨296229719825175415422831677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197486479883450276948554451 296229719825175415422831677)
              ·
                refine ⟨111086144934440780783561879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 296229719825175415422831677 111086144934440780783561879)
                ·
                  refine ⟨166629217401661171175342819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 111086144934440780783561879 166629217401661171175342819)
                  ·
                    refine ⟨249943826102491756763014229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 166629217401661171175342819 249943826102491756763014229)
                    ·
                      refine ⟨2929029212138575274566573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 249943826102491756763014229 2929029212138575274566573)
                      ·
                        rfl

theorem cell23_5704264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 1, 1, 8].length) (baseStart_5704264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5704264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5704264 prefixEnd_5704264 := by exact prefixLift 5704264
  have htrace : WordTrace (prefixWord ++ tailWord_5704264) baseStart_5704264 baseEnd_5704264 := by
    simpa [prefixWord, tailWord_5704264, baseEnd_5704264] using wordTrace_append hprefix tailTrace_5704264
  have hstable : (prefixWord ++ tailWord_5704264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5704264).length < 2 ^ (prefixWord ++ tailWord_5704264).sum := by decide
  have hdescent : baseEnd_5704264 < baseStart_5704264 := by decide
  rcases family_descends (prefixWord ++ tailWord_5704264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5704288 : List Nat := [2, 1, 1, 3, 2, 1, 2, 4, 3, 1, 3]
def baseStart_5704288 : Nat := 118140960795 + 5704288 * 2 ^ 59
def prefixEnd_5704288 : Nat := 4983230072969 + 3 ^ 40 * 5704288 * 2
def baseEnd_5704288 : Nat := 2929041535674283180666463

theorem tailTrace_5704288 : CollatzResearch.WordTrace tailWord_5704288 prefixEnd_5704288 2929041535674283180666463 := by
  unfold tailWord_5704288
  simp only [CollatzResearch.WordTrace]
  refine ⟨104026237779173132837152759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138701650372230843782870345 104026237779173132837152759)
  ·
    refine ⟨156039356668759699255729139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104026237779173132837152759 156039356668759699255729139)
    ·
      refine ⟨234059035003139548883593709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156039356668759699255729139 234059035003139548883593709)
      ·
        refine ⟨87772138126177330831347641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 234059035003139548883593709 87772138126177330831347641)
        ·
          refine ⟨65829103594632998123510731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87772138126177330831347641 65829103594632998123510731)
          ·
            refine ⟨98743655391949497185266097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65829103594632998123510731 98743655391949497185266097)
            ·
              refine ⟨74057741543962122888949573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98743655391949497185266097 74057741543962122888949573)
              ·
                refine ⟨13885826539492898041678045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74057741543962122888949573 13885826539492898041678045)
                ·
                  refine ⟨5207184952309836765629267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13885826539492898041678045 5207184952309836765629267)
                  ·
                    refine ⟨7810777428464755148443901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5207184952309836765629267 7810777428464755148443901)
                    ·
                      refine ⟨2929041535674283180666463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7810777428464755148443901 2929041535674283180666463)
                      ·
                        rfl

theorem cell23_5704288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 4, 3, 1, 3].length) (baseStart_5704288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5704288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5704288 prefixEnd_5704288 := by exact prefixLift 5704288
  have htrace : WordTrace (prefixWord ++ tailWord_5704288) baseStart_5704288 baseEnd_5704288 := by
    simpa [prefixWord, tailWord_5704288, baseEnd_5704288] using wordTrace_append hprefix tailTrace_5704288
  have hstable : (prefixWord ++ tailWord_5704288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5704288).length < 2 ^ (prefixWord ++ tailWord_5704288).sum := by decide
  have hdescent : baseEnd_5704288 < baseStart_5704288 := by decide
  rcases family_descends (prefixWord ++ tailWord_5704288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5704291 : List Nat := [1, 1, 1, 5, 1, 2, 3, 1, 3, 5]
def baseStart_5704291 : Nat := 118140960795 + 5704291 * 2 ^ 59
def prefixEnd_5704291 : Nat := 4983230072969 + 3 ^ 40 * 5704291 * 2
def baseEnd_5704291 : Nat := 976347692038748889642983

theorem tailTrace_5704291 : CollatzResearch.WordTrace tailWord_5704291 prefixEnd_5704291 976347692038748889642983 := by
  unfold tailWord_5704291
  simp only [CollatzResearch.WordTrace]
  refine ⟨208052584977335397186664727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138701723318223598124443151 208052584977335397186664727)
  ·
    refine ⟨312078877466003095779997091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208052584977335397186664727 312078877466003095779997091)
    ·
      refine ⟨468118316199004643669995637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312078877466003095779997091 468118316199004643669995637)
      ·
        refine ⟨43886092143656685344062091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 468118316199004643669995637 43886092143656685344062091)
        ·
          refine ⟨65829138215485028016093137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43886092143656685344062091 65829138215485028016093137)
          ·
            refine ⟨49371853661613771012069853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65829138215485028016093137 49371853661613771012069853)
            ·
              refine ⟨18514445123105164129526195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49371853661613771012069853 18514445123105164129526195)
              ·
                refine ⟨27771667684657746194289293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18514445123105164129526195 27771667684657746194289293)
                ·
                  refine ⟨10414375381746654822858485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27771667684657746194289293 10414375381746654822858485)
                  ·
                    refine ⟨976347692038748889642983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10414375381746654822858485 976347692038748889642983)
                    ·
                      rfl

theorem cell23_5704291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 1, 3, 5].length) (baseStart_5704291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5704291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5704291 prefixEnd_5704291 := by exact prefixLift 5704291
  have htrace : WordTrace (prefixWord ++ tailWord_5704291) baseStart_5704291 baseEnd_5704291 := by
    simpa [prefixWord, tailWord_5704291, baseEnd_5704291] using wordTrace_append hprefix tailTrace_5704291
  have hstable : (prefixWord ++ tailWord_5704291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5704291).length < 2 ^ (prefixWord ++ tailWord_5704291).sum := by decide
  have hdescent : baseEnd_5704291 < baseStart_5704291 := by decide
  rcases family_descends (prefixWord ++ tailWord_5704291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5704321 : List Nat := [1, 2, 4, 2, 1, 1, 1, 2, 3, 6]
def baseStart_5704321 : Nat := 118140960795 + 5704321 * 2 ^ 59
def prefixEnd_5704321 : Nat := 4983230072969 + 3 ^ 40 * 5704321 * 2
def baseEnd_5704321 : Nat := 976352826845293850517937

theorem tailTrace_5704321 : CollatzResearch.WordTrace tailWord_5704321 prefixEnd_5704321 976352826845293850517937 := by
  unfold tailWord_5704321
  simp only [CollatzResearch.WordTrace]
  refine ⟨208053679167226712310256817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138702452778151141540171211 208053679167226712310256817)
  ·
    refine ⟨156040259375420034232692613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208053679167226712310256817 156040259375420034232692613)
    ·
      refine ⟨29257548632891256418629865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 156040259375420034232692613 29257548632891256418629865)
      ·
        refine ⟨21943161474668442313972399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29257548632891256418629865 21943161474668442313972399)
        ·
          refine ⟨32914742212002663470958599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21943161474668442313972399 32914742212002663470958599)
          ·
            refine ⟨49372113318003995206437899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32914742212002663470958599 49372113318003995206437899)
            ·
              refine ⟨74058169977005992809656849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49372113318003995206437899 74058169977005992809656849)
              ·
                refine ⟨55543627482754494607242637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74058169977005992809656849 55543627482754494607242637)
                ·
                  refine ⟨20828860306032935477715989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55543627482754494607242637 20828860306032935477715989)
                  ·
                    refine ⟨976352826845293850517937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20828860306032935477715989 976352826845293850517937)
                    ·
                      rfl

theorem cell23_5704321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 2, 3, 6].length) (baseStart_5704321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5704321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5704321 prefixEnd_5704321 := by exact prefixLift 5704321
  have htrace : WordTrace (prefixWord ++ tailWord_5704321) baseStart_5704321 baseEnd_5704321 := by
    simpa [prefixWord, tailWord_5704321, baseEnd_5704321] using wordTrace_append hprefix tailTrace_5704321
  have hstable : (prefixWord ++ tailWord_5704321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5704321).length < 2 ^ (prefixWord ++ tailWord_5704321).sum := by decide
  have hdescent : baseEnd_5704321 < baseStart_5704321 := by decide
  rcases family_descends (prefixWord ++ tailWord_5704321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5704338 : List Nat := [3, 2, 3, 1, 2, 1, 1, 3, 1, 6]
def baseStart_5704338 : Nat := 118140960795 + 5704338 * 2 ^ 59
def prefixEnd_5704338 : Nat := 4983230072969 + 3 ^ 40 * 5704338 * 2
def baseEnd_5704338 : Nat := 976355736569002661680411

theorem tailTrace_5704338 : CollatzResearch.WordTrace tailWord_5704338 prefixEnd_5704338 976355736569002661680411 := by
  unfold tailWord_5704338
  simp only [CollatzResearch.WordTrace]
  refine ⟨52013574802041281053406417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138702866138776749475750445 52013574802041281053406417)
  ·
    refine ⟨39010181101530960790054813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52013574802041281053406417 39010181101530960790054813)
    ·
      refine ⟨14628817913074110296270555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39010181101530960790054813 14628817913074110296270555)
      ·
        refine ⟨21943226869611165444405833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14628817913074110296270555 21943226869611165444405833)
        ·
          refine ⟨16457420152208374083304375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21943226869611165444405833 16457420152208374083304375)
          ·
            refine ⟨24686130228312561124956563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16457420152208374083304375 24686130228312561124956563)
            ·
              refine ⟨37029195342468841687434845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24686130228312561124956563 37029195342468841687434845)
              ·
                refine ⟨13885948253425815632788067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37029195342468841687434845 13885948253425815632788067)
                ·
                  refine ⟨20828922380138723449182101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13885948253425815632788067 20828922380138723449182101)
                  ·
                    refine ⟨976355736569002661680411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20828922380138723449182101 976355736569002661680411)
                    ·
                      rfl

theorem cell23_5704338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_5704338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5704338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5704338 prefixEnd_5704338 := by exact prefixLift 5704338
  have htrace : WordTrace (prefixWord ++ tailWord_5704338) baseStart_5704338 baseEnd_5704338 := by
    simpa [prefixWord, tailWord_5704338, baseEnd_5704338] using wordTrace_append hprefix tailTrace_5704338
  have hstable : (prefixWord ++ tailWord_5704338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5704338).length < 2 ^ (prefixWord ++ tailWord_5704338).sum := by decide
  have hdescent : baseEnd_5704338 < baseStart_5704338 := by decide
  rcases family_descends (prefixWord ++ tailWord_5704338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5704345 : List Nat := [1, 2, 1, 2, 1, 2, 5, 2, 3, 2, 2]
def baseStart_5704345 : Nat := 118140960795 + 5704345 * 2 ^ 59
def prefixEnd_5704345 : Nat := 4983230072969 + 3 ^ 40 * 5704345 * 2
def baseEnd_5704345 : Nat := 2929070804071589457653701

theorem tailTrace_5704345 : CollatzResearch.WordTrace tailWord_5704345 prefixEnd_5704345 2929070804071589457653701 := by
  unfold tailWord_5704345
  simp only [CollatzResearch.WordTrace]
  refine ⟨208054554519139764409130489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138703036346093176272753659 208054554519139764409130489)
  ·
    refine ⟨156040915889354823306847867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208054554519139764409130489 156040915889354823306847867)
    ·
      refine ⟨234061373834032234960271801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156040915889354823306847867 234061373834032234960271801)
      ·
        refine ⟨175546030375524176220203851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 234061373834032234960271801 175546030375524176220203851)
        ·
          refine ⟨263319045563286264330305777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175546030375524176220203851 263319045563286264330305777)
          ·
            refine ⟨197489284172464698247729333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 263319045563286264330305777 197489284172464698247729333)
            ·
              refine ⟨18514620391168565460724625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 197489284172464698247729333 18514620391168565460724625)
              ·
                refine ⟨13885965293376424095543469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18514620391168565460724625 13885965293376424095543469)
                ·
                  refine ⟨5207236985016159035828801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13885965293376424095543469 5207236985016159035828801)
                  ·
                    refine ⟨3905427738762119276871601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5207236985016159035828801 3905427738762119276871601)
                    ·
                      refine ⟨2929070804071589457653701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3905427738762119276871601 2929070804071589457653701)
                      ·
                        rfl

theorem cell23_5704345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 2, 3, 2, 2].length) (baseStart_5704345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5704345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5704345 prefixEnd_5704345 := by exact prefixLift 5704345
  have htrace : WordTrace (prefixWord ++ tailWord_5704345) baseStart_5704345 baseEnd_5704345 := by
    simpa [prefixWord, tailWord_5704345, baseEnd_5704345] using wordTrace_append hprefix tailTrace_5704345
  have hstable : (prefixWord ++ tailWord_5704345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5704345).length < 2 ^ (prefixWord ++ tailWord_5704345).sum := by decide
  have hdescent : baseEnd_5704345 < baseStart_5704345 := by decide
  rcases family_descends (prefixWord ++ tailWord_5704345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5704359 : List Nat := [1, 1, 6, 3, 1, 2, 2, 1, 1, 5]
def baseStart_5704359 : Nat := 118140960795 + 5704359 * 2 ^ 59
def prefixEnd_5704359 : Nat := 4983230072969 + 3 ^ 40 * 5704359 * 2
def baseEnd_5704359 : Nat := 976359330933584134292879

theorem tailTrace_5704359 : CollatzResearch.WordTrace tailWord_5704359 prefixEnd_5704359 976359330933584134292879 := by
  unfold tailWord_5704359
  simp only [CollatzResearch.WordTrace]
  refine ⟨208055065141089044800140131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138703376760726029866760087 208055065141089044800140131)
  ·
    refine ⟨312082597711633567200210197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208055065141089044800140131 312082597711633567200210197)
    ·
      refine ⟨14628871767732823462509853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 312082597711633567200210197 14628871767732823462509853)
      ·
        refine ⟨5485826912899808798441195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14628871767732823462509853 5485826912899808798441195)
        ·
          refine ⟨8228740369349713197661793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5485826912899808798441195 8228740369349713197661793)
          ·
            refine ⟨6171555277012284898246345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8228740369349713197661793 6171555277012284898246345)
            ·
              refine ⟨4628666457759213673684759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6171555277012284898246345 4628666457759213673684759)
              ·
                refine ⟨6942999686638820510527139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4628666457759213673684759 6942999686638820510527139)
                ·
                  refine ⟨10414499529958230765790709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6942999686638820510527139 10414499529958230765790709)
                  ·
                    refine ⟨976359330933584134292879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10414499529958230765790709 976359330933584134292879)
                    ·
                      rfl

theorem cell23_5704359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 2, 1, 1, 5].length) (baseStart_5704359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5704359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5704359 prefixEnd_5704359 := by exact prefixLift 5704359
  have htrace : WordTrace (prefixWord ++ tailWord_5704359) baseStart_5704359 baseEnd_5704359 := by
    simpa [prefixWord, tailWord_5704359, baseEnd_5704359] using wordTrace_append hprefix tailTrace_5704359
  have hstable : (prefixWord ++ tailWord_5704359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5704359).length < 2 ^ (prefixWord ++ tailWord_5704359).sum := by decide
  have hdescent : baseEnd_5704359 < baseStart_5704359 := by decide
  rcases family_descends (prefixWord ++ tailWord_5704359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5704402 : List Nat := [3, 2, 2, 2, 4, 1, 2, 7]
def baseStart_5704402 : Nat := 118140960795 + 5704402 * 2 ^ 59
def prefixEnd_5704402 : Nat := 4983230072969 + 3 ^ 40 * 5704402 * 2
def baseEnd_5704402 : Nat := 108485187869218360542257

theorem tailTrace_5704402 : CollatzResearch.WordTrace tailWord_5704402 prefixEnd_5704402 108485187869218360542257 := by
  unfold tailWord_5704402
  simp only [CollatzResearch.WordTrace]
  refine ⟨52014158369983315785988865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138704422319955508762636973 52014158369983315785988865)
  ·
    refine ⟨39010618777487486839491649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52014158369983315785988865 39010618777487486839491649)
    ·
      refine ⟨29257964083115615129618737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39010618777487486839491649 29257964083115615129618737)
      ·
        refine ⟨21943473062336711347214053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29257964083115615129618737 21943473062336711347214053)
        ·
          refine ⟨4114401199188133377602635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21943473062336711347214053 4114401199188133377602635)
          ·
            refine ⟨6171601798782200066403953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4114401199188133377602635 6171601798782200066403953)
            ·
              refine ⟨4628701349086650049802965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6171601798782200066403953 4628701349086650049802965)
              ·
                refine ⟨108485187869218360542257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4628701349086650049802965 108485187869218360542257)
                ·
                  rfl

theorem cell23_5704402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 2, 7].length) (baseStart_5704402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5704402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5704402 prefixEnd_5704402 := by exact prefixLift 5704402
  have htrace : WordTrace (prefixWord ++ tailWord_5704402) baseStart_5704402 baseEnd_5704402 := by
    simpa [prefixWord, tailWord_5704402, baseEnd_5704402] using wordTrace_append hprefix tailTrace_5704402
  have hstable : (prefixWord ++ tailWord_5704402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5704402).length < 2 ^ (prefixWord ++ tailWord_5704402).sum := by decide
  have hdescent : baseEnd_5704402 < baseStart_5704402 := by decide
  rcases family_descends (prefixWord ++ tailWord_5704402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5704412 : List Nat := [2, 2, 5, 1, 1, 1, 1, 2, 4, 1, 3]
def baseStart_5704412 : Nat := 118140960795 + 5704412 * 2 ^ 59
def prefixEnd_5704412 : Nat := 4983230072969 + 3 ^ 40 * 5704412 * 2
def baseEnd_5704412 : Nat := 2929105207275440695515893

theorem tailTrace_5704412 : CollatzResearch.WordTrace tailWord_5704412 prefixEnd_5704412 2929105207275440695515893 := by
  unfold tailWord_5704412
  simp only [CollatzResearch.WordTrace]
  refine ⟨104028499104948517425909745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138704665473264689901212993 104028499104948517425909745)
  ·
    refine ⟨78021374328711388069432309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104028499104948517425909745 78021374328711388069432309)
    ·
      refine ⟨7314503843316692631509279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 78021374328711388069432309 7314503843316692631509279)
      ·
        refine ⟨10971755764975038947263919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7314503843316692631509279 10971755764975038947263919)
        ·
          refine ⟨16457633647462558420895879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10971755764975038947263919 16457633647462558420895879)
          ·
            refine ⟨24686450471193837631343819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16457633647462558420895879 24686450471193837631343819)
            ·
              refine ⟨37029675706790756447015729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24686450471193837631343819 37029675706790756447015729)
              ·
                refine ⟨27772256780093067335261797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37029675706790756447015729 27772256780093067335261797)
                ·
                  refine ⟨5207298146267450125361587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27772256780093067335261797 5207298146267450125361587)
                  ·
                    refine ⟨7810947219401175188042381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5207298146267450125361587 7810947219401175188042381)
                    ·
                      refine ⟨2929105207275440695515893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7810947219401175188042381 2929105207275440695515893)
                      ·
                        rfl

theorem cell23_5704412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_5704412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5704412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5704412 prefixEnd_5704412 := by exact prefixLift 5704412
  have htrace : WordTrace (prefixWord ++ tailWord_5704412) baseStart_5704412 baseEnd_5704412 := by
    simpa [prefixWord, tailWord_5704412, baseEnd_5704412] using wordTrace_append hprefix tailTrace_5704412
  have hstable : (prefixWord ++ tailWord_5704412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5704412).length < 2 ^ (prefixWord ++ tailWord_5704412).sum := by decide
  have hdescent : baseEnd_5704412 < baseStart_5704412 := by decide
  rcases family_descends (prefixWord ++ tailWord_5704412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5704438 : List Nat := [5, 1, 1, 1, 1, 2, 1, 2, 1, 3, 5]
def baseStart_5704438 : Nat := 118140960795 + 5704438 * 2 ^ 59
def prefixEnd_5704438 : Nat := 4983230072969 + 3 ^ 40 * 5704438 * 2
def baseEnd_5704438 : Nat := 2929118557772457593790773

theorem tailTrace_5704438 : CollatzResearch.WordTrace tailWord_5704438 prefixEnd_5704438 2929118557772457593790773 := by
  unfold tailWord_5704438
  simp only [CollatzResearch.WordTrace]
  refine ⟨13003621656737677580766623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 138705297671868560861510645 13003621656737677580766623)
  ·
    refine ⟨19505432485106516371149935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13003621656737677580766623 19505432485106516371149935)
    ·
      refine ⟨29258148727659774556724903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19505432485106516371149935 29258148727659774556724903)
      ·
        refine ⟨43887223091489661835087355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29258148727659774556724903 43887223091489661835087355)
        ·
          refine ⟨65830834637234492752631033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43887223091489661835087355 65830834637234492752631033)
          ·
            refine ⟨49373125977925869564473275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65830834637234492752631033 49373125977925869564473275)
            ·
              refine ⟨74059688966888804346709913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49373125977925869564473275 74059688966888804346709913)
              ·
                refine ⟨55544766725166603260032435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74059688966888804346709913 55544766725166603260032435)
                ·
                  refine ⟨83317150087749904890048653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55544766725166603260032435 83317150087749904890048653)
                  ·
                    refine ⟨31243931282906214333768245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 83317150087749904890048653 31243931282906214333768245)
                    ·
                      refine ⟨2929118557772457593790773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31243931282906214333768245 2929118557772457593790773)
                      ·
                        rfl

theorem cell23_5704438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_5704438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5704438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5704438 prefixEnd_5704438 := by exact prefixLift 5704438
  have htrace : WordTrace (prefixWord ++ tailWord_5704438) baseStart_5704438 baseEnd_5704438 := by
    simpa [prefixWord, tailWord_5704438, baseEnd_5704438] using wordTrace_append hprefix tailTrace_5704438
  have hstable : (prefixWord ++ tailWord_5704438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5704438).length < 2 ^ (prefixWord ++ tailWord_5704438).sum := by decide
  have hdescent : baseEnd_5704438 < baseStart_5704438 := by decide
  rcases family_descends (prefixWord ++ tailWord_5704438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5704446 : List Nat := [4, 2, 2, 1, 2, 3, 2, 1, 2, 1, 3]
def baseStart_5704446 : Nat := 118140960795 + 5704446 * 2 ^ 59
def prefixEnd_5704446 : Nat := 4983230072969 + 3 ^ 40 * 5704446 * 2
def baseEnd_5704446 : Nat := 2929122665617693562490737

theorem tailTrace_5704446 : CollatzResearch.WordTrace tailWord_5704446 prefixEnd_5704446 2929122665617693562490737 := by
  unfold tailWord_5704446
  simp only [CollatzResearch.WordTrace]
  refine ⟨26007279786471732332319649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138705492194515905772371461 26007279786471732332319649)
  ·
    refine ⟨19505459839853799249239737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26007279786471732332319649 19505459839853799249239737)
    ·
      refine ⟨14629094879890349436929803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19505459839853799249239737 14629094879890349436929803)
      ·
        refine ⟨21943642319835524155394705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14629094879890349436929803 21943642319835524155394705)
        ·
          refine ⟨16457731739876643116546029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21943642319835524155394705 16457731739876643116546029)
          ·
            refine ⟨6171649402453741168704761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16457731739876643116546029 6171649402453741168704761)
            ·
              refine ⟨4628737051840305876528571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6171649402453741168704761 4628737051840305876528571)
              ·
                refine ⟨6943105577760458814792857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4628737051840305876528571 6943105577760458814792857)
                ·
                  refine ⟨5207329183320344111094643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6943105577760458814792857 5207329183320344111094643)
                  ·
                    refine ⟨7810993774980516166641965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5207329183320344111094643 7810993774980516166641965)
                    ·
                      refine ⟨2929122665617693562490737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7810993774980516166641965 2929122665617693562490737)
                      ·
                        rfl

theorem cell23_5704446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 2, 1, 2, 1, 3].length) (baseStart_5704446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5704446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5704446 prefixEnd_5704446 := by exact prefixLift 5704446
  have htrace : WordTrace (prefixWord ++ tailWord_5704446) baseStart_5704446 baseEnd_5704446 := by
    simpa [prefixWord, tailWord_5704446, baseEnd_5704446] using wordTrace_append hprefix tailTrace_5704446
  have hstable : (prefixWord ++ tailWord_5704446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5704446).length < 2 ^ (prefixWord ++ tailWord_5704446).sum := by decide
  have hdescent : baseEnd_5704446 < baseStart_5704446 := by decide
  rcases family_descends (prefixWord ++ tailWord_5704446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5704498 : List Nat := [3, 2, 1, 1, 3, 1, 1, 3, 1, 2, 5]
def baseStart_5704498 : Nat := 118140960795 + 5704498 * 2 ^ 59
def prefixEnd_5704498 : Nat := 4983230072969 + 3 ^ 40 * 5704498 * 2
def baseEnd_5704498 : Nat := 2929149366611727359040497

theorem tailTrace_5704498 : CollatzResearch.WordTrace tailWord_5704498 prefixEnd_5704498 2929149366611727359040497 := by
  unfold tailWord_5704498
  simp only [CollatzResearch.WordTrace]
  refine ⟨52015033721896367884862537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138706756591723647692966765 52015033721896367884862537)
  ·
    refine ⟨39011275291422275913646903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52015033721896367884862537 39011275291422275913646903)
    ·
      refine ⟨58516912937133413870470355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39011275291422275913646903 58516912937133413870470355)
      ·
        refine ⟨87775369405700120805705533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58516912937133413870470355 87775369405700120805705533)
        ·
          refine ⟨32915763527137545302139575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87775369405700120805705533 32915763527137545302139575)
          ·
            refine ⟨49373645290706317953209363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32915763527137545302139575 49373645290706317953209363)
            ·
              refine ⟨74060467936059476929814045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49373645290706317953209363 74060467936059476929814045)
              ·
                refine ⟨27772675476022303848680267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74060467936059476929814045 27772675476022303848680267)
                ·
                  refine ⟨41659013214033455773020401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27772675476022303848680267 41659013214033455773020401)
                  ·
                    refine ⟨31244259910525091829765301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41659013214033455773020401 31244259910525091829765301)
                    ·
                      refine ⟨2929149366611727359040497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31244259910525091829765301 2929149366611727359040497)
                      ·
                        rfl

theorem cell23_5704498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 3, 1, 2, 5].length) (baseStart_5704498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5704498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5704498 prefixEnd_5704498 := by exact prefixLift 5704498
  have htrace : WordTrace (prefixWord ++ tailWord_5704498) baseStart_5704498 baseEnd_5704498 := by
    simpa [prefixWord, tailWord_5704498, baseEnd_5704498] using wordTrace_append hprefix tailTrace_5704498
  have hstable : (prefixWord ++ tailWord_5704498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5704498).length < 2 ^ (prefixWord ++ tailWord_5704498).sum := by decide
  have hdescent : baseEnd_5704498 < baseStart_5704498 := by decide
  rcases family_descends (prefixWord ++ tailWord_5704498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5704508 : List Nat := [2, 2, 2, 2, 1, 1, 1, 4, 1, 3, 4]
def baseStart_5704508 : Nat := 118140960795 + 5704508 * 2 ^ 59
def prefixEnd_5704508 : Nat := 4983230072969 + 3 ^ 40 * 5704508 * 2
def baseEnd_5704508 : Nat := 2929154501418272319915451

theorem tailTrace_5704508 : CollatzResearch.WordTrace tailWord_5704508 prefixEnd_5704508 2929154501418272319915451 := by
  unfold tailWord_5704508
  simp only [CollatzResearch.WordTrace]
  refine ⟨104030249808774621623657089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138706999745032828831542785 104030249808774621623657089)
  ·
    refine ⟨78022687356580966217742817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104030249808774621623657089 78022687356580966217742817)
    ·
      refine ⟨58517015517435724663307113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78022687356580966217742817 58517015517435724663307113)
      ·
        refine ⟨43887761638076793497480335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58517015517435724663307113 43887761638076793497480335)
        ·
          refine ⟨65831642457115190246220503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43887761638076793497480335 65831642457115190246220503)
          ·
            refine ⟨98747463685672785369330755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65831642457115190246220503 98747463685672785369330755)
            ·
              refine ⟨148121195528509178053996133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98747463685672785369330755 148121195528509178053996133)
              ·
                refine ⟨27772724161595470885124275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 148121195528509178053996133 27772724161595470885124275)
                ·
                  refine ⟨41659086242393206327686413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27772724161595470885124275 41659086242393206327686413)
                  ·
                    refine ⟨15622157340897452372882405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41659086242393206327686413 15622157340897452372882405)
                    ·
                      refine ⟨2929154501418272319915451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15622157340897452372882405 2929154501418272319915451)
                      ·
                        rfl

theorem cell23_5704508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 4, 1, 3, 4].length) (baseStart_5704508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5704508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5704508 prefixEnd_5704508 := by exact prefixLift 5704508
  have htrace : WordTrace (prefixWord ++ tailWord_5704508) baseStart_5704508 baseEnd_5704508 := by
    simpa [prefixWord, tailWord_5704508, baseEnd_5704508] using wordTrace_append hprefix tailTrace_5704508
  have hstable : (prefixWord ++ tailWord_5704508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5704508).length < 2 ^ (prefixWord ++ tailWord_5704508).sum := by decide
  have hdescent : baseEnd_5704508 < baseStart_5704508 := by decide
  rcases family_descends (prefixWord ++ tailWord_5704508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5704538 : List Nat := [3, 1, 1, 2, 1, 4, 1, 1, 2, 1, 6]
def baseStart_5704538 : Nat := 118140960795 + 5704538 * 2 ^ 59
def prefixEnd_5704538 : Nat := 4983230072969 + 3 ^ 40 * 5704538 * 2
def baseEnd_5704538 : Nat := 2929169905837907202540313

theorem tailTrace_5704538 : CollatzResearch.WordTrace tailWord_5704538 prefixEnd_5704538 2929169905837907202540313 := by
  unfold tailWord_5704538
  simp only [CollatzResearch.WordTrace]
  refine ⟨52015398451860139592726567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138707729204960372247270845 52015398451860139592726567)
  ·
    refine ⟨78023097677790209389089851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52015398451860139592726567 78023097677790209389089851)
    ·
      refine ⟨117034646516685314083634777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78023097677790209389089851 117034646516685314083634777)
      ·
        refine ⟨87775984887513985562726083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117034646516685314083634777 87775984887513985562726083)
        ·
          refine ⟨131663977331270978344089125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87775984887513985562726083 131663977331270978344089125)
          ·
            refine ⟨24686995749613308439516711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 131663977331270978344089125 24686995749613308439516711)
            ·
              refine ⟨37030493624419962659275067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24686995749613308439516711 37030493624419962659275067)
              ·
                refine ⟨55545740436629943988912601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37030493624419962659275067 55545740436629943988912601)
                ·
                  refine ⟨41659305327472457991684451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55545740436629943988912601 41659305327472457991684451)
                  ·
                    refine ⟨62488957991208686987526677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41659305327472457991684451 62488957991208686987526677)
                    ·
                      refine ⟨2929169905837907202540313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62488957991208686987526677 2929169905837907202540313)
                      ·
                        rfl

theorem cell23_5704538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 1, 2, 1, 6].length) (baseStart_5704538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5704538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5704538 prefixEnd_5704538 := by exact prefixLift 5704538
  have htrace : WordTrace (prefixWord ++ tailWord_5704538) baseStart_5704538 baseEnd_5704538 := by
    simpa [prefixWord, tailWord_5704538, baseEnd_5704538] using wordTrace_append hprefix tailTrace_5704538
  have hstable : (prefixWord ++ tailWord_5704538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5704538).length < 2 ^ (prefixWord ++ tailWord_5704538).sum := by decide
  have hdescent : baseEnd_5704538 < baseStart_5704538 := by decide
  rcases family_descends (prefixWord ++ tailWord_5704538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5704552 : List Nat := [2, 1, 4, 2, 1, 3, 2, 1, 3, 4]
def baseStart_5704552 : Nat := 118140960795 + 5704552 * 2 ^ 59
def prefixEnd_5704552 : Nat := 4983230072969 + 3 ^ 40 * 5704552 * 2
def baseEnd_5704552 : Nat := 976392364855690049255083

theorem tailTrace_5704552 : CollatzResearch.WordTrace tailWord_5704552 prefixEnd_5704552 976392364855690049255083 := by
  unfold tailWord_5704552
  simp only [CollatzResearch.WordTrace]
  refine ⟨104031052214694919380957955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138708069619593225841277273 104031052214694919380957955)
  ·
    refine ⟨156046578322042379071436933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104031052214694919380957955 156046578322042379071436933)
    ·
      refine ⟨29258733435382946075894425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 156046578322042379071436933 29258733435382946075894425)
      ·
        refine ⟨21944050076537209556920819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29258733435382946075894425 21944050076537209556920819)
        ·
          refine ⟨32916075114805814335381229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21944050076537209556920819 32916075114805814335381229)
          ·
            refine ⟨12343528168052180375767961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32916075114805814335381229 12343528168052180375767961)
            ·
              refine ⟨9257646126039135281825971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12343528168052180375767961 9257646126039135281825971)
              ·
                refine ⟨13886469189058702922738957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9257646126039135281825971 13886469189058702922738957)
                ·
                  refine ⟨5207425945897013596027109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13886469189058702922738957 5207425945897013596027109)
                  ·
                    refine ⟨976392364855690049255083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5207425945897013596027109 976392364855690049255083)
                    ·
                      rfl

theorem cell23_5704552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 1, 3, 4].length) (baseStart_5704552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5704552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5704552 prefixEnd_5704552 := by exact prefixLift 5704552
  have htrace : WordTrace (prefixWord ++ tailWord_5704552) baseStart_5704552 baseEnd_5704552 := by
    simpa [prefixWord, tailWord_5704552, baseEnd_5704552] using wordTrace_append hprefix tailTrace_5704552
  have hstable : (prefixWord ++ tailWord_5704552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5704552).length < 2 ^ (prefixWord ++ tailWord_5704552).sum := by decide
  have hdescent : baseEnd_5704552 < baseStart_5704552 := by decide
  rcases family_descends (prefixWord ++ tailWord_5704552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5704586 : List Nat := [3, 1, 2, 4, 1, 3, 1, 3, 1, 4]
def baseStart_5704586 : Nat := 118140960795 + 5704586 * 2 ^ 59
def prefixEnd_5704586 : Nat := 4983230072969 + 3 ^ 40 * 5704586 * 2
def baseEnd_5704586 : Nat := 976398184303107671580031

theorem tailTrace_5704586 : CollatzResearch.WordTrace tailWord_5704586 prefixEnd_5704586 976398184303107671580031 := by
  unfold tailWord_5704586
  simp only [CollatzResearch.WordTrace]
  refine ⟨52015836127816665642163403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138708896340844441712435741 52015836127816665642163403)
  ·
    refine ⟨78023754191724998463245105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52015836127816665642163403 78023754191724998463245105)
    ·
      refine ⟨58517815643793748847433829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78023754191724998463245105 58517815643793748847433829)
      ·
        refine ⟨10972090433211327908893843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58517815643793748847433829 10972090433211327908893843)
        ·
          refine ⟨16458135649816991863340765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10972090433211327908893843 16458135649816991863340765)
          ·
            refine ⟨6171800868681371948752787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16458135649816991863340765 6171800868681371948752787)
            ·
              refine ⟨9257701303022057923129181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6171800868681371948752787 9257701303022057923129181)
              ·
                refine ⟨3471637988633271721173443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9257701303022057923129181 3471637988633271721173443)
                ·
                  refine ⟨5207456982949907581760165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3471637988633271721173443 5207456982949907581760165)
                  ·
                    refine ⟨976398184303107671580031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5207456982949907581760165 976398184303107671580031)
                    ·
                      rfl

theorem cell23_5704586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 3, 1, 4].length) (baseStart_5704586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5704586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5704586 prefixEnd_5704586 := by exact prefixLift 5704586
  have htrace : WordTrace (prefixWord ++ tailWord_5704586) baseStart_5704586 baseEnd_5704586 := by
    simpa [prefixWord, tailWord_5704586, baseEnd_5704586] using wordTrace_append hprefix tailTrace_5704586
  have hstable : (prefixWord ++ tailWord_5704586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5704586).length < 2 ^ (prefixWord ++ tailWord_5704586).sum := by decide
  have hdescent : baseEnd_5704586 < baseStart_5704586 := by decide
  rcases family_descends (prefixWord ++ tailWord_5704586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5704609 : List Nat := [1, 2, 3, 4, 1, 1, 3, 1, 3, 1, 3]
def baseStart_5704609 : Nat := 118140960795 + 5704609 * 2 ^ 59
def prefixEnd_5704609 : Nat := 4983230072969 + 3 ^ 40 * 5704609 * 2
def baseEnd_5704609 : Nat := 2929206362964376424752487

theorem tailTrace_5704609 : CollatzResearch.WordTrace tailWord_5704609 prefixEnd_5704609 2929206362964376424752487 := by
  unfold tailWord_5704609
  simp only [CollatzResearch.WordTrace]
  refine ⟨208064183390183337496740881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138709455593455558331160587 208064183390183337496740881)
  ·
    refine ⟨156048137542637503122555661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208064183390183337496740881 156048137542637503122555661)
    ·
      refine ⟨58518051578489063670958373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156048137542637503122555661 58518051578489063670958373)
      ·
        refine ⟨10972134670966699438304695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58518051578489063670958373 10972134670966699438304695)
        ·
          refine ⟨16458202006450049157457043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10972134670966699438304695 16458202006450049157457043)
          ·
            refine ⟨24687303009675073736185565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16458202006450049157457043 24687303009675073736185565)
            ·
              refine ⟨9257738628628152651069587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24687303009675073736185565 9257738628628152651069587)
              ·
                refine ⟨13886607942942228976604381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9257738628628152651069587 13886607942942228976604381)
                ·
                  refine ⟨5207477978603335866226643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13886607942942228976604381 5207477978603335866226643)
                  ·
                    refine ⟨7811216967905003799339965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5207477978603335866226643 7811216967905003799339965)
                    ·
                      refine ⟨2929206362964376424752487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7811216967905003799339965 2929206362964376424752487)
                      ·
                        rfl

theorem cell23_5704609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_5704609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5704609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5704609 prefixEnd_5704609 := by exact prefixLift 5704609
  have htrace : WordTrace (prefixWord ++ tailWord_5704609) baseStart_5704609 baseEnd_5704609 := by
    simpa [prefixWord, tailWord_5704609, baseEnd_5704609] using wordTrace_append hprefix tailTrace_5704609
  have hstable : (prefixWord ++ tailWord_5704609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5704609).length < 2 ^ (prefixWord ++ tailWord_5704609).sum := by decide
  have hdescent : baseEnd_5704609 < baseStart_5704609 := by decide
  rcases family_descends (prefixWord ++ tailWord_5704609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5704632 : List Nat := [2, 1, 2, 1, 2, 4, 3, 2, 1, 1, 4]
def baseStart_5704632 : Nat := 118140960795 + 5704632 * 2 ^ 59
def prefixEnd_5704632 : Nat := 4983230072969 + 3 ^ 40 * 5704632 * 2
def baseEnd_5704632 : Nat := 2929218173019429834764881

theorem tailTrace_5704632 : CollatzResearch.WordTrace tailWord_5704632 prefixEnd_5704632 2929218173019429834764881 := by
  unfold tailWord_5704632
  simp only [CollatzResearch.WordTrace]
  refine ⟨104032511134550006212414075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138710014846066674949885433 104032511134550006212414075)
  ·
    refine ⟨156048766701825009318621113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104032511134550006212414075 156048766701825009318621113)
    ·
      refine ⟨117036575026368756988965835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156048766701825009318621113 117036575026368756988965835)
      ·
        refine ⟨175554862539553135483448753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117036575026368756988965835 175554862539553135483448753)
        ·
          refine ⟨131666146904664851612586565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175554862539553135483448753 131666146904664851612586565)
          ·
            refine ⟨24687402544624659677359981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 131666146904664851612586565 24687402544624659677359981)
            ·
              refine ⟨9257775954234247379009993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24687402544624659677359981 9257775954234247379009993)
              ·
                refine ⟨6943331965675685534257495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9257775954234247379009993 6943331965675685534257495)
                ·
                  refine ⟨10414997948513528301386243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6943331965675685534257495 10414997948513528301386243)
                  ·
                    refine ⟨15622496922770292452079365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10414997948513528301386243 15622496922770292452079365)
                    ·
                      refine ⟨2929218173019429834764881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15622496922770292452079365 2929218173019429834764881)
                      ·
                        rfl

theorem cell23_5704632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 2, 1, 1, 4].length) (baseStart_5704632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5704632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5704632 prefixEnd_5704632 := by exact prefixLift 5704632
  have htrace : WordTrace (prefixWord ++ tailWord_5704632) baseStart_5704632 baseEnd_5704632 := by
    simpa [prefixWord, tailWord_5704632, baseEnd_5704632] using wordTrace_append hprefix tailTrace_5704632
  have hstable : (prefixWord ++ tailWord_5704632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5704632).length < 2 ^ (prefixWord ++ tailWord_5704632).sum := by decide
  have hdescent : baseEnd_5704632 < baseStart_5704632 := by decide
  rcases family_descends (prefixWord ++ tailWord_5704632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5704682 : List Nat := [3, 1, 3, 1, 2, 2, 1, 3, 1, 3, 3]
def baseStart_5704682 : Nat := 118140960795 + 5704682 * 2 ^ 59
def prefixEnd_5704682 : Nat := 4983230072969 + 3 ^ 40 * 5704682 * 2
def baseEnd_5704682 : Nat := 2929243847052154639139651

theorem tailTrace_5704682 : CollatzResearch.WordTrace tailWord_5704682 prefixEnd_5704682 2929243847052154639139651 := by
  unfold tailWord_5704682
  simp only [CollatzResearch.WordTrace]
  refine ⟨52016711479729717741037075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138711230612612580642765533 52016711479729717741037075)
  ·
    refine ⟨78025067219594576611555613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52016711479729717741037075 78025067219594576611555613)
    ·
      refine ⟨29259400207347966229333355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78025067219594576611555613 29259400207347966229333355)
      ·
        refine ⟨43889100311021949344000033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29259400207347966229333355 43889100311021949344000033)
        ·
          refine ⟨32916825233266462008000025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43889100311021949344000033 32916825233266462008000025)
          ·
            refine ⟨24687618924949846506000019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32916825233266462008000025 24687618924949846506000019)
            ·
              refine ⟨37031428387424769759000029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24687618924949846506000019 37031428387424769759000029)
              ·
                refine ⟨13886785645284288659625011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37031428387424769759000029 13886785645284288659625011)
                ·
                  refine ⟨20830178467926432989437517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13886785645284288659625011 20830178467926432989437517)
                  ·
                    refine ⟨7811316925472412371039069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20830178467926432989437517 7811316925472412371039069)
                    ·
                      refine ⟨2929243847052154639139651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7811316925472412371039069 2929243847052154639139651)
                      ·
                        rfl

theorem cell23_5704682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 3, 1, 3, 3].length) (baseStart_5704682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5704682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5704682 prefixEnd_5704682 := by exact prefixLift 5704682
  have htrace : WordTrace (prefixWord ++ tailWord_5704682) baseStart_5704682 baseEnd_5704682 := by
    simpa [prefixWord, tailWord_5704682, baseEnd_5704682] using wordTrace_append hprefix tailTrace_5704682
  have hstable : (prefixWord ++ tailWord_5704682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5704682).length < 2 ^ (prefixWord ++ tailWord_5704682).sum := by decide
  have hdescent : baseEnd_5704682 < baseStart_5704682 := by decide
  rcases family_descends (prefixWord ++ tailWord_5704682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5704709 : List Nat := [1, 3, 1, 1, 2, 3, 3, 3, 1, 3, 2]
def baseStart_5704709 : Nat := 118140960795 + 5704709 * 2 ^ 59
def prefixEnd_5704709 : Nat := 4983230072969 + 3 ^ 40 * 5704709 * 2
def baseEnd_5704709 : Nat := 2929257711029826033502027

theorem tailTrace_5704709 : CollatzResearch.WordTrace tailWord_5704709 prefixEnd_5704709 2929257711029826033502027 := by
  unfold tailWord_5704709
  simp only [CollatzResearch.WordTrace]
  refine ⟨208067830689821054575381181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138711887126547369716920787 208067830689821054575381181)
  ·
    refine ⟨78025436508682895465767943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208067830689821054575381181 78025436508682895465767943)
    ·
      refine ⟨117038154763024343198651915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78025436508682895465767943 117038154763024343198651915)
      ·
        refine ⟨175557232144536514797977873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117038154763024343198651915 175557232144536514797977873)
        ·
          refine ⟨131667924108402386098483405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175557232144536514797977873 131667924108402386098483405)
          ·
            refine ⟨49375471540650894786931277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 131667924108402386098483405 49375471540650894786931277)
            ·
              refine ⟨18515801827744085545099229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49375471540650894786931277 18515801827744085545099229)
              ·
                refine ⟨6943425685404032079412211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18515801827744085545099229 6943425685404032079412211)
                ·
                  refine ⟨10415138528106048119118317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6943425685404032079412211 10415138528106048119118317)
                  ·
                    refine ⟨3905676948039768044669369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10415138528106048119118317 3905676948039768044669369)
                    ·
                      refine ⟨2929257711029826033502027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3905676948039768044669369 2929257711029826033502027)
                      ·
                        rfl

theorem cell23_5704709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 3, 1, 3, 2].length) (baseStart_5704709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5704709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5704709 prefixEnd_5704709 := by exact prefixLift 5704709
  have htrace : WordTrace (prefixWord ++ tailWord_5704709) baseStart_5704709 baseEnd_5704709 := by
    simpa [prefixWord, tailWord_5704709, baseEnd_5704709] using wordTrace_append hprefix tailTrace_5704709
  have hstable : (prefixWord ++ tailWord_5704709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5704709).length < 2 ^ (prefixWord ++ tailWord_5704709).sum := by decide
  have hdescent : baseEnd_5704709 < baseStart_5704709 := by decide
  rcases family_descends (prefixWord ++ tailWord_5704709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5704715 : List Nat := [1, 1, 1, 1, 6, 2, 1, 2, 2, 6]
def baseStart_5704715 : Nat := 118140960795 + 5704715 * 2 ^ 59
def prefixEnd_5704715 : Nat := 4983230072969 + 3 ^ 40 * 5704715 * 2
def baseEnd_5704715 : Nat := 976420263971251003342333

theorem tailTrace_5704715 : CollatzResearch.WordTrace tailWord_5704715 prefixEnd_5704715 976420263971251003342333 := by
  unfold tailWord_5704715
  simp only [CollatzResearch.WordTrace]
  refine ⟨208068049527799317600099599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138712033018532878400066399 208068049527799317600099599)
  ·
    refine ⟨312102074291698976400149399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208068049527799317600099599 312102074291698976400149399)
    ·
      refine ⟨468153111437548464600224099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312102074291698976400149399 468153111437548464600224099)
      ·
        refine ⟨702229667156322696900336149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 468153111437548464600224099 702229667156322696900336149)
        ·
          refine ⟨32917015647952626417203257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 702229667156322696900336149 32917015647952626417203257)
          ·
            refine ⟨24687761735964469812902443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32917015647952626417203257 24687761735964469812902443)
            ·
              refine ⟨37031642603946704719353665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24687761735964469812902443 37031642603946704719353665)
              ·
                refine ⟨27773731952960028539515249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37031642603946704719353665 27773731952960028539515249)
                ·
                  refine ⟨20830298964720021404636437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27773731952960028539515249 20830298964720021404636437)
                  ·
                    refine ⟨976420263971251003342333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20830298964720021404636437 976420263971251003342333)
                    ·
                      rfl

theorem cell23_5704715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 2, 2, 6].length) (baseStart_5704715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5704715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5704715 prefixEnd_5704715 := by exact prefixLift 5704715
  have htrace : WordTrace (prefixWord ++ tailWord_5704715) baseStart_5704715 baseEnd_5704715 := by
    simpa [prefixWord, tailWord_5704715, baseEnd_5704715] using wordTrace_append hprefix tailTrace_5704715
  have hstable : (prefixWord ++ tailWord_5704715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5704715).length < 2 ^ (prefixWord ++ tailWord_5704715).sum := by decide
  have hdescent : baseEnd_5704715 < baseStart_5704715 := by decide
  rcases family_descends (prefixWord ++ tailWord_5704715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5704716 : List Nat := [2, 2, 1, 2, 3, 4, 1, 2, 2, 1, 3]
def baseStart_5704716 : Nat := 118140960795 + 5704716 * 2 ^ 59
def prefixEnd_5704716 : Nat := 4983230072969 + 3 ^ 40 * 5704716 * 2
def baseEnd_5704716 : Nat := 2929261305394407506114495

theorem tailTrace_5704716 : CollatzResearch.WordTrace tailWord_5704716 prefixEnd_5704716 2929261305394407506114495 := by
  unfold tailWord_5704716
  simp only [CollatzResearch.WordTrace]
  refine ⟨104034043000397847385443001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138712057333863796513924001 104034043000397847385443001)
  ·
    refine ⟨78025532250298385539082251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104034043000397847385443001 78025532250298385539082251)
    ·
      refine ⟨117038298375447578308623377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78025532250298385539082251 117038298375447578308623377)
      ·
        refine ⟨87778723781585683731467533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117038298375447578308623377 87778723781585683731467533)
        ·
          refine ⟨32917021418094631399300325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87778723781585683731467533 32917021418094631399300325)
          ·
            refine ⟨6171941515892743387368811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32917021418094631399300325 6171941515892743387368811)
            ·
              refine ⟨9257912273839115081053217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6171941515892743387368811 9257912273839115081053217)
              ·
                refine ⟨6943434205379336310789913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9257912273839115081053217 6943434205379336310789913)
                ·
                  refine ⟨5207575654034502233092435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6943434205379336310789913 5207575654034502233092435)
                  ·
                    refine ⟨7811363481051753349638653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5207575654034502233092435 7811363481051753349638653)
                    ·
                      refine ⟨2929261305394407506114495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7811363481051753349638653 2929261305394407506114495)
                      ·
                        rfl

theorem cell23_5704716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 2, 2, 1, 3].length) (baseStart_5704716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5704716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5704716 prefixEnd_5704716 := by exact prefixLift 5704716
  have htrace : WordTrace (prefixWord ++ tailWord_5704716) baseStart_5704716 baseEnd_5704716 := by
    simpa [prefixWord, tailWord_5704716, baseEnd_5704716] using wordTrace_append hprefix tailTrace_5704716
  have hstable : (prefixWord ++ tailWord_5704716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5704716).length < 2 ^ (prefixWord ++ tailWord_5704716).sum := by decide
  have hdescent : baseEnd_5704716 < baseStart_5704716 := by decide
  rcases family_descends (prefixWord ++ tailWord_5704716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5704733 : List Nat := [1, 4, 2, 2, 3, 1, 3, 1, 2, 1, 3]
def baseStart_5704733 : Nat := 118140960795 + 5704733 * 2 ^ 59
def prefixEnd_5704733 : Nat := 4983230072969 + 3 ^ 40 * 5704733 * 2
def baseEnd_5704733 : Nat := 2929270034565533939601917

theorem tailTrace_5704733 : CollatzResearch.WordTrace tailWord_5704733 prefixEnd_5704733 2929270034565533939601917 := by
  unfold tailWord_5704733
  simp only [CollatzResearch.WordTrace]
  refine ⟨208068706041734106674254853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138712470694489404449503235 208068706041734106674254853)
  ·
    refine ⟨39012882382825145001422785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 208068706041734106674254853 39012882382825145001422785)
    ·
      refine ⟨29259661787118858751067089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39012882382825145001422785 29259661787118858751067089)
      ·
        refine ⟨21944746340339144063300317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29259661787118858751067089 21944746340339144063300317)
        ·
          refine ⟨8229279877627179023737619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21944746340339144063300317 8229279877627179023737619)
          ·
            refine ⟨12343919816440768535606429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8229279877627179023737619 12343919816440768535606429)
            ·
              refine ⟨4628969931165288200852411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12343919816440768535606429 4628969931165288200852411)
              ·
                refine ⟨6943454896747932301278617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4628969931165288200852411 6943454896747932301278617)
                ·
                  refine ⟨5207591172560949225958963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6943454896747932301278617 5207591172560949225958963)
                  ·
                    refine ⟨7811386758841423838938445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5207591172560949225958963 7811386758841423838938445)
                    ·
                      refine ⟨2929270034565533939601917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7811386758841423838938445 2929270034565533939601917)
                      ·
                        rfl

theorem cell23_5704733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 3, 1, 2, 1, 3].length) (baseStart_5704733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5704733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5704733 prefixEnd_5704733 := by exact prefixLift 5704733
  have htrace : WordTrace (prefixWord ++ tailWord_5704733) baseStart_5704733 baseEnd_5704733 := by
    simpa [prefixWord, tailWord_5704733, baseEnd_5704733] using wordTrace_append hprefix tailTrace_5704733
  have hstable : (prefixWord ++ tailWord_5704733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5704733).length < 2 ^ (prefixWord ++ tailWord_5704733).sum := by decide
  have hdescent : baseEnd_5704733 < baseStart_5704733 := by decide
  rcases family_descends (prefixWord ++ tailWord_5704733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5704739 : List Nat := [1, 1, 1, 4, 3, 2, 3, 1, 1, 4, 2]
def baseStart_5704739 : Nat := 118140960795 + 5704739 * 2 ^ 59
def prefixEnd_5704739 : Nat := 4983230072969 + 3 ^ 40 * 5704739 * 2
def baseEnd_5704739 : Nat := 2929273115449460916126889

theorem tailTrace_5704739 : CollatzResearch.WordTrace tailWord_5704739 prefixEnd_5704739 2929273115449460916126889 := by
  unfold tailWord_5704739
  simp only [CollatzResearch.WordTrace]
  refine ⟨208068924879712369698973271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138712616586474913132648847 208068924879712369698973271)
  ·
    refine ⟨312103387319568554548459907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208068924879712369698973271 312103387319568554548459907)
    ·
      refine ⟨468155080979352831822689861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312103387319568554548459907 468155080979352831822689861)
      ·
        refine ⟨87779077683628655966754349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 468155080979352831822689861 87779077683628655966754349)
        ·
          refine ⟨32917154131360745987532881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87779077683628655966754349 32917154131360745987532881)
          ·
            refine ⟨24687865598520559490649661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32917154131360745987532881 24687865598520559490649661)
            ·
              refine ⟨9257949599445209808993623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24687865598520559490649661 9257949599445209808993623)
              ·
                refine ⟨13886924399167814713490435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9257949599445209808993623 13886924399167814713490435)
                ·
                  refine ⟨20830386598751722070235653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13886924399167814713490435 20830386598751722070235653)
                  ·
                    refine ⟨3905697487265947888169185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20830386598751722070235653 3905697487265947888169185)
                    ·
                      refine ⟨2929273115449460916126889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3905697487265947888169185 2929273115449460916126889)
                      ·
                        rfl

theorem cell23_5704739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 1, 1, 4, 2].length) (baseStart_5704739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5704739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5704739 prefixEnd_5704739 := by exact prefixLift 5704739
  have htrace : WordTrace (prefixWord ++ tailWord_5704739) baseStart_5704739 baseEnd_5704739 := by
    simpa [prefixWord, tailWord_5704739, baseEnd_5704739] using wordTrace_append hprefix tailTrace_5704739
  have hstable : (prefixWord ++ tailWord_5704739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5704739).length < 2 ^ (prefixWord ++ tailWord_5704739).sum := by decide
  have hdescent : baseEnd_5704739 < baseStart_5704739 := by decide
  rcases family_descends (prefixWord ++ tailWord_5704739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5704743 : List Nat := [1, 1, 7, 1, 1, 2, 2, 2, 1, 3, 2]
def baseStart_5704743 : Nat := 118140960795 + 5704743 * 2 ^ 59
def prefixEnd_5704743 : Nat := 4983230072969 + 3 ^ 40 * 5704743 * 2
def baseEnd_5704743 : Nat := 2929275169372078900476871

theorem tailTrace_5704743 : CollatzResearch.WordTrace tailWord_5704743 prefixEnd_5704743 2929275169372078900476871 := by
  unfold tailWord_5704743
  simp only [CollatzResearch.WordTrace]
  refine ⟨208069070771697878382118883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138712713847798585588079255 208069070771697878382118883)
  ·
    refine ⟨312103606157546817573178325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208069070771697878382118883 312103606157546817573178325)
    ·
      refine ⟨7314928269317503536871367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 312103606157546817573178325 7314928269317503536871367)
      ·
        refine ⟨10972392403976255305307051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7314928269317503536871367 10972392403976255305307051)
        ·
          refine ⟨16458588605964382957960577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10972392403976255305307051 16458588605964382957960577)
          ·
            refine ⟨12343941454473287218470433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16458588605964382957960577 12343941454473287218470433)
            ·
              refine ⟨9257956090854965413852825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12343941454473287218470433 9257956090854965413852825)
              ·
                refine ⟨6943467068141224060389619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9257956090854965413852825 6943467068141224060389619)
                ·
                  refine ⟨10415200602211836090584429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6943467068141224060389619 10415200602211836090584429)
                  ·
                    refine ⟨3905700225829438533969161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10415200602211836090584429 3905700225829438533969161)
                    ·
                      refine ⟨2929275169372078900476871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3905700225829438533969161 2929275169372078900476871)
                      ·
                        rfl

theorem cell23_5704743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 2, 1, 3, 2].length) (baseStart_5704743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5704743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5704743 prefixEnd_5704743 := by exact prefixLift 5704743
  have htrace : WordTrace (prefixWord ++ tailWord_5704743) baseStart_5704743 baseEnd_5704743 := by
    simpa [prefixWord, tailWord_5704743, baseEnd_5704743] using wordTrace_append hprefix tailTrace_5704743
  have hstable : (prefixWord ++ tailWord_5704743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5704743).length < 2 ^ (prefixWord ++ tailWord_5704743).sum := by decide
  have hdescent : baseEnd_5704743 < baseStart_5704743 := by decide
  rcases family_descends (prefixWord ++ tailWord_5704743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5704785 : List Nat := [1, 2, 2, 1, 3, 1, 3, 1, 1, 1, 7]
def baseStart_5704785 : Nat := 118140960795 + 5704785 * 2 ^ 59
def prefixEnd_5704785 : Nat := 4983230072969 + 3 ^ 40 * 5704785 * 2
def baseEnd_5704785 : Nat := 2929296735559567736151677

theorem tailTrace_5704785 : CollatzResearch.WordTrace tailWord_5704785 prefixEnd_5704785 2929296735559567736151677 := by
  unfold tailWord_5704785
  simp only [CollatzResearch.WordTrace]
  refine ⟨208070602637545719555147809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138713735091697146370098539 208070602637545719555147809)
  ·
    refine ⟨156052951978159289666360857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208070602637545719555147809 156052951978159289666360857)
    ·
      refine ⟨117039713983619467249770643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156052951978159289666360857 117039713983619467249770643)
      ·
        refine ⟨175559570975429200874655965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117039713983619467249770643 175559570975429200874655965)
        ·
          refine ⟨65834839115785950327995987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 175559570975429200874655965 65834839115785950327995987)
          ·
            refine ⟨98752258673678925491993981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65834839115785950327995987 98752258673678925491993981)
            ·
              refine ⟨37032097002629597059497743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 98752258673678925491993981 37032097002629597059497743)
              ·
                refine ⟨55548145503944395589246615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37032097002629597059497743 55548145503944395589246615)
                ·
                  refine ⟨83322218255916593383869923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55548145503944395589246615 83322218255916593383869923)
                  ·
                    refine ⟨124983327383874890075804885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 83322218255916593383869923 124983327383874890075804885)
                    ·
                      refine ⟨2929296735559567736151677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 124983327383874890075804885 2929296735559567736151677)
                      ·
                        rfl

theorem cell23_5704785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 1, 1, 1, 7].length) (baseStart_5704785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5704785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5704785 prefixEnd_5704785 := by exact prefixLift 5704785
  have htrace : WordTrace (prefixWord ++ tailWord_5704785) baseStart_5704785 baseEnd_5704785 := by
    simpa [prefixWord, tailWord_5704785, baseEnd_5704785] using wordTrace_append hprefix tailTrace_5704785
  have hstable : (prefixWord ++ tailWord_5704785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5704785).length < 2 ^ (prefixWord ++ tailWord_5704785).sum := by decide
  have hdescent : baseEnd_5704785 < baseStart_5704785 := by decide
  rcases family_descends (prefixWord ++ tailWord_5704785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5704829 : List Nat := [1, 4, 1, 1, 3, 1, 2, 2, 2, 4, 2]
def baseStart_5704829 : Nat := 118140960795 + 5704829 * 2 ^ 59
def prefixEnd_5704829 : Nat := 4983230072969 + 3 ^ 40 * 5704829 * 2
def baseEnd_5704829 : Nat := 2929319328708365564001475

theorem tailTrace_5704829 : CollatzResearch.WordTrace tailWord_5704829 prefixEnd_5704829 2929319328708365564001475 := by
  unfold tailWord_5704829
  simp only [CollatzResearch.WordTrace]
  refine ⟨208072207449386315069749541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138714804966257543379833027 208072207449386315069749541)
  ·
    refine ⟨39013538896759934075578039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 208072207449386315069749541 39013538896759934075578039)
    ·
      refine ⟨58520308345139901113367059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39013538896759934075578039 58520308345139901113367059)
      ·
        refine ⟨87780462517709851670050589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58520308345139901113367059 87780462517709851670050589)
        ·
          refine ⟨32917673444141194376268971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87780462517709851670050589 32917673444141194376268971)
          ·
            refine ⟨49376510166211791564403457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32917673444141194376268971 49376510166211791564403457)
            ·
              refine ⟨37032382624658843673302593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49376510166211791564403457 37032382624658843673302593)
              ·
                refine ⟨27774286968494132754976945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37032382624658843673302593 27774286968494132754976945)
                ·
                  refine ⟨20830715226370599566232709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27774286968494132754976945 20830715226370599566232709)
                  ·
                    refine ⟨3905759104944487418668633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20830715226370599566232709 3905759104944487418668633)
                    ·
                      refine ⟨2929319328708365564001475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3905759104944487418668633 2929319328708365564001475)
                      ·
                        rfl

theorem cell23_5704829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 2, 2, 4, 2].length) (baseStart_5704829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5704829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5704829 prefixEnd_5704829 := by exact prefixLift 5704829
  have htrace : WordTrace (prefixWord ++ tailWord_5704829) baseStart_5704829 baseEnd_5704829 := by
    simpa [prefixWord, tailWord_5704829, baseEnd_5704829] using wordTrace_append hprefix tailTrace_5704829
  have hstable : (prefixWord ++ tailWord_5704829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5704829).length < 2 ^ (prefixWord ++ tailWord_5704829).sum := by decide
  have hdescent : baseEnd_5704829 < baseStart_5704829 := by decide
  rcases family_descends (prefixWord ++ tailWord_5704829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5704830 : List Nat := [4, 2, 4, 1, 1, 1, 1, 4, 5]
def baseStart_5704830 : Nat := 118140960795 + 5704830 * 2 ^ 59
def prefixEnd_5704830 : Nat := 4983230072969 + 3 ^ 40 * 5704830 * 2
def baseEnd_5704830 : Nat := 325479982465446673343219

theorem tailTrace_5704830 : CollatzResearch.WordTrace tailWord_5704830 prefixEnd_5704830 325479982465446673343219 := by
  unfold tailWord_5704830
  simp only [CollatzResearch.WordTrace]
  refine ⟨26009030490297836530066993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138714829281588461493690629 26009030490297836530066993)
  ·
    refine ⟨19506772867723377397550245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26009030490297836530066993 19506772867723377397550245)
    ·
      refine ⟨3657519912698133262040671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19506772867723377397550245 3657519912698133262040671)
      ·
        refine ⟨5486279869047199893061007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3657519912698133262040671 5486279869047199893061007)
        ·
          refine ⟨8229419803570799839591511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5486279869047199893061007 8229419803570799839591511)
          ·
            refine ⟨12344129705356199759387267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8229419803570799839591511 12344129705356199759387267)
            ·
              refine ⟨18516194558034299639080901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12344129705356199759387267 18516194558034299639080901)
              ·
                refine ⟨3471786479631431182327669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18516194558034299639080901 3471786479631431182327669)
                ·
                  refine ⟨325479982465446673343219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3471786479631431182327669 325479982465446673343219)
                  ·
                    rfl

theorem cell23_5704830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 4, 5].length) (baseStart_5704830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5704830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5704830 prefixEnd_5704830 := by exact prefixLift 5704830
  have htrace : WordTrace (prefixWord ++ tailWord_5704830) baseStart_5704830 baseEnd_5704830 := by
    simpa [prefixWord, tailWord_5704830, baseEnd_5704830] using wordTrace_append hprefix tailTrace_5704830
  have hstable : (prefixWord ++ tailWord_5704830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5704830).length < 2 ^ (prefixWord ++ tailWord_5704830).sum := by decide
  have hdescent : baseEnd_5704830 < baseStart_5704830 := by decide
  rcases family_descends (prefixWord ++ tailWord_5704830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5704846 : List Nat := [4, 1, 1, 3, 2, 2, 1, 1, 2, 4, 2]
def baseStart_5704846 : Nat := 118140960795 + 5704846 * 2 ^ 59
def prefixEnd_5704846 : Nat := 4983230072969 + 3 ^ 40 * 5704846 * 2
def baseEnd_5704846 : Nat := 2929328057879491997488897

theorem tailTrace_5704846 : CollatzResearch.WordTrace tailWord_5704846 prefixEnd_5704846 2929328057879491997488897 := by
  unfold tailWord_5704846
  simp only [CollatzResearch.WordTrace]
  refine ⟨26009103436290590871639799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138715218326883151315412261 26009103436290590871639799)
  ·
    refine ⟨39013655154435886307459699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26009103436290590871639799 39013655154435886307459699)
    ·
      refine ⟨58520482731653829461189549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39013655154435886307459699 58520482731653829461189549)
      ·
        refine ⟨21945181024370186047946081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58520482731653829461189549 21945181024370186047946081)
        ·
          refine ⟨16458885768277639535959561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21945181024370186047946081 16458885768277639535959561)
          ·
            refine ⟨12344164326208229651969671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16458885768277639535959561 12344164326208229651969671)
            ·
              refine ⟨18516246489312344477954507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12344164326208229651969671 18516246489312344477954507)
              ·
                refine ⟨27774369733968516716931761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18516246489312344477954507 27774369733968516716931761)
                ·
                  refine ⟨20830777300476387537698821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27774369733968516716931761 20830777300476387537698821)
                  ·
                    refine ⟨3905770743839322663318529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20830777300476387537698821 3905770743839322663318529)
                    ·
                      refine ⟨2929328057879491997488897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3905770743839322663318529 2929328057879491997488897)
                      ·
                        rfl

theorem cell23_5704846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 1, 2, 4, 2].length) (baseStart_5704846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5704846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5704846 prefixEnd_5704846 := by exact prefixLift 5704846
  have htrace : WordTrace (prefixWord ++ tailWord_5704846) baseStart_5704846 baseEnd_5704846 := by
    simpa [prefixWord, tailWord_5704846, baseEnd_5704846] using wordTrace_append hprefix tailTrace_5704846
  have hstable : (prefixWord ++ tailWord_5704846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5704846).length < 2 ^ (prefixWord ++ tailWord_5704846).sum := by decide
  have hdescent : baseEnd_5704846 < baseStart_5704846 := by decide
  rcases family_descends (prefixWord ++ tailWord_5704846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5704863 : List Nat := [1, 1, 2, 6, 3, 1, 1, 1, 2, 1, 4]
def baseStart_5704863 : Nat := 118140960795 + 5704863 * 2 ^ 59
def prefixEnd_5704863 : Nat := 4983230072969 + 3 ^ 40 * 5704863 * 2
def baseEnd_5704863 : Nat := 2929336787050618430976319

theorem tailTrace_5704863 : CollatzResearch.WordTrace tailWord_5704863 prefixEnd_5704863 2929336787050618430976319 := by
  unfold tailWord_5704863
  simp only [CollatzResearch.WordTrace]
  refine ⟨208073447531263138876487243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138715631687508759250991495 208073447531263138876487243)
  ·
    refine ⟨312110171296894708314730865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208073447531263138876487243 312110171296894708314730865)
    ·
      refine ⟨234082628472671031236048149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 312110171296894708314730865 234082628472671031236048149)
      ·
        refine ⟨10972623209656454589189757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 234082628472671031236048149 10972623209656454589189757)
        ·
          refine ⟨4114733703621170470946159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10972623209656454589189757 4114733703621170470946159)
          ·
            refine ⟨6172100555431755706419239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4114733703621170470946159 6172100555431755706419239)
            ·
              refine ⟨9258150833147633559628859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6172100555431755706419239 9258150833147633559628859)
              ·
                refine ⟨13887226249721450339443289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9258150833147633559628859 13887226249721450339443289)
                ·
                  refine ⟨10415419687291087754582467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13887226249721450339443289 10415419687291087754582467)
                  ·
                    refine ⟨15623129530936631631873701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10415419687291087754582467 15623129530936631631873701)
                    ·
                      refine ⟨2929336787050618430976319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15623129530936631631873701 2929336787050618430976319)
                      ·
                        rfl

theorem cell23_5704863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 1, 2, 1, 4].length) (baseStart_5704863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5704863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5704863 prefixEnd_5704863 := by exact prefixLift 5704863
  have htrace : WordTrace (prefixWord ++ tailWord_5704863) baseStart_5704863 baseEnd_5704863 := by
    simpa [prefixWord, tailWord_5704863, baseEnd_5704863] using wordTrace_append hprefix tailTrace_5704863
  have hstable : (prefixWord ++ tailWord_5704863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5704863).length < 2 ^ (prefixWord ++ tailWord_5704863).sum := by decide
  have hdescent : baseEnd_5704863 < baseStart_5704863 := by decide
  rcases family_descends (prefixWord ++ tailWord_5704863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5704866 : List Nat := [3, 3, 1, 3, 2, 1, 1, 1, 1, 4, 3]
def baseStart_5704866 : Nat := 118140960795 + 5704866 * 2 ^ 59
def prefixEnd_5704866 : Nat := 4983230072969 + 3 ^ 40 * 5704866 * 2
def baseEnd_5704866 : Nat := 2929338327492581919238805

theorem tailTrace_5704866 : CollatzResearch.WordTrace tailWord_5704866 prefixEnd_5704866 2929338327492581919238805 := by
  unfold tailWord_5704866
  simp only [CollatzResearch.WordTrace]
  refine ⟨52018389237563067597211613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138715704633501513592564301 52018389237563067597211613)
  ·
    refine ⟨19506895964086150348954355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52018389237563067597211613 19506895964086150348954355)
    ·
      refine ⟨29260343946129225523431533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19506895964086150348954355 29260343946129225523431533)
      ·
        refine ⟨10972628979798459571286825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29260343946129225523431533 10972628979798459571286825)
        ·
          refine ⟨8229471734848844678465119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10972628979798459571286825 8229471734848844678465119)
          ·
            refine ⟨12344207602273267017697679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8229471734848844678465119 12344207602273267017697679)
            ·
              refine ⟨18516311403409900526546519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12344207602273267017697679 18516311403409900526546519)
              ·
                refine ⟨27774467105114850789819779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18516311403409900526546519 27774467105114850789819779)
                ·
                  refine ⟨41661700657672276184729669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27774467105114850789819779 41661700657672276184729669)
                  ·
                    refine ⟨7811568873313551784636813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41661700657672276184729669 7811568873313551784636813)
                    ·
                      refine ⟨2929338327492581919238805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7811568873313551784636813 2929338327492581919238805)
                      ·
                        rfl

theorem cell23_5704866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_5704866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5704866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5704866 prefixEnd_5704866 := by exact prefixLift 5704866
  have htrace : WordTrace (prefixWord ++ tailWord_5704866) baseStart_5704866 baseEnd_5704866 := by
    simpa [prefixWord, tailWord_5704866, baseEnd_5704866] using wordTrace_append hprefix tailTrace_5704866
  have hstable : (prefixWord ++ tailWord_5704866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5704866).length < 2 ^ (prefixWord ++ tailWord_5704866).sum := by decide
  have hdescent : baseEnd_5704866 < baseStart_5704866 := by decide
  rcases family_descends (prefixWord ++ tailWord_5704866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5704919 : List Nat := [1, 1, 3, 2, 1, 2, 3, 4, 1, 1, 4]
def baseStart_5704919 : Nat := 118140960795 + 5704919 * 2 ^ 59
def prefixEnd_5704919 : Nat := 4983230072969 + 3 ^ 40 * 5704919 * 2
def baseEnd_5704919 : Nat := 2929365541967270211876061

theorem tailTrace_5704919 : CollatzResearch.WordTrace tailWord_5704919 prefixEnd_5704919 2929365541967270211876061 := by
  unfold tailWord_5704919
  simp only [CollatzResearch.WordTrace]
  refine ⟨208075490019060260440525811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138716993346040173627017207 208075490019060260440525811)
  ·
    refine ⟨312113235028590390660788717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208075490019060260440525811 312113235028590390660788717)
    ·
      refine ⟨117042463135721396497795769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 312113235028590390660788717 117042463135721396497795769)
      ·
        refine ⟨87781847351791047373346827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117042463135721396497795769 87781847351791047373346827)
        ·
          refine ⟨131672771027686571060020241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87781847351791047373346827 131672771027686571060020241)
          ·
            refine ⟨98754578270764928295015181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131672771027686571060020241 98754578270764928295015181)
            ·
              refine ⟨37032966851536848110630693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 98754578270764928295015181 37032966851536848110630693)
              ·
                refine ⟨6943681284663159020743255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37032966851536848110630693 6943681284663159020743255)
                ·
                  refine ⟨10415521926994738531114883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6943681284663159020743255 10415521926994738531114883)
                  ·
                    refine ⟨15623282890492107796672325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10415521926994738531114883 15623282890492107796672325)
                    ·
                      refine ⟨2929365541967270211876061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15623282890492107796672325 2929365541967270211876061)
                      ·
                        rfl

theorem cell23_5704919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 4, 1, 1, 4].length) (baseStart_5704919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5704919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5704919 prefixEnd_5704919 := by exact prefixLift 5704919
  have htrace : WordTrace (prefixWord ++ tailWord_5704919) baseStart_5704919 baseEnd_5704919 := by
    simpa [prefixWord, tailWord_5704919, baseEnd_5704919] using wordTrace_append hprefix tailTrace_5704919
  have hstable : (prefixWord ++ tailWord_5704919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5704919).length < 2 ^ (prefixWord ++ tailWord_5704919).sum := by decide
  have hdescent : baseEnd_5704919 < baseStart_5704919 := by decide
  rcases family_descends (prefixWord ++ tailWord_5704919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5704922 : List Nat := [3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 5]
def baseStart_5704922 : Nat := 118140960795 + 5704922 * 2 ^ 59
def prefixEnd_5704922 : Nat := 4983230072969 + 3 ^ 40 * 5704922 * 2
def baseEnd_5704922 : Nat := 2929367082409233700138547

theorem tailTrace_5704922 : CollatzResearch.WordTrace tailWord_5704922 prefixEnd_5704922 2929367082409233700138547 := by
  unfold tailWord_5704922
  simp only [CollatzResearch.WordTrace]
  refine ⟨52018899859512347988221255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138717066292032927968590013 52018899859512347988221255)
  ·
    refine ⟨78028349789268521982331883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52018899859512347988221255 78028349789268521982331883)
    ·
      refine ⟨117042524683902782973497825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78028349789268521982331883 117042524683902782973497825)
      ·
        refine ⟨87781893512927087230123369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117042524683902782973497825 87781893512927087230123369)
        ·
          refine ⟨65836420134695315422592527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87781893512927087230123369 65836420134695315422592527)
          ·
            refine ⟨98754630202042973133888791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65836420134695315422592527 98754630202042973133888791)
            ·
              refine ⟨148131945303064459700833187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98754630202042973133888791 148131945303064459700833187)
              ·
                refine ⟨222197917954596689551249781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 148131945303064459700833187 222197917954596689551249781)
                ·
                  refine ⟨20831054808243439645429667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 222197917954596689551249781 20831054808243439645429667)
                  ·
                    refine ⟨31246582212365159468144501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20831054808243439645429667 31246582212365159468144501)
                    ·
                      refine ⟨2929367082409233700138547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31246582212365159468144501 2929367082409233700138547)
                      ·
                        rfl

theorem cell23_5704922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 5].length) (baseStart_5704922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5704922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5704922 prefixEnd_5704922 := by exact prefixLift 5704922
  have htrace : WordTrace (prefixWord ++ tailWord_5704922) baseStart_5704922 baseEnd_5704922 := by
    simpa [prefixWord, tailWord_5704922, baseEnd_5704922] using wordTrace_append hprefix tailTrace_5704922
  have hstable : (prefixWord ++ tailWord_5704922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5704922).length < 2 ^ (prefixWord ++ tailWord_5704922).sum := by decide
  have hdescent : baseEnd_5704922 < baseStart_5704922 := by decide
  rcases family_descends (prefixWord ++ tailWord_5704922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5704929 : List Nat := [1, 2, 3, 1, 3, 2, 1, 2, 4, 4]
def baseStart_5704929 : Nat := 118140960795 + 5704929 * 2 ^ 59
def prefixEnd_5704929 : Nat := 4983230072969 + 3 ^ 40 * 5704929 * 2
def baseEnd_5704929 : Nat := 976456892257938390917005

theorem tailTrace_5704929 : CollatzResearch.WordTrace tailWord_5704929 prefixEnd_5704929 976456892257938390917005 := by
  unfold tailWord_5704929
  simp only [CollatzResearch.WordTrace]
  refine ⟨208075854749024032148389841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138717236499349354765593227 208075854749024032148389841)
  ·
    refine ⟨156056891061768024111292381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208075854749024032148389841 156056891061768024111292381)
    ·
      refine ⟨58521334148163009041734643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156056891061768024111292381 58521334148163009041734643)
      ·
        refine ⟨87782001222244513562601965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58521334148163009041734643 87782001222244513562601965)
        ·
          refine ⟨32918250458341692585975737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87782001222244513562601965 32918250458341692585975737)
          ·
            refine ⟨24688687843756269439481803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32918250458341692585975737 24688687843756269439481803)
            ·
              refine ⟨37033031765634404159222705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24688687843756269439481803 37033031765634404159222705)
              ·
                refine ⟨27774773824225803119417029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37033031765634404159222705 27774773824225803119417029)
                ·
                  refine ⟨5207770092042338084890693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27774773824225803119417029 5207770092042338084890693)
                  ·
                    refine ⟨976456892257938390917005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5207770092042338084890693 976456892257938390917005)
                    ·
                      rfl

theorem cell23_5704929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 2, 4, 4].length) (baseStart_5704929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5704929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5704929 prefixEnd_5704929 := by exact prefixLift 5704929
  have htrace : WordTrace (prefixWord ++ tailWord_5704929) baseStart_5704929 baseEnd_5704929 := by
    simpa [prefixWord, tailWord_5704929, baseEnd_5704929] using wordTrace_append hprefix tailTrace_5704929
  have hstable : (prefixWord ++ tailWord_5704929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5704929).length < 2 ^ (prefixWord ++ tailWord_5704929).sum := by decide
  have hdescent : baseEnd_5704929 < baseStart_5704929 := by decide
  rcases family_descends (prefixWord ++ tailWord_5704929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5704939 : List Nat := [1, 1, 1, 1, 2, 7, 2, 1, 1, 1, 5]
def baseStart_5704939 : Nat := 118140960795 + 5704939 * 2 ^ 59
def prefixEnd_5704939 : Nat := 4983230072969 + 3 ^ 40 * 5704939 * 2
def baseEnd_5704939 : Nat := 2929375811580360133625969

theorem tailTrace_5704939 : CollatzResearch.WordTrace tailWord_5704939 prefixEnd_5704939 2929375811580360133625969 := by
  unfold tailWord_5704939
  simp only [CollatzResearch.WordTrace]
  refine ⟨208076219478987803856253871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138717479652658535904169247 208076219478987803856253871)
  ·
    refine ⟨312114329218481705784380807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208076219478987803856253871 312114329218481705784380807)
    ·
      refine ⟨468171493827722558676571211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312114329218481705784380807 468171493827722558676571211)
      ·
        refine ⟨702257240741583838014856817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 468171493827722558676571211 702257240741583838014856817)
        ·
          refine ⟨526692930556187878511142613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 702257240741583838014856817 526692930556187878511142613)
          ·
            refine ⟨12344365559910653402604905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 526692930556187878511142613 12344365559910653402604905)
            ·
              refine ⟨9258274169932990051953679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12344365559910653402604905 9258274169932990051953679)
              ·
                refine ⟨13887411254899485077930519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9258274169932990051953679 13887411254899485077930519)
                ·
                  refine ⟨20831116882349227616895779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13887411254899485077930519 20831116882349227616895779)
                  ·
                    refine ⟨31246675323523841425343669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20831116882349227616895779 31246675323523841425343669)
                    ·
                      refine ⟨2929375811580360133625969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31246675323523841425343669 2929375811580360133625969)
                      ·
                        rfl

theorem cell23_5704939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 1, 1, 1, 5].length) (baseStart_5704939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5704939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5704939 prefixEnd_5704939 := by exact prefixLift 5704939
  have htrace : WordTrace (prefixWord ++ tailWord_5704939) baseStart_5704939 baseEnd_5704939 := by
    simpa [prefixWord, tailWord_5704939, baseEnd_5704939] using wordTrace_append hprefix tailTrace_5704939
  have hstable : (prefixWord ++ tailWord_5704939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5704939).length < 2 ^ (prefixWord ++ tailWord_5704939).sum := by decide
  have hdescent : baseEnd_5704939 < baseStart_5704939 := by decide
  rcases family_descends (prefixWord ++ tailWord_5704939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5704942 : List Nat := [4, 1, 2, 1, 1, 1, 13]
def baseStart_5704942 : Nat := 118140960795 + 5704942 * 2 ^ 59
def prefixEnd_5704942 : Nat := 4983230072969 + 3 ^ 40 * 5704942 * 2
def baseEnd_5704942 : Nat := 36165152494102760764055

theorem tailTrace_5704942 : CollatzResearch.WordTrace tailWord_5704942 prefixEnd_5704942 36165152494102760764055 := by
  unfold tailWord_5704942
  simp only [CollatzResearch.WordTrace]
  refine ⟨26009541112247116921076635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138717552598651290245742053 26009541112247116921076635)
  ·
    refine ⟨39014311668370675381614953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26009541112247116921076635 39014311668370675381614953)
    ·
      refine ⟨29260733751278006536211215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39014311668370675381614953 29260733751278006536211215)
      ·
        refine ⟨43891100626917009804316823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29260733751278006536211215 43891100626917009804316823)
        ·
          refine ⟨65836650940375514706475235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43891100626917009804316823 65836650940375514706475235)
          ·
            refine ⟨98754976410563272059712853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65836650940375514706475235 98754976410563272059712853)
            ·
              refine ⟨36165152494102760764055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 98754976410563272059712853 36165152494102760764055)
              ·
                rfl

theorem cell23_5704942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 13].length) (baseStart_5704942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5704942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5704942 prefixEnd_5704942 := by exact prefixLift 5704942
  have htrace : WordTrace (prefixWord ++ tailWord_5704942) baseStart_5704942 baseEnd_5704942 := by
    simpa [prefixWord, tailWord_5704942, baseEnd_5704942] using wordTrace_append hprefix tailTrace_5704942
  have hstable : (prefixWord ++ tailWord_5704942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5704942).length < 2 ^ (prefixWord ++ tailWord_5704942).sum := by decide
  have hdescent : baseEnd_5704942 < baseStart_5704942 := by decide
  rcases family_descends (prefixWord ++ tailWord_5704942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5704963 : List Nat := [1, 1, 1, 3, 2, 6, 2, 1, 2, 4]
def baseStart_5704963 : Nat := 118140960795 + 5704963 * 2 ^ 59
def prefixEnd_5704963 : Nat := 4983230072969 + 3 ^ 40 * 5704963 * 2
def baseEnd_5704963 : Nat := 976462711705356013241953

theorem tailTrace_5704963 : CollatzResearch.WordTrace tailWord_5704963 prefixEnd_5704963 976462711705356013241953 := by
  unfold tailWord_5704963
  simp only [CollatzResearch.WordTrace]
  refine ⟨208077094830900855955127543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138718063220600570636751695 208077094830900855955127543)
  ·
    refine ⟨312115642246351283932691315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208077094830900855955127543 312115642246351283932691315)
    ·
      refine ⟨468173463369526925899036973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312115642246351283932691315 468173463369526925899036973)
      ·
        refine ⟨175565048763572597212138865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 468173463369526925899036973 175565048763572597212138865)
        ·
          refine ⟨131673786572679447909104149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175565048763572597212138865 131673786572679447909104149)
          ·
            refine ⟨6172208745594349120739257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 131673786572679447909104149 6172208745594349120739257)
            ·
              refine ⟨4629156559195761840554443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6172208745594349120739257 4629156559195761840554443)
              ·
                refine ⟨6943734838793642760831665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4629156559195761840554443 6943734838793642760831665)
                ·
                  refine ⟨5207801129095232070623749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6943734838793642760831665 5207801129095232070623749)
                  ·
                    refine ⟨976462711705356013241953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5207801129095232070623749 976462711705356013241953)
                    ·
                      rfl

theorem cell23_5704963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 2, 1, 2, 4].length) (baseStart_5704963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5704963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5704963 prefixEnd_5704963 := by exact prefixLift 5704963
  have htrace : WordTrace (prefixWord ++ tailWord_5704963) baseStart_5704963 baseEnd_5704963 := by
    simpa [prefixWord, tailWord_5704963, baseEnd_5704963] using wordTrace_append hprefix tailTrace_5704963
  have hstable : (prefixWord ++ tailWord_5704963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5704963).length < 2 ^ (prefixWord ++ tailWord_5704963).sum := by decide
  have hdescent : baseEnd_5704963 < baseStart_5704963 := by decide
  rcases family_descends (prefixWord ++ tailWord_5704963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5704969 : List Nat := [1, 2, 1, 1, 3, 3, 2, 3, 1, 3, 3]
def baseStart_5704969 : Nat := 118140960795 + 5704969 * 2 ^ 59
def prefixEnd_5704969 : Nat := 4983230072969 + 3 ^ 40 * 5704969 * 2
def baseEnd_5704969 : Nat := 2929391215999995016250831

theorem tailTrace_5704969 : CollatzResearch.WordTrace tailWord_5704969 prefixEnd_5704969 2929391215999995016250831 := by
  unfold tailWord_5704969
  simp only [CollatzResearch.WordTrace]
  refine ⟨208077313668879118979845961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138718209112586079319897307 208077313668879118979845961)
  ·
    refine ⟨156057985251659339234884471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208077313668879118979845961 156057985251659339234884471)
    ·
      refine ⟨234086977877489008852326707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156057985251659339234884471 234086977877489008852326707)
      ·
        refine ⟨351130466816233513278490061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234086977877489008852326707 351130466816233513278490061)
        ·
          refine ⟨131673925056087567479433773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 351130466816233513278490061 131673925056087567479433773)
          ·
            refine ⟨49377721896032837804787665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 131673925056087567479433773 49377721896032837804787665)
            ·
              refine ⟨37033291422024628353590749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49377721896032837804787665 37033291422024628353590749)
              ·
                refine ⟨13887484283259235632596531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37033291422024628353590749 13887484283259235632596531)
                ·
                  refine ⟨20831226424888853448894797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13887484283259235632596531 20831226424888853448894797)
                  ·
                    refine ⟨7811709909333320043335549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20831226424888853448894797 7811709909333320043335549)
                    ·
                      refine ⟨2929391215999995016250831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7811709909333320043335549 2929391215999995016250831)
                      ·
                        rfl

theorem cell23_5704969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 3, 1, 3, 3].length) (baseStart_5704969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5704969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5704969 prefixEnd_5704969 := by exact prefixLift 5704969
  have htrace : WordTrace (prefixWord ++ tailWord_5704969) baseStart_5704969 baseEnd_5704969 := by
    simpa [prefixWord, tailWord_5704969, baseEnd_5704969] using wordTrace_append hprefix tailTrace_5704969
  have hstable : (prefixWord ++ tailWord_5704969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5704969).length < 2 ^ (prefixWord ++ tailWord_5704969).sum := by decide
  have hdescent : baseEnd_5704969 < baseStart_5704969 := by decide
  rcases family_descends (prefixWord ++ tailWord_5704969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5704986 : List Nat := [3, 1, 1, 3, 3, 2, 1, 2, 1, 3, 3]
def baseStart_5704986 : Nat := 118140960795 + 5704986 * 2 ^ 59
def prefixEnd_5704986 : Nat := 4983230072969 + 3 ^ 40 * 5704986 * 2
def baseEnd_5704986 : Nat := 2929399945171121449738253

theorem tailTrace_5704986 : CollatzResearch.WordTrace tailWord_5704986 prefixEnd_5704986 2929399945171121449738253 := by
  unfold tailWord_5704986
  simp only [CollatzResearch.WordTrace]
  refine ⟨52019483427454382720803703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138718622473211687255476541 52019483427454382720803703)
  ·
    refine ⟨78029225141181574081205555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52019483427454382720803703 78029225141181574081205555)
    ·
      refine ⟨117043837711772361121808333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78029225141181574081205555 117043837711772361121808333)
      ·
        refine ⟨43891439141914635420678125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117043837711772361121808333 43891439141914635420678125)
        ·
          refine ⟨16459289678217988282754297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43891439141914635420678125 16459289678217988282754297)
          ·
            refine ⟨12344467258663491212065723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16459289678217988282754297 12344467258663491212065723)
            ·
              refine ⟨18516700887995236818098585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12344467258663491212065723 18516700887995236818098585)
              ·
                refine ⟨13887525665996427613573939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18516700887995236818098585 13887525665996427613573939)
                ·
                  refine ⟨20831288498994641420360909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13887525665996427613573939 20831288498994641420360909)
                  ·
                    refine ⟨7811733187122990532635341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20831288498994641420360909 7811733187122990532635341)
                    ·
                      refine ⟨2929399945171121449738253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7811733187122990532635341 2929399945171121449738253)
                      ·
                        rfl

theorem cell23_5704986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 2, 1, 3, 3].length) (baseStart_5704986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5704986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5704986 prefixEnd_5704986 := by exact prefixLift 5704986
  have htrace : WordTrace (prefixWord ++ tailWord_5704986) baseStart_5704986 baseEnd_5704986 := by
    simpa [prefixWord, tailWord_5704986, baseEnd_5704986] using wordTrace_append hprefix tailTrace_5704986
  have hstable : (prefixWord ++ tailWord_5704986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5704986).length < 2 ^ (prefixWord ++ tailWord_5704986).sum := by decide
  have hdescent : baseEnd_5704986 < baseStart_5704986 := by decide
  rcases family_descends (prefixWord ++ tailWord_5704986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5704990 : List Nat := [4, 3, 2, 1, 2, 2, 1, 1, 1, 1, 5]
def baseStart_5704990 : Nat := 118140960795 + 5704990 * 2 ^ 59
def prefixEnd_5704990 : Nat := 4983230072969 + 3 ^ 40 * 5704990 * 2
def baseEnd_5704990 : Nat := 2929401999093739434088235

theorem tailTrace_5704990 : CollatzResearch.WordTrace tailWord_5704990 prefixEnd_5704990 2929401999093739434088235 := by
  unfold tailWord_5704990
  simp only [CollatzResearch.WordTrace]
  refine ⟨26009759950225379945795053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138718719734535359710906949 26009759950225379945795053)
  ·
    refine ⟨9753659981334517479673145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26009759950225379945795053 9753659981334517479673145)
    ·
      refine ⟨7315244986000888109754859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9753659981334517479673145 7315244986000888109754859)
      ·
        refine ⟨10972867479001332164632289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7315244986000888109754859 10972867479001332164632289)
        ·
          refine ⟨8229650609250999123474217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10972867479001332164632289 8229650609250999123474217)
          ·
            refine ⟨6172237956938249342605663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8229650609250999123474217 6172237956938249342605663)
            ·
              refine ⟨9258356935407374013908495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6172237956938249342605663 9258356935407374013908495)
              ·
                refine ⟨13887535403111061020862743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9258356935407374013908495 13887535403111061020862743)
                ·
                  refine ⟨20831303104666591531294115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13887535403111061020862743 20831303104666591531294115)
                  ·
                    refine ⟨31246954656999887296941173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20831303104666591531294115 31246954656999887296941173)
                    ·
                      refine ⟨2929401999093739434088235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31246954656999887296941173 2929401999093739434088235)
                      ·
                        rfl

theorem cell23_5704990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_5704990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5704990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5704990 prefixEnd_5704990 := by exact prefixLift 5704990
  have htrace : WordTrace (prefixWord ++ tailWord_5704990) baseStart_5704990 baseEnd_5704990 := by
    simpa [prefixWord, tailWord_5704990, baseEnd_5704990] using wordTrace_append hprefix tailTrace_5704990
  have hstable : (prefixWord ++ tailWord_5704990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5704990).length < 2 ^ (prefixWord ++ tailWord_5704990).sum := by decide
  have hdescent : baseEnd_5704990 < baseStart_5704990 := by decide
  rcases family_descends (prefixWord ++ tailWord_5704990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5705009 : List Nat := [1, 2, 2, 3, 3, 1, 1, 1, 2, 3, 4]
def baseStart_5705009 : Nat := 118140960795 + 5705009 * 2 ^ 59
def prefixEnd_5705009 : Nat := 4983230072969 + 3 ^ 40 * 5705009 * 2
def baseEnd_5705009 : Nat := 2929411755226174859750647

theorem tailTrace_5705009 : CollatzResearch.WordTrace tailWord_5705009 prefixEnd_5705009 2929411755226174859750647 := by
  unfold tailWord_5705009
  simp only [CollatzResearch.WordTrace]
  refine ⟨208078772588734205811302081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138719181725822803874201387 208078772588734205811302081)
  ·
    refine ⟨156059079441550654358476561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208078772588734205811302081 156059079441550654358476561)
    ·
      refine ⟨117044309581162990768857421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156059079441550654358476561 117044309581162990768857421)
      ·
        refine ⟨43891616092936121538321533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117044309581162990768857421 43891616092936121538321533)
        ·
          refine ⟨16459356034851045576870575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43891616092936121538321533 16459356034851045576870575)
          ·
            refine ⟨24689034052276568365305863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16459356034851045576870575 24689034052276568365305863)
            ·
              refine ⟨37033551078414852547958795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24689034052276568365305863 37033551078414852547958795)
              ·
                refine ⟨55550326617622278821938193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37033551078414852547958795 55550326617622278821938193)
                ·
                  refine ⟨41662744963216709116453645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55550326617622278821938193 41662744963216709116453645)
                  ·
                    refine ⟨15623529361206265918670117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41662744963216709116453645 15623529361206265918670117)
                    ·
                      refine ⟨2929411755226174859750647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15623529361206265918670117 2929411755226174859750647)
                      ·
                        rfl

theorem cell23_5705009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 1, 2, 3, 4].length) (baseStart_5705009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5705009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5705009 prefixEnd_5705009 := by exact prefixLift 5705009
  have htrace : WordTrace (prefixWord ++ tailWord_5705009) baseStart_5705009 baseEnd_5705009 := by
    simpa [prefixWord, tailWord_5705009, baseEnd_5705009] using wordTrace_append hprefix tailTrace_5705009
  have hstable : (prefixWord ++ tailWord_5705009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5705009).length < 2 ^ (prefixWord ++ tailWord_5705009).sum := by decide
  have hdescent : baseEnd_5705009 < baseStart_5705009 := by decide
  rcases family_descends (prefixWord ++ tailWord_5705009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5705060 : List Nat := [2, 3, 1, 1, 3, 2, 3, 2, 2, 2, 2]
def baseStart_5705060 : Nat := 118140960795 + 5705060 * 2 ^ 59
def prefixEnd_5705060 : Nat := 4983230072969 + 3 ^ 40 * 5705060 * 2
def baseEnd_5705060 : Nat := 2929437942739554160212913

theorem tailTrace_5705060 : CollatzResearch.WordTrace tailWord_5705060 prefixEnd_5705060 2929437942739554160212913 := by
  unfold tailWord_5705060
  simp only [CollatzResearch.WordTrace]
  refine ⟨104040316355774720760704317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138720421807699627680939089 104040316355774720760704317)
  ·
    refine ⟨39015118633415520285264119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104040316355774720760704317 39015118633415520285264119)
    ·
      refine ⟨58522677950123280427896179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39015118633415520285264119 58522677950123280427896179)
      ·
        refine ⟨87784016925184920641844269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58522677950123280427896179 87784016925184920641844269)
        ·
          refine ⟨32919006346944345240691601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87784016925184920641844269 32919006346944345240691601)
          ·
            refine ⟨24689254760208258930518701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32919006346944345240691601 24689254760208258930518701)
            ·
              refine ⟨9258470535078097098944513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24689254760208258930518701 9258470535078097098944513)
              ·
                refine ⟨6943852901308572824208385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9258470535078097098944513 6943852901308572824208385)
                ·
                  refine ⟨5207889675981429618156289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6943852901308572824208385 5207889675981429618156289)
                  ·
                    refine ⟨3905917256986072213617217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5207889675981429618156289 3905917256986072213617217)
                    ·
                      refine ⟨2929437942739554160212913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3905917256986072213617217 2929437942739554160212913)
                      ·
                        rfl

theorem cell23_5705060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 2, 2, 2, 2].length) (baseStart_5705060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5705060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5705060 prefixEnd_5705060 := by exact prefixLift 5705060
  have htrace : WordTrace (prefixWord ++ tailWord_5705060) baseStart_5705060 baseEnd_5705060 := by
    simpa [prefixWord, tailWord_5705060, baseEnd_5705060] using wordTrace_append hprefix tailTrace_5705060
  have hstable : (prefixWord ++ tailWord_5705060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5705060).length < 2 ^ (prefixWord ++ tailWord_5705060).sum := by decide
  have hdescent : baseEnd_5705060 < baseStart_5705060 := by decide
  rcases family_descends (prefixWord ++ tailWord_5705060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5705077 : List Nat := [1, 3, 4, 1, 4, 1, 1, 1, 1, 4, 2]
def baseStart_5705077 : Nat := 118140960795 + 5705077 * 2 ^ 59
def prefixEnd_5705077 : Nat := 4983230072969 + 3 ^ 40 * 5705077 * 2
def baseEnd_5705077 : Nat := 2929446671910680593700335

theorem tailTrace_5705077 : CollatzResearch.WordTrace tailWord_5705077 prefixEnd_5705077 2929446671910680593700335 := by
  unfold tailWord_5705077
  simp only [CollatzResearch.WordTrace]
  refine ⟨208081252752487853424777485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138720835168325235616518323 208081252752487853424777485)
  ·
    refine ⟨78030469782182945034291557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208081252752487853424777485 78030469782182945034291557)
    ·
      refine ⟨14630713084159302193929667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78030469782182945034291557 14630713084159302193929667)
      ·
        refine ⟨21946069626238953290894501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14630713084159302193929667 21946069626238953290894501)
        ·
          refine ⟨4114888054919803742042719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21946069626238953290894501 4114888054919803742042719)
          ·
            refine ⟨6172332082379705613064079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4114888054919803742042719 6172332082379705613064079)
            ·
              refine ⟨9258498123569558419596119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6172332082379705613064079 9258498123569558419596119)
              ·
                refine ⟨13887747185354337629394179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9258498123569558419596119 13887747185354337629394179)
                ·
                  refine ⟨20831620778031506444091269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13887747185354337629394179 20831620778031506444091269)
                  ·
                    refine ⟨3905928895880907458267113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20831620778031506444091269 3905928895880907458267113)
                    ·
                      refine ⟨2929446671910680593700335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3905928895880907458267113 2929446671910680593700335)
                      ·
                        rfl

theorem cell23_5705077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 1, 1, 4, 2].length) (baseStart_5705077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5705077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5705077 prefixEnd_5705077 := by exact prefixLift 5705077
  have htrace : WordTrace (prefixWord ++ tailWord_5705077) baseStart_5705077 baseEnd_5705077 := by
    simpa [prefixWord, tailWord_5705077, baseEnd_5705077] using wordTrace_append hprefix tailTrace_5705077
  have hstable : (prefixWord ++ tailWord_5705077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5705077).length < 2 ^ (prefixWord ++ tailWord_5705077).sum := by decide
  have hdescent : baseEnd_5705077 < baseStart_5705077 := by decide
  rcases family_descends (prefixWord ++ tailWord_5705077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5705099 : List Nat := [1, 1, 1, 1, 4, 3, 1, 3, 1, 3, 4]
def baseStart_5705099 : Nat := 118140960795 + 5705099 * 2 ^ 59
def prefixEnd_5705099 : Nat := 4983230072969 + 3 ^ 40 * 5705099 * 2
def baseEnd_5705099 : Nat := 2929457968485079507625233

theorem tailTrace_5705099 : CollatzResearch.WordTrace tailWord_5705099 prefixEnd_5705099 2929457968485079507625233 := by
  unfold tailWord_5705099
  simp only [CollatzResearch.WordTrace]
  refine ⟨208082055158408151182078351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138721370105605434121385567 208082055158408151182078351)
  ·
    refine ⟨312123082737612226773117527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208082055158408151182078351 312123082737612226773117527)
    ·
      refine ⟨468184624106418340159676291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312123082737612226773117527 468184624106418340159676291)
      ·
        refine ⟨702276936159627510239514437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 468184624106418340159676291 702276936159627510239514437)
        ·
          refine ⟨131676925529930158169908957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 702276936159627510239514437 131676925529930158169908957)
          ·
            refine ⟨49378847073723809313715859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 131676925529930158169908957 49378847073723809313715859)
            ·
              refine ⟨74068270610585713970573789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49378847073723809313715859 74068270610585713970573789)
              ·
                refine ⟨27775601478969642738965171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74068270610585713970573789 27775601478969642738965171)
                ·
                  refine ⟨41663402218454464108447757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27775601478969642738965171 41663402218454464108447757)
                  ·
                    refine ⟨15623775831920424040667909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41663402218454464108447757 15623775831920424040667909)
                    ·
                      refine ⟨2929457968485079507625233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15623775831920424040667909 2929457968485079507625233)
                      ·
                        rfl

theorem cell23_5705099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 3, 1, 3, 4].length) (baseStart_5705099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5705099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5705099 prefixEnd_5705099 := by exact prefixLift 5705099
  have htrace : WordTrace (prefixWord ++ tailWord_5705099) baseStart_5705099 baseEnd_5705099 := by
    simpa [prefixWord, tailWord_5705099, baseEnd_5705099] using wordTrace_append hprefix tailTrace_5705099
  have hstable : (prefixWord ++ tailWord_5705099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5705099).length < 2 ^ (prefixWord ++ tailWord_5705099).sum := by decide
  have hdescent : baseEnd_5705099 < baseStart_5705099 := by decide
  rcases family_descends (prefixWord ++ tailWord_5705099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5705177 : List Nat := [1, 2, 1, 2, 4, 4, 2, 2, 1, 4]
def baseStart_5705177 : Nat := 118140960795 + 5705177 * 2 ^ 59
def prefixEnd_5705177 : Nat := 4983230072969 + 3 ^ 40 * 5705177 * 2
def baseEnd_5705177 : Nat := 976499339992043400816625

theorem tailTrace_5705177 : CollatzResearch.WordTrace tailWord_5705177 prefixEnd_5705177 976499339992043400816625 := by
  unfold tailWord_5705177
  simp only [CollatzResearch.WordTrace]
  refine ⟨208084900052125570503417785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138723266701417047002278523 208084900052125570503417785)
  ·
    refine ⟨156063675039094177877563339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208084900052125570503417785 156063675039094177877563339)
    ·
      refine ⟨234095512558641266816345009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156063675039094177877563339 234095512558641266816345009)
      ·
        refine ⟨175571634418980950112258757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 234095512558641266816345009 175571634418980950112258757)
        ·
          refine ⟨32919681453558928146048517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 175571634418980950112258757 32919681453558928146048517)
          ·
            refine ⟨6172440272542299027384097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32919681453558928146048517 6172440272542299027384097)
            ·
              refine ⟨4629330204406724270538073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6172440272542299027384097 4629330204406724270538073)
              ·
                refine ⟨3471997653305043202903555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4629330204406724270538073 3471997653305043202903555)
                ·
                  refine ⟨5207996479957564804355333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3471997653305043202903555 5207996479957564804355333)
                  ·
                    refine ⟨976499339992043400816625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5207996479957564804355333 976499339992043400816625)
                    ·
                      rfl

theorem cell23_5705177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 2, 2, 1, 4].length) (baseStart_5705177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5705177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5705177 prefixEnd_5705177 := by exact prefixLift 5705177
  have htrace : WordTrace (prefixWord ++ tailWord_5705177) baseStart_5705177 baseEnd_5705177 := by
    simpa [prefixWord, tailWord_5705177, baseEnd_5705177] using wordTrace_append hprefix tailTrace_5705177
  have hstable : (prefixWord ++ tailWord_5705177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5705177).length < 2 ^ (prefixWord ++ tailWord_5705177).sum := by decide
  have hdescent : baseEnd_5705177 < baseStart_5705177 := by decide
  rcases family_descends (prefixWord ++ tailWord_5705177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5705183 : List Nat := [1, 1, 2, 3, 3, 1, 2, 3, 3, 1, 3]
def baseStart_5705183 : Nat := 118140960795 + 5705183 * 2 ^ 59
def prefixEnd_5705183 : Nat := 4983230072969 + 3 ^ 40 * 5705183 * 2
def baseEnd_5705183 : Nat := 2929501100860057178974847

theorem tailTrace_5705183 : CollatzResearch.WordTrace tailWord_5705183 prefixEnd_5705183 2929501100860057178974847 := by
  unfold tailWord_5705183
  simp only [CollatzResearch.WordTrace]
  refine ⟨208085118890103833528136203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138723412593402555685424135 208085118890103833528136203)
  ·
    refine ⟨312127678335155750292204305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208085118890103833528136203 312127678335155750292204305)
    ·
      refine ⟨234095758751366812719153229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 312127678335155750292204305 234095758751366812719153229)
      ·
        refine ⟨87785909531762554769682461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 234095758751366812719153229 87785909531762554769682461)
        ·
          refine ⟨32919716074410958038630923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87785909531762554769682461 32919716074410958038630923)
          ·
            refine ⟨49379574111616437057946385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32919716074410958038630923 49379574111616437057946385)
            ·
              refine ⟨37034680583712327793459789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49379574111616437057946385 37034680583712327793459789)
              ·
                refine ⟨13888005218892122922547421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37034680583712327793459789 13888005218892122922547421)
                ·
                  refine ⟨5208001957084546095955283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13888005218892122922547421 5208001957084546095955283)
                  ·
                    refine ⟨7812002935626819143932925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5208001957084546095955283 7812002935626819143932925)
                    ·
                      refine ⟨2929501100860057178974847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7812002935626819143932925 2929501100860057178974847)
                      ·
                        rfl

theorem cell23_5705183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 3, 3, 1, 3].length) (baseStart_5705183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5705183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5705183 prefixEnd_5705183 := by exact prefixLift 5705183
  have htrace : WordTrace (prefixWord ++ tailWord_5705183) baseStart_5705183 baseEnd_5705183 := by
    simpa [prefixWord, tailWord_5705183, baseEnd_5705183] using wordTrace_append hprefix tailTrace_5705183
  have hstable : (prefixWord ++ tailWord_5705183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5705183).length < 2 ^ (prefixWord ++ tailWord_5705183).sum := by decide
  have hdescent : baseEnd_5705183 < baseStart_5705183 := by decide
  rcases family_descends (prefixWord ++ tailWord_5705183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5705220 : List Nat := [2, 3, 2, 3, 2, 1, 1, 3, 1, 5]
def baseStart_5705220 : Nat := 118140960795 + 5705220 * 2 ^ 59
def prefixEnd_5705220 : Nat := 4983230072969 + 3 ^ 40 * 5705220 * 2
def baseEnd_5705220 : Nat := 976506699881424511404059

theorem tailTrace_5705220 : CollatzResearch.WordTrace tailWord_5705220 prefixEnd_5705220 976506699881424511404059 := by
  unfold tailWord_5705220
  simp only [CollatzResearch.WordTrace]
  refine ⟨104043234195484894423616557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138724312260646525898155409 104043234195484894423616557)
  ·
    refine ⟨39016212823306835408856209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104043234195484894423616557 39016212823306835408856209)
    ·
      refine ⟨29262159617480126556642157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39016212823306835408856209 29262159617480126556642157)
      ·
        refine ⟨10973309856555047458740809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29262159617480126556642157 10973309856555047458740809)
        ·
          refine ⟨8229982392416285594055607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10973309856555047458740809 8229982392416285594055607)
          ·
            refine ⟨12344973588624428391083411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8229982392416285594055607 12344973588624428391083411)
            ·
              refine ⟨18517460382936642586625117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12344973588624428391083411 18517460382936642586625117)
              ·
                refine ⟨6944047643601240969984419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18517460382936642586625117 6944047643601240969984419)
                ·
                  refine ⟨10416071465401861454976629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6944047643601240969984419 10416071465401861454976629)
                  ·
                    refine ⟨976506699881424511404059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10416071465401861454976629 976506699881424511404059)
                    ·
                      rfl

theorem cell23_5705220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 3, 1, 5].length) (baseStart_5705220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5705220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5705220 prefixEnd_5705220 := by exact prefixLift 5705220
  have htrace : WordTrace (prefixWord ++ tailWord_5705220) baseStart_5705220 baseEnd_5705220 := by
    simpa [prefixWord, tailWord_5705220, baseEnd_5705220] using wordTrace_append hprefix tailTrace_5705220
  have hstable : (prefixWord ++ tailWord_5705220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5705220).length < 2 ^ (prefixWord ++ tailWord_5705220).sum := by decide
  have hdescent : baseEnd_5705220 < baseStart_5705220 := by decide
  rcases family_descends (prefixWord ++ tailWord_5705220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5705283 : List Nat := [1, 1, 1, 3, 1, 2, 1, 1, 7, 3, 2]
def baseStart_5705283 : Nat := 118140960795 + 5705283 * 2 ^ 59
def prefixEnd_5705283 : Nat := 4983230072969 + 3 ^ 40 * 5705283 * 2
def baseEnd_5705283 : Nat := 2929552448925506787724387

theorem tailTrace_5705283 : CollatzResearch.WordTrace tailWord_5705283 prefixEnd_5705283 2929552448925506787724387 := by
  unfold tailWord_5705283
  simp only [CollatzResearch.WordTrace]
  refine ⟨208088766189741550606776503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138725844126494367071184335 208088766189741550606776503)
  ·
    refine ⟨312133149284612325910164755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208088766189741550606776503 312133149284612325910164755)
    ·
      refine ⟨468199723926918488865247133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312133149284612325910164755 468199723926918488865247133)
      ·
        refine ⟨175574896472594433324467675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 468199723926918488865247133 175574896472594433324467675)
        ·
          refine ⟨263362344708891649986701513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175574896472594433324467675 263362344708891649986701513)
          ·
            refine ⟨197521758531668737490026135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 263362344708891649986701513 197521758531668737490026135)
            ·
              refine ⟨296282637797503106235039203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197521758531668737490026135 296282637797503106235039203)
              ·
                refine ⟨444423956696254659352558805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 296282637797503106235039203 444423956696254659352558805)
                ·
                  refine ⟨10416186485068468578575597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 444423956696254659352558805 10416186485068468578575597)
                  ·
                    refine ⟨3906069931900675716965849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10416186485068468578575597 3906069931900675716965849)
                    ·
                      refine ⟨2929552448925506787724387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3906069931900675716965849 2929552448925506787724387)
                      ·
                        rfl

theorem cell23_5705283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 7, 3, 2].length) (baseStart_5705283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5705283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5705283 prefixEnd_5705283 := by exact prefixLift 5705283
  have htrace : WordTrace (prefixWord ++ tailWord_5705283) baseStart_5705283 baseEnd_5705283 := by
    simpa [prefixWord, tailWord_5705283, baseEnd_5705283] using wordTrace_append hprefix tailTrace_5705283
  have hstable : (prefixWord ++ tailWord_5705283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5705283).length < 2 ^ (prefixWord ++ tailWord_5705283).sum := by decide
  have hdescent : baseEnd_5705283 < baseStart_5705283 := by decide
  rcases family_descends (prefixWord ++ tailWord_5705283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5705290 : List Nat := [3, 1, 2, 1, 1, 3, 2, 4, 2, 1, 3]
def baseStart_5705290 : Nat := 118140960795 + 5705290 * 2 ^ 59
def prefixEnd_5705290 : Nat := 4983230072969 + 3 ^ 40 * 5705290 * 2
def baseEnd_5705290 : Nat := 2929556043290088260336855

theorem tailTrace_5705290 : CollatzResearch.WordTrace tailWord_5705290 prefixEnd_5705290 2929556043290088260336855 := by
  unfold tailWord_5705290
  simp only [CollatzResearch.WordTrace]
  refine ⟨52022255375179047700570331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138726014333810793868187549 52022255375179047700570331)
  ·
    refine ⟨78033383062768571550855497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52022255375179047700570331 78033383062768571550855497)
    ·
      refine ⟨58525037297076428663141623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78033383062768571550855497 58525037297076428663141623)
      ·
        refine ⟨87787555945614642994712435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58525037297076428663141623 87787555945614642994712435)
        ·
          refine ⟨131681333918421964492068653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87787555945614642994712435 131681333918421964492068653)
          ·
            refine ⟨49380500219408236684525745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 131681333918421964492068653 49380500219408236684525745)
            ·
              refine ⟨37035375164556177513394309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49380500219408236684525745 37035375164556177513394309)
              ·
                refine ⟨6944132843354283283761433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37035375164556177513394309 6944132843354283283761433)
                ·
                  refine ⟨5208099632515712462821075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6944132843354283283761433 5208099632515712462821075)
                  ·
                    refine ⟨7812149448773568694231613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5208099632515712462821075 7812149448773568694231613)
                    ·
                      refine ⟨2929556043290088260336855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7812149448773568694231613 2929556043290088260336855)
                      ·
                        rfl

theorem cell23_5705290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 4, 2, 1, 3].length) (baseStart_5705290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5705290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5705290 prefixEnd_5705290 := by exact prefixLift 5705290
  have htrace : WordTrace (prefixWord ++ tailWord_5705290) baseStart_5705290 baseEnd_5705290 := by
    simpa [prefixWord, tailWord_5705290, baseEnd_5705290] using wordTrace_append hprefix tailTrace_5705290
  have hstable : (prefixWord ++ tailWord_5705290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5705290).length < 2 ^ (prefixWord ++ tailWord_5705290).sum := by decide
  have hdescent : baseEnd_5705290 < baseStart_5705290 := by decide
  rcases family_descends (prefixWord ++ tailWord_5705290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5705296 : List Nat := [2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 4]
def baseStart_5705296 : Nat := 118140960795 + 5705296 * 2 ^ 59
def prefixEnd_5705296 : Nat := 4983230072969 + 3 ^ 40 * 5705296 * 2
def baseEnd_5705296 : Nat := 2929559124174015236861827

theorem tailTrace_5705296 : CollatzResearch.WordTrace tailWord_5705296 prefixEnd_5705296 2929559124174015236861827 := by
  unfold tailWord_5705296
  simp only [CollatzResearch.WordTrace]
  refine ⟨104044620169347226913499871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138726160225796302551333161 104044620169347226913499871)
  ·
    refine ⟨156066930254020840370249807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104044620169347226913499871 156066930254020840370249807)
    ·
      refine ⟨234100395381031260555374711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156066930254020840370249807 234100395381031260555374711)
      ·
        refine ⟨351150593071546890833062067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234100395381031260555374711 351150593071546890833062067)
        ·
          refine ⟨526725889607320336249593101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 351150593071546890833062067 526725889607320336249593101)
          ·
            refine ⟨197522208602745126093597413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 526725889607320336249593101 197522208602745126093597413)
            ·
              refine ⟨37035414113014711142549515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 197522208602745126093597413 37035414113014711142549515)
              ·
                refine ⟨55553121169522066713824273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37035414113014711142549515 55553121169522066713824273)
                ·
                  refine ⟨41664840877141550035368205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55553121169522066713824273 41664840877141550035368205)
                  ·
                    refine ⟨15624315328928081263263077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41664840877141550035368205 15624315328928081263263077)
                    ·
                      refine ⟨2929559124174015236861827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15624315328928081263263077 2929559124174015236861827)
                      ·
                        rfl

theorem cell23_5705296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 4].length) (baseStart_5705296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5705296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5705296 prefixEnd_5705296 := by exact prefixLift 5705296
  have htrace : WordTrace (prefixWord ++ tailWord_5705296) baseStart_5705296 baseEnd_5705296 := by
    simpa [prefixWord, tailWord_5705296, baseEnd_5705296] using wordTrace_append hprefix tailTrace_5705296
  have hstable : (prefixWord ++ tailWord_5705296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5705296).length < 2 ^ (prefixWord ++ tailWord_5705296).sum := by decide
  have hdescent : baseEnd_5705296 < baseStart_5705296 := by decide
  rcases family_descends (prefixWord ++ tailWord_5705296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5705300 : List Nat := [2, 4, 1, 1, 1, 2, 2, 2, 3, 3, 2]
def baseStart_5705300 : Nat := 118140960795 + 5705300 * 2 ^ 59
def prefixEnd_5705300 : Nat := 4983230072969 + 3 ^ 40 * 5705300 * 2
def baseEnd_5705300 : Nat := 2929561178096633221211809

theorem tailTrace_5705300 : CollatzResearch.WordTrace tailWord_5705300 prefixEnd_5705300 2929561178096633221211809 := by
  unfold tailWord_5705300
  simp only [CollatzResearch.WordTrace]
  refine ⟨104044693115339981255072677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138726257487119975006763569 104044693115339981255072677)
  ·
    refine ⟨19508379959126246485326127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104044693115339981255072677 19508379959126246485326127)
    ·
      refine ⟨29262569938689369727989191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19508379959126246485326127 29262569938689369727989191)
      ·
        refine ⟨43893854908034054591983787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29262569938689369727989191 43893854908034054591983787)
        ·
          refine ⟨65840782362051081887975681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43893854908034054591983787 65840782362051081887975681)
          ·
            refine ⟨49380586771538311415981761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65840782362051081887975681 49380586771538311415981761)
            ·
              refine ⟨37035440078653733561986321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49380586771538311415981761 37035440078653733561986321)
              ·
                refine ⟨27776580058990300171489741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37035440078653733561986321 27776580058990300171489741)
                ·
                  refine ⟨10416217522121362564308653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27776580058990300171489741 10416217522121362564308653)
                  ·
                    refine ⟨3906081570795510961615745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10416217522121362564308653 3906081570795510961615745)
                    ·
                      refine ⟨2929561178096633221211809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3906081570795510961615745 2929561178096633221211809)
                      ·
                        rfl

theorem cell23_5705300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 2, 3, 3, 2].length) (baseStart_5705300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5705300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5705300 prefixEnd_5705300 := by exact prefixLift 5705300
  have htrace : WordTrace (prefixWord ++ tailWord_5705300) baseStart_5705300 baseEnd_5705300 := by
    simpa [prefixWord, tailWord_5705300, baseEnd_5705300] using wordTrace_append hprefix tailTrace_5705300
  have hstable : (prefixWord ++ tailWord_5705300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5705300).length < 2 ^ (prefixWord ++ tailWord_5705300).sum := by decide
  have hdescent : baseEnd_5705300 < baseStart_5705300 := by decide
  rcases family_descends (prefixWord ++ tailWord_5705300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5705306 : List Nat := [3, 1, 1, 2, 1, 1, 1, 5, 2, 6]
def baseStart_5705306 : Nat := 118140960795 + 5705306 * 2 ^ 59
def prefixEnd_5705306 : Nat := 4983230072969 + 3 ^ 40 * 5705306 * 2
def baseEnd_5705306 : Nat := 976521419660186732578927

theorem tailTrace_5705306 : CollatzResearch.WordTrace tailWord_5705306 prefixEnd_5705306 976521419660186732578927 := by
  unfold tailWord_5705306
  simp only [CollatzResearch.WordTrace]
  refine ⟨52022401267164556383715943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138726403379105483689909181 52022401267164556383715943)
  ·
    refine ⟨78033601900746834575573915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52022401267164556383715943 78033601900746834575573915)
    ·
      refine ⟨117050402851120251863360873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78033601900746834575573915 117050402851120251863360873)
      ·
        refine ⟨87787802138340188897520655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117050402851120251863360873 87787802138340188897520655)
        ·
          refine ⟨131681703207510283346280983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87787802138340188897520655 131681703207510283346280983)
          ·
            refine ⟨197522554811265425019421475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131681703207510283346280983 197522554811265425019421475)
            ·
              refine ⟨296283832216898137529132213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197522554811265425019421475 296283832216898137529132213)
              ·
                refine ⟨27776609270334200393356145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 296283832216898137529132213 27776609270334200393356145)
                ·
                  refine ⟨20832456952750650295017109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27776609270334200393356145 20832456952750650295017109)
                  ·
                    refine ⟨976521419660186732578927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20832456952750650295017109 976521419660186732578927)
                    ·
                      rfl

theorem cell23_5705306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 5, 2, 6].length) (baseStart_5705306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5705306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5705306 prefixEnd_5705306 := by exact prefixLift 5705306
  have htrace : WordTrace (prefixWord ++ tailWord_5705306) baseStart_5705306 baseEnd_5705306 := by
    simpa [prefixWord, tailWord_5705306, baseEnd_5705306] using wordTrace_append hprefix tailTrace_5705306
  have hstable : (prefixWord ++ tailWord_5705306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5705306).length < 2 ^ (prefixWord ++ tailWord_5705306).sum := by decide
  have hdescent : baseEnd_5705306 < baseStart_5705306 := by decide
  rcases family_descends (prefixWord ++ tailWord_5705306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5705317 : List Nat := [1, 3, 1, 3, 3, 1, 3, 2, 1, 3, 2]
def baseStart_5705317 : Nat := 118140960795 + 5705317 * 2 ^ 59
def prefixEnd_5705317 : Nat := 4983230072969 + 3 ^ 40 * 5705317 * 2
def baseEnd_5705317 : Nat := 2929569907267759654699231

theorem tailTrace_5705317 : CollatzResearch.WordTrace tailWord_5705317 prefixEnd_5705317 2929569907267759654699231 := by
  unfold tailWord_5705317
  simp only [CollatzResearch.WordTrace]
  refine ⟨208090006271618374413514205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138726670847745582942342803 208090006271618374413514205)
  ·
    refine ⟨78033752351856890405067827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208090006271618374413514205 78033752351856890405067827)
    ·
      refine ⟨117050628527785335607601741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78033752351856890405067827 117050628527785335607601741)
      ·
        refine ⟨43893985697919500852850653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117050628527785335607601741 43893985697919500852850653)
        ·
          refine ⟨16460244636719812819818995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43893985697919500852850653 16460244636719812819818995)
          ·
            refine ⟨24690366955079719229728493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16460244636719812819818995 24690366955079719229728493)
            ·
              refine ⟨9258887608154894711148185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24690366955079719229728493 9258887608154894711148185)
              ·
                refine ⟨6944165706116171033361139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9258887608154894711148185 6944165706116171033361139)
                ·
                  refine ⟨10416248559174256550041709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6944165706116171033361139 10416248559174256550041709)
                  ·
                    refine ⟨3906093209690346206265641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10416248559174256550041709 3906093209690346206265641)
                    ·
                      refine ⟨2929569907267759654699231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3906093209690346206265641 2929569907267759654699231)
                      ·
                        rfl

theorem cell23_5705317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 2, 1, 3, 2].length) (baseStart_5705317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5705317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5705317 prefixEnd_5705317 := by exact prefixLift 5705317
  have htrace : WordTrace (prefixWord ++ tailWord_5705317) baseStart_5705317 baseEnd_5705317 := by
    simpa [prefixWord, tailWord_5705317, baseEnd_5705317] using wordTrace_append hprefix tailTrace_5705317
  have hstable : (prefixWord ++ tailWord_5705317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5705317).length < 2 ^ (prefixWord ++ tailWord_5705317).sum := by decide
  have hdescent : baseEnd_5705317 < baseStart_5705317 := by decide
  rcases family_descends (prefixWord ++ tailWord_5705317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5705330 : List Nat := [3, 2, 1, 2, 3, 1, 1, 1, 3, 4, 2]
def baseStart_5705330 : Nat := 118140960795 + 5705330 * 2 ^ 59
def prefixEnd_5705330 : Nat := 4983230072969 + 3 ^ 40 * 5705330 * 2
def baseEnd_5705330 : Nat := 2929576582516268103836671

theorem tailTrace_5705330 : CollatzResearch.WordTrace tailWord_5705330 prefixEnd_5705330 2929576582516268103836671 := by
  unfold tailWord_5705330
  simp only [CollatzResearch.WordTrace]
  refine ⟨52022620105142819408434361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138726986947047518422491629 52022620105142819408434361)
  ·
    refine ⟨39016965078857114556325771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52022620105142819408434361 39016965078857114556325771)
    ·
      refine ⟨58525447618285671834488657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39016965078857114556325771 58525447618285671834488657)
      ·
        refine ⟨43894085713714253875866493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58525447618285671834488657 43894085713714253875866493)
        ·
          refine ⟨16460282142642845203449935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43894085713714253875866493 16460282142642845203449935)
          ·
            refine ⟨24690423213964267805174903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16460282142642845203449935 24690423213964267805174903)
            ·
              refine ⟨37035634820946401707762355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24690423213964267805174903 37035634820946401707762355)
              ·
                refine ⟨55553452231419602561643533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37035634820946401707762355 55553452231419602561643533)
                ·
                  refine ⟨20832544586782350960616325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55553452231419602561643533 20832544586782350960616325)
                  ·
                    refine ⟨3906102110021690805115561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20832544586782350960616325 3906102110021690805115561)
                    ·
                      refine ⟨2929576582516268103836671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3906102110021690805115561 2929576582516268103836671)
                      ·
                        rfl

theorem cell23_5705330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 1, 3, 4, 2].length) (baseStart_5705330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5705330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5705330 prefixEnd_5705330 := by exact prefixLift 5705330
  have htrace : WordTrace (prefixWord ++ tailWord_5705330) baseStart_5705330 baseEnd_5705330 := by
    simpa [prefixWord, tailWord_5705330, baseEnd_5705330] using wordTrace_append hprefix tailTrace_5705330
  have hstable : (prefixWord ++ tailWord_5705330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5705330).length < 2 ^ (prefixWord ++ tailWord_5705330).sum := by decide
  have hdescent : baseEnd_5705330 < baseStart_5705330 := by decide
  rcases family_descends (prefixWord ++ tailWord_5705330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5705364 : List Nat := [2, 4, 2, 2, 2, 1, 2, 1, 1, 4, 2]
def baseStart_5705364 : Nat := 118140960795 + 5705364 * 2 ^ 59
def prefixEnd_5705364 : Nat := 4983230072969 + 3 ^ 40 * 5705364 * 2
def baseEnd_5705364 : Nat := 2929594040858520970811515

theorem tailTrace_5705364 : CollatzResearch.WordTrace tailWord_5705364 prefixEnd_5705364 2929594040858520970811515 := by
  unfold tailWord_5705364
  simp only [CollatzResearch.WordTrace]
  refine ⟨104045860251224050720237573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138727813668298734293650097 104045860251224050720237573)
  ·
    refine ⟨19508598797104509510044545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104045860251224050720237573 19508598797104509510044545)
    ·
      refine ⟨14631449097828382132533409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19508598797104509510044545 14631449097828382132533409)
      ·
        refine ⟨10973586823371286599400057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14631449097828382132533409 10973586823371286599400057)
        ·
          refine ⟨8230190117528464949550043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10973586823371286599400057 8230190117528464949550043)
          ·
            refine ⟨12345285176292697424325065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8230190117528464949550043 12345285176292697424325065)
            ·
              refine ⟨9258963882219523068243799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12345285176292697424325065 9258963882219523068243799)
              ·
                refine ⟨13888445823329284602365699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9258963882219523068243799 13888445823329284602365699)
                ·
                  refine ⟨20832668734993926903548549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13888445823329284602365699 20832668734993926903548549)
                  ·
                    refine ⟨3906125387811361294415353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20832668734993926903548549 3906125387811361294415353)
                    ·
                      refine ⟨2929594040858520970811515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3906125387811361294415353 2929594040858520970811515)
                      ·
                        rfl

theorem cell23_5705364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 1, 1, 4, 2].length) (baseStart_5705364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5705364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5705364 prefixEnd_5705364 := by exact prefixLift 5705364
  have htrace : WordTrace (prefixWord ++ tailWord_5705364) baseStart_5705364 baseEnd_5705364 := by
    simpa [prefixWord, tailWord_5705364, baseEnd_5705364] using wordTrace_append hprefix tailTrace_5705364
  have hstable : (prefixWord ++ tailWord_5705364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5705364).length < 2 ^ (prefixWord ++ tailWord_5705364).sum := by decide
  have hdescent : baseEnd_5705364 < baseStart_5705364 := by decide
  rcases family_descends (prefixWord ++ tailWord_5705364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5705398 : List Nat := [5, 1, 3, 1, 1, 3, 1, 2, 2, 2, 2]
def baseStart_5705398 : Nat := 118140960795 + 5705398 * 2 ^ 59
def prefixEnd_5705398 : Nat := 4983230072969 + 3 ^ 40 * 5705398 * 2
def baseEnd_5705398 : Nat := 2929611499200773837786359

theorem tailTrace_5705398 : CollatzResearch.WordTrace tailWord_5705398 prefixEnd_5705398 2929611499200773837786359 := by
  unfold tailWord_5705398
  simp only [CollatzResearch.WordTrace]
  refine ⟨13005810036520307827950803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 138728640389549950164808565 13005810036520307827950803)
  ·
    refine ⟨19508715054780461741926205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13005810036520307827950803 19508715054780461741926205)
    ·
      refine ⟨7315768145542673153222327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19508715054780461741926205 7315768145542673153222327)
      ·
        refine ⟨10973652218314009729833491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7315768145542673153222327 10973652218314009729833491)
        ·
          refine ⟨16460478327471014594750237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10973652218314009729833491 16460478327471014594750237)
          ·
            refine ⟨6172679372801630473031339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16460478327471014594750237 6172679372801630473031339)
            ·
              refine ⟨9259019059202445709547009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6172679372801630473031339 9259019059202445709547009)
              ·
                refine ⟨6944264294401834282160257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9259019059202445709547009 6944264294401834282160257)
                ·
                  refine ⟨5208198220801375711620193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6944264294401834282160257 5208198220801375711620193)
                  ·
                    refine ⟨3906148665601031783715145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5208198220801375711620193 3906148665601031783715145)
                    ·
                      refine ⟨2929611499200773837786359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3906148665601031783715145 2929611499200773837786359)
                      ·
                        rfl

theorem cell23_5705398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 2, 2, 2, 2].length) (baseStart_5705398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5705398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5705398 prefixEnd_5705398 := by exact prefixLift 5705398
  have htrace : WordTrace (prefixWord ++ tailWord_5705398) baseStart_5705398 baseEnd_5705398 := by
    simpa [prefixWord, tailWord_5705398, baseEnd_5705398] using wordTrace_append hprefix tailTrace_5705398
  have hstable : (prefixWord ++ tailWord_5705398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5705398).length < 2 ^ (prefixWord ++ tailWord_5705398).sum := by decide
  have hdescent : baseEnd_5705398 < baseStart_5705398 := by decide
  rcases family_descends (prefixWord ++ tailWord_5705398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5705403 : List Nat := [1, 1, 1, 1, 1, 2, 3, 6, 2, 1, 4]
def baseStart_5705403 : Nat := 118140960795 + 5705403 * 2 ^ 59
def prefixEnd_5705403 : Nat := 4983230072969 + 3 ^ 40 * 5705403 * 2
def baseEnd_5705403 : Nat := 2929614066604046318223835

theorem tailTrace_5705403 : CollatzResearch.WordTrace tailWord_5705403 prefixEnd_5705403 2929614066604046318223835 := by
  unfold tailWord_5705403
  simp only [CollatzResearch.WordTrace]
  refine ⟨208093142949306811101144863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138728761966204540734096575 208093142949306811101144863)
  ·
    refine ⟨312139714423960216651717295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208093142949306811101144863 312139714423960216651717295)
    ·
      refine ⟨468209571635940324977575943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312139714423960216651717295 468209571635940324977575943)
      ·
        refine ⟨702314357453910487466363915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 468209571635940324977575943 702314357453910487466363915)
        ·
          refine ⟨1053471536180865731199545873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 702314357453910487466363915 1053471536180865731199545873)
          ·
            refine ⟨790103652135649298399659405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1053471536180865731199545873 790103652135649298399659405)
            ·
              refine ⟨296288869550868486899872277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 790103652135649298399659405 296288869550868486899872277)
              ·
                refine ⟨13888540760196960323431513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 296288869550868486899872277 13888540760196960323431513)
                ·
                  refine ⟨10416405570147720242573635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13888540760196960323431513 10416405570147720242573635)
                  ·
                    refine ⟨15624608355221580363860453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10416405570147720242573635 15624608355221580363860453)
                    ·
                      refine ⟨2929614066604046318223835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15624608355221580363860453 2929614066604046318223835)
                      ·
                        rfl

theorem cell23_5705403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6, 2, 1, 4].length) (baseStart_5705403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5705403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5705403 prefixEnd_5705403 := by exact prefixLift 5705403
  have htrace : WordTrace (prefixWord ++ tailWord_5705403) baseStart_5705403 baseEnd_5705403 := by
    simpa [prefixWord, tailWord_5705403, baseEnd_5705403] using wordTrace_append hprefix tailTrace_5705403
  have hstable : (prefixWord ++ tailWord_5705403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5705403).length < 2 ^ (prefixWord ++ tailWord_5705403).sum := by decide
  have hdescent : baseEnd_5705403 < baseStart_5705403 := by decide
  rcases family_descends (prefixWord ++ tailWord_5705403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5705413 : List Nat := [1, 3, 1, 1, 1, 1, 2, 2, 7, 4]
def baseStart_5705413 : Nat := 118140960795 + 5705413 * 2 ^ 59
def prefixEnd_5705413 : Nat := 4983230072969 + 3 ^ 40 * 5705413 * 2
def baseEnd_5705413 : Nat := 976539733803530426366263

theorem tailTrace_5705413 : CollatzResearch.WordTrace tailWord_5705413 prefixEnd_5705413 976539733803530426366263 := by
  unfold tailWord_5705413
  simp only [CollatzResearch.WordTrace]
  refine ⟨208093507679270582809008893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138729005119513721872672595 208093507679270582809008893)
  ·
    refine ⟨78035065379726468553378335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208093507679270582809008893 78035065379726468553378335)
    ·
      refine ⟨117052598069589702830067503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78035065379726468553378335 117052598069589702830067503)
      ·
        refine ⟨175578897104384554245101255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117052598069589702830067503 175578897104384554245101255)
        ·
          refine ⟨263368345656576831367651883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175578897104384554245101255 263368345656576831367651883)
          ·
            refine ⟨395052518484865247051477825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 263368345656576831367651883 395052518484865247051477825)
            ·
              refine ⟨296289388863648935288608369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 395052518484865247051477825 296289388863648935288608369)
              ·
                refine ⟨222217041647736701466456277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 296289388863648935288608369 222217041647736701466456277)
                ·
                  refine ⟨5208211913618828940620069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 222217041647736701466456277 5208211913618828940620069)
                  ·
                    refine ⟨976539733803530426366263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5208211913618828940620069 976539733803530426366263)
                    ·
                      rfl

theorem cell23_5705413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 7, 4].length) (baseStart_5705413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5705413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5705413 prefixEnd_5705413 := by exact prefixLift 5705413
  have htrace : WordTrace (prefixWord ++ tailWord_5705413) baseStart_5705413 baseEnd_5705413 := by
    simpa [prefixWord, tailWord_5705413, baseEnd_5705413] using wordTrace_append hprefix tailTrace_5705413
  have hstable : (prefixWord ++ tailWord_5705413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5705413).length < 2 ^ (prefixWord ++ tailWord_5705413).sum := by decide
  have hdescent : baseEnd_5705413 < baseStart_5705413 := by decide
  rcases family_descends (prefixWord ++ tailWord_5705413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5705414 : List Nat := [6, 1, 2, 1, 1, 1, 2, 1, 2, 3, 3]
def baseStart_5705414 : Nat := 118140960795 + 5705414 * 2 ^ 59
def prefixEnd_5705414 : Nat := 4983230072969 + 3 ^ 40 * 5705414 * 2
def baseEnd_5705414 : Nat := 2929619714891245775186285

theorem tailTrace_5705414 : CollatzResearch.WordTrace tailWord_5705414 prefixEnd_5705414 2929619714891245775186285 := by
  unfold tailWord_5705414
  simp only [CollatzResearch.WordTrace]
  refine ⟨6502923254758342499368603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 138729029434844639986530197 6502923254758342499368603)
  ·
    refine ⟨9754384882137513749052905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6502923254758342499368603 9754384882137513749052905)
    ·
      refine ⟨7315788661603135311789679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9754384882137513749052905 7315788661603135311789679)
      ·
        refine ⟨10973682992404702967684519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7315788661603135311789679 10973682992404702967684519)
        ·
          refine ⟨16460524488607054451526779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10973682992404702967684519 16460524488607054451526779)
          ·
            refine ⟨24690786732910581677290169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16460524488607054451526779 24690786732910581677290169)
            ·
              refine ⟨18518090049682936257967627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24690786732910581677290169 18518090049682936257967627)
              ·
                refine ⟨27777135074524404386951441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18518090049682936257967627 27777135074524404386951441)
                ·
                  refine ⟨20832851305893303290213581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27777135074524404386951441 20832851305893303290213581)
                  ·
                    refine ⟨7812319239709988733830093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20832851305893303290213581 7812319239709988733830093)
                    ·
                      refine ⟨2929619714891245775186285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7812319239709988733830093 2929619714891245775186285)
                      ·
                        rfl

theorem cell23_5705414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_5705414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5705414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5705414 prefixEnd_5705414 := by exact prefixLift 5705414
  have htrace : WordTrace (prefixWord ++ tailWord_5705414) baseStart_5705414 baseEnd_5705414 := by
    simpa [prefixWord, tailWord_5705414, baseEnd_5705414] using wordTrace_append hprefix tailTrace_5705414
  have hstable : (prefixWord ++ tailWord_5705414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5705414).length < 2 ^ (prefixWord ++ tailWord_5705414).sum := by decide
  have hdescent : baseEnd_5705414 < baseStart_5705414 := by decide
  rcases family_descends (prefixWord ++ tailWord_5705414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5705504 : List Nat := [2, 1, 1, 5, 1, 1, 2, 5, 1, 1, 3]
def baseStart_5705504 : Nat := 118140960795 + 5705504 * 2 ^ 59
def prefixEnd_5705504 : Nat := 4983230072969 + 3 ^ 40 * 5705504 * 2
def baseEnd_5705504 : Nat := 2929665928150150423060871

theorem tailTrace_5705504 : CollatzResearch.WordTrace tailWord_5705504 prefixEnd_5705504 2929665928150150423060871 := by
  unfold tailWord_5705504
  simp only [CollatzResearch.WordTrace]
  refine ⟨104048413360970452675285783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138731217814627270233714377 104048413360970452675285783)
  ·
    refine ⟨156072620041455679012928675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104048413360970452675285783 156072620041455679012928675)
    ·
      refine ⟨234108930062183518519393013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156072620041455679012928675 234108930062183518519393013)
      ·
        refine ⟨21947712193329704861193095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 234108930062183518519393013 21947712193329704861193095)
        ·
          refine ⟨32921568289994557291789643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21947712193329704861193095 32921568289994557291789643)
          ·
            refine ⟨49382352434991835937684465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32921568289994557291789643 49382352434991835937684465)
            ·
              refine ⟨37036764326243876953263349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49382352434991835937684465 37036764326243876953263349)
              ·
                refine ⟨3472196655585363464368439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37036764326243876953263349 3472196655585363464368439)
                ·
                  refine ⟨5208294983378045196552659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3472196655585363464368439 5208294983378045196552659)
                  ·
                    refine ⟨7812442475067067794828989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5208294983378045196552659 7812442475067067794828989)
                    ·
                      refine ⟨2929665928150150423060871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7812442475067067794828989 2929665928150150423060871)
                      ·
                        rfl

theorem cell23_5705504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 5, 1, 1, 3].length) (baseStart_5705504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5705504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5705504 prefixEnd_5705504 := by exact prefixLift 5705504
  have htrace : WordTrace (prefixWord ++ tailWord_5705504) baseStart_5705504 baseEnd_5705504 := by
    simpa [prefixWord, tailWord_5705504, baseEnd_5705504] using wordTrace_append hprefix tailTrace_5705504
  have hstable : (prefixWord ++ tailWord_5705504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5705504).length < 2 ^ (prefixWord ++ tailWord_5705504).sum := by decide
  have hdescent : baseEnd_5705504 < baseStart_5705504 := by decide
  rcases family_descends (prefixWord ++ tailWord_5705504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5705521 : List Nat := [1, 2, 2, 3, 2, 2, 4, 2, 1, 1, 3]
def baseStart_5705521 : Nat := 118140960795 + 5705521 * 2 ^ 59
def prefixEnd_5705521 : Nat := 4983230072969 + 3 ^ 40 * 5705521 * 2
def baseEnd_5705521 : Nat := 2929674657321276856548293

theorem tailTrace_5705521 : CollatzResearch.WordTrace tailWord_5705521 prefixEnd_5705521 2929674657321276856548293 := by
  unfold tailWord_5705521
  simp only [CollatzResearch.WordTrace]
  refine ⟨208097446762879317253940417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138731631175252878169293611 208097446762879317253940417)
  ·
    refine ⟨156073085072159487940455313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208097446762879317253940417 156073085072159487940455313)
    ·
      refine ⟨117054813804119615955341485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156073085072159487940455313 117054813804119615955341485)
      ·
        refine ⟨43895555176544855983253057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117054813804119615955341485 43895555176544855983253057)
        ·
          refine ⟨32921666382408641987439793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43895555176544855983253057 32921666382408641987439793)
          ·
            refine ⟨24691249786806481490579845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32921666382408641987439793 24691249786806481490579845)
            ·
              refine ⟨4629609335026215279483721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24691249786806481490579845 4629609335026215279483721)
              ·
                refine ⟨3472207001269661459612791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4629609335026215279483721 3472207001269661459612791)
                ·
                  refine ⟨5208310501904492189419187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3472207001269661459612791 5208310501904492189419187)
                  ·
                    refine ⟨7812465752856738284128781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5208310501904492189419187 7812465752856738284128781)
                    ·
                      refine ⟨2929674657321276856548293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7812465752856738284128781 2929674657321276856548293)
                      ·
                        rfl

theorem cell23_5705521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 4, 2, 1, 1, 3].length) (baseStart_5705521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5705521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5705521 prefixEnd_5705521 := by exact prefixLift 5705521
  have htrace : WordTrace (prefixWord ++ tailWord_5705521) baseStart_5705521 baseEnd_5705521 := by
    simpa [prefixWord, tailWord_5705521, baseEnd_5705521] using wordTrace_append hprefix tailTrace_5705521
  have hstable : (prefixWord ++ tailWord_5705521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5705521).length < 2 ^ (prefixWord ++ tailWord_5705521).sum := by decide
  have hdescent : baseEnd_5705521 < baseStart_5705521 := by decide
  rcases family_descends (prefixWord ++ tailWord_5705521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5705544 : List Nat := [2, 1, 3, 1, 1, 5, 1, 2, 3, 2, 2]
def baseStart_5705544 : Nat := 118140960795 + 5705544 * 2 ^ 59
def prefixEnd_5705544 : Nat := 4983230072969 + 3 ^ 40 * 5705544 * 2
def baseEnd_5705544 : Nat := 2929686467376330266560687

theorem tailTrace_5705544 : CollatzResearch.WordTrace tailWord_5705544 prefixEnd_5705544 2929686467376330266560687 := by
  unfold tailWord_5705544
  simp only [CollatzResearch.WordTrace]
  refine ⟨104049142820897996091013843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138732190427863994788018457 104049142820897996091013843)
  ·
    refine ⟨156073714231346994136520765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104049142820897996091013843 156073714231346994136520765)
    ·
      refine ⟨58527642836755122801195287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156073714231346994136520765 58527642836755122801195287)
      ·
        refine ⟨87791464255132684201792931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58527642836755122801195287 87791464255132684201792931)
        ·
          refine ⟨131687196382699026302689397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87791464255132684201792931 131687196382699026302689397)
          ·
            refine ⟨12345674660878033715877131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 131687196382699026302689397 12345674660878033715877131)
            ·
              refine ⟨18518511991317050573815697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12345674660878033715877131 18518511991317050573815697)
              ·
                refine ⟨13888883993487787930361773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18518511991317050573815697 13888883993487787930361773)
                ·
                  refine ⟨5208331497557920473885665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13888883993487787930361773 5208331497557920473885665)
                  ·
                    refine ⟨3906248623168440355414249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5208331497557920473885665 3906248623168440355414249)
                    ·
                      refine ⟨2929686467376330266560687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3906248623168440355414249 2929686467376330266560687)
                      ·
                        rfl

theorem cell23_5705544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 2, 3, 2, 2].length) (baseStart_5705544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5705544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5705544 prefixEnd_5705544 := by exact prefixLift 5705544
  have htrace : WordTrace (prefixWord ++ tailWord_5705544) baseStart_5705544 baseEnd_5705544 := by
    simpa [prefixWord, tailWord_5705544, baseEnd_5705544] using wordTrace_append hprefix tailTrace_5705544
  have hstable : (prefixWord ++ tailWord_5705544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5705544).length < 2 ^ (prefixWord ++ tailWord_5705544).sum := by decide
  have hdescent : baseEnd_5705544 < baseStart_5705544 := by decide
  rcases family_descends (prefixWord ++ tailWord_5705544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5705561 : List Nat := [1, 2, 1, 2, 2, 3, 4, 3, 1, 2, 2]
def baseStart_5705561 : Nat := 118140960795 + 5705561 * 2 ^ 59
def prefixEnd_5705561 : Nat := 4983230072969 + 3 ^ 40 * 5705561 * 2
def baseEnd_5705561 : Nat := 2929695196547456700048109

theorem tailTrace_5705561 : CollatzResearch.WordTrace tailWord_5705561 prefixEnd_5705561 2929695196547456700048109 := by
  unfold tailWord_5705561
  simp only [CollatzResearch.WordTrace]
  refine ⟨208098905682734404085396537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138732603788489602723597691 208098905682734404085396537)
  ·
    refine ⟨156074179262050803064047403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208098905682734404085396537 156074179262050803064047403)
    ·
      refine ⟨234111268893076204596071105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156074179262050803064047403 234111268893076204596071105)
      ·
        refine ⟨175583451669807153447053329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 234111268893076204596071105 175583451669807153447053329)
        ·
          refine ⟨131687588752355365085289997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175583451669807153447053329 131687588752355365085289997)
          ·
            refine ⟨49382845782133261906983749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 131687588752355365085289997 49382845782133261906983749)
            ·
              refine ⟨9259283584149986607559453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49382845782133261906983749 9259283584149986607559453)
              ·
                refine ⟨3472231344056244977834795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9259283584149986607559453 3472231344056244977834795)
                ·
                  refine ⟨5208347016084367466752193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3472231344056244977834795 5208347016084367466752193)
                  ·
                    refine ⟨3906260262063275600064145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5208347016084367466752193 3906260262063275600064145)
                    ·
                      refine ⟨2929695196547456700048109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3906260262063275600064145 2929695196547456700048109)
                      ·
                        rfl

theorem cell23_5705561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 3, 1, 2, 2].length) (baseStart_5705561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5705561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5705561 prefixEnd_5705561 := by exact prefixLift 5705561
  have htrace : WordTrace (prefixWord ++ tailWord_5705561) baseStart_5705561 baseEnd_5705561 := by
    simpa [prefixWord, tailWord_5705561, baseEnd_5705561] using wordTrace_append hprefix tailTrace_5705561
  have hstable : (prefixWord ++ tailWord_5705561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5705561).length < 2 ^ (prefixWord ++ tailWord_5705561).sum := by decide
  have hdescent : baseEnd_5705561 < baseStart_5705561 := by decide
  rcases family_descends (prefixWord ++ tailWord_5705561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5705571 : List Nat := [1, 1, 1, 5, 5, 1, 1, 2, 2, 4]
def baseStart_5705571 : Nat := 118140960795 + 5705571 * 2 ^ 59
def prefixEnd_5705571 : Nat := 4983230072969 + 3 ^ 40 * 5705571 * 2
def baseEnd_5705571 : Nat := 976566777118000553641021

theorem tailTrace_5705571 : CollatzResearch.WordTrace tailWord_5705571 prefixEnd_5705571 976566777118000553641021 := by
  unfold tailWord_5705571
  simp only [CollatzResearch.WordTrace]
  refine ⟨208099270412698175793260567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138732846941798783862173711 208099270412698175793260567)
  ·
    refine ⟨312148905619047263689890851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208099270412698175793260567 312148905619047263689890851)
    ·
      refine ⟨468223358428570895534836277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312148905619047263689890851 468223358428570895534836277)
      ·
        refine ⟨43895939852678521456390901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 468223358428570895534836277 43895939852678521456390901)
        ·
          refine ⟨4115244361188611386536647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 43895939852678521456390901 4115244361188611386536647)
          ·
            refine ⟨6172866541782917079804971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4115244361188611386536647 6172866541782917079804971)
            ·
              refine ⟨9259299812674375619707457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6172866541782917079804971 9259299812674375619707457)
              ·
                refine ⟨6944474859505781714780593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9259299812674375619707457 6944474859505781714780593)
                ·
                  refine ⟨5208356144629336286085445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6944474859505781714780593 5208356144629336286085445)
                  ·
                    refine ⟨976566777118000553641021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5208356144629336286085445 976566777118000553641021)
                    ·
                      rfl

theorem cell23_5705571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 2, 2, 4].length) (baseStart_5705571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5705571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5705571 prefixEnd_5705571 := by exact prefixLift 5705571
  have htrace : WordTrace (prefixWord ++ tailWord_5705571) baseStart_5705571 baseEnd_5705571 := by
    simpa [prefixWord, tailWord_5705571, baseEnd_5705571] using wordTrace_append hprefix tailTrace_5705571
  have hstable : (prefixWord ++ tailWord_5705571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5705571).length < 2 ^ (prefixWord ++ tailWord_5705571).sum := by decide
  have hdescent : baseEnd_5705571 < baseStart_5705571 := by decide
  rcases family_descends (prefixWord ++ tailWord_5705571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5705578 : List Nat := [3, 1, 3, 4, 1, 1, 2, 1, 3, 2, 2]
def baseStart_5705578 : Nat := 118140960795 + 5705578 * 2 ^ 59
def prefixEnd_5705578 : Nat := 4983230072969 + 3 ^ 40 * 5705578 * 2
def baseEnd_5705578 : Nat := 2929703925718583133535531

theorem tailTrace_5705578 : CollatzResearch.WordTrace tailWord_5705578 prefixEnd_5705578 2929703925718583133535531 := by
  unfold tailWord_5705578
  simp only [CollatzResearch.WordTrace]
  refine ⟨52024881430918203997191347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138733017149115210659176925 52024881430918203997191347)
  ·
    refine ⟨78037322146377305995787021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52024881430918203997191347 78037322146377305995787021)
    ·
      refine ⟨29263995804891489748420133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78037322146377305995787021 29263995804891489748420133)
      ·
        refine ⟨5486999213417154327828775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29263995804891489748420133 5486999213417154327828775)
        ·
          refine ⟨8230498820125731491743163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5486999213417154327828775 8230498820125731491743163)
          ·
            refine ⟨12345748230188597237614745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8230498820125731491743163 12345748230188597237614745)
            ·
              refine ⟨9259311172641447928211059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12345748230188597237614745 9259311172641447928211059)
              ·
                refine ⟨13888966758962171892316589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9259311172641447928211059 13888966758962171892316589)
                ·
                  refine ⟨5208362534610814459618721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13888966758962171892316589 5208362534610814459618721)
                  ·
                    refine ⟨3906271900958110844714041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5208362534610814459618721 3906271900958110844714041)
                    ·
                      refine ⟨2929703925718583133535531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3906271900958110844714041 2929703925718583133535531)
                      ·
                        rfl

theorem cell23_5705578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_5705578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5705578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5705578 prefixEnd_5705578 := by exact prefixLift 5705578
  have htrace : WordTrace (prefixWord ++ tailWord_5705578) baseStart_5705578 baseEnd_5705578 := by
    simpa [prefixWord, tailWord_5705578, baseEnd_5705578] using wordTrace_append hprefix tailTrace_5705578
  have hstable : (prefixWord ++ tailWord_5705578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5705578).length < 2 ^ (prefixWord ++ tailWord_5705578).sum := by decide
  have hdescent : baseEnd_5705578 < baseStart_5705578 := by decide
  rcases family_descends (prefixWord ++ tailWord_5705578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5705601 : List Nat := [1, 2, 4, 4, 2, 1, 2, 7]
def baseStart_5705601 : Nat := 118140960795 + 5705601 * 2 ^ 59
def prefixEnd_5705601 : Nat := 4983230072969 + 3 ^ 40 * 5705601 * 2
def baseEnd_5705601 : Nat := 108507990213838390501775

theorem tailTrace_5705601 : CollatzResearch.WordTrace tailWord_5705601 prefixEnd_5705601 108507990213838390501775 := by
  unfold tailWord_5705601
  simp only [CollatzResearch.WordTrace]
  refine ⟨208100364602589490916852657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138733576401726327277901771 208100364602589490916852657)
  ·
    refine ⟨156075273451942118187639493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208100364602589490916852657 156075273451942118187639493)
    ·
      refine ⟨29264113772239147160182405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 156075273451942118187639493 29264113772239147160182405)
      ·
        refine ⟨5487021332294840092534201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29264113772239147160182405 5487021332294840092534201)
        ·
          refine ⟨4115265999221130069400651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5487021332294840092534201 4115265999221130069400651)
          ·
            refine ⟨6172898998831695104100977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4115265999221130069400651 6172898998831695104100977)
            ·
              refine ⟨4629674249123771328075733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6172898998831695104100977 4629674249123771328075733)
              ·
                refine ⟨108507990213838390501775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4629674249123771328075733 108507990213838390501775)
                ·
                  rfl

theorem cell23_5705601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 2, 7].length) (baseStart_5705601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5705601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5705601 prefixEnd_5705601 := by exact prefixLift 5705601
  have htrace : WordTrace (prefixWord ++ tailWord_5705601) baseStart_5705601 baseEnd_5705601 := by
    simpa [prefixWord, tailWord_5705601, baseEnd_5705601] using wordTrace_append hprefix tailTrace_5705601
  have hstable : (prefixWord ++ tailWord_5705601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5705601).length < 2 ^ (prefixWord ++ tailWord_5705601).sum := by decide
  have hdescent : baseEnd_5705601 < baseStart_5705601 := by decide
  rcases family_descends (prefixWord ++ tailWord_5705601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5705604 : List Nat := [2, 3, 2, 1, 1, 1, 3, 4, 1, 3, 2]
def baseStart_5705604 : Nat := 118140960795 + 5705604 * 2 ^ 59
def prefixEnd_5705604 : Nat := 4983230072969 + 3 ^ 40 * 5705604 * 2
def baseEnd_5705604 : Nat := 2929717276215600031810411

theorem tailTrace_5705604 : CollatzResearch.WordTrace tailWord_5705604 prefixEnd_5705604 2929717276215600031810411 := by
  unfold tailWord_5705604
  simp only [CollatzResearch.WordTrace]
  refine ⟨104050237010789311214605933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138733649347719081619474577 104050237010789311214605933)
  ·
    refine ⟨39018838879045991705477225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104050237010789311214605933 39018838879045991705477225)
    ·
      refine ⟨29264129159284493779107919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39018838879045991705477225 29264129159284493779107919)
      ·
        refine ⟨43896193738926740668661879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29264129159284493779107919 43896193738926740668661879)
        ·
          refine ⟨65844290608390111002992819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43896193738926740668661879 65844290608390111002992819)
          ·
            refine ⟨98766435912585166504489229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65844290608390111002992819 98766435912585166504489229)
            ·
              refine ⟨37037413467219437439183461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 98766435912585166504489229 37037413467219437439183461)
              ·
                refine ⟨6944515025103644519846899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37037413467219437439183461 6944515025103644519846899)
                ·
                  refine ⟨10416772537655466779770349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6944515025103644519846899 10416772537655466779770349)
                  ·
                    refine ⟨3906289701620800042413881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10416772537655466779770349 3906289701620800042413881)
                    ·
                      refine ⟨2929717276215600031810411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3906289701620800042413881 2929717276215600031810411)
                      ·
                        rfl

theorem cell23_5705604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 4, 1, 3, 2].length) (baseStart_5705604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5705604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5705604 prefixEnd_5705604 := by exact prefixLift 5705604
  have htrace : WordTrace (prefixWord ++ tailWord_5705604) baseStart_5705604 baseEnd_5705604 := by
    simpa [prefixWord, tailWord_5705604, baseEnd_5705604] using wordTrace_append hprefix tailTrace_5705604
  have hstable : (prefixWord ++ tailWord_5705604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5705604).length < 2 ^ (prefixWord ++ tailWord_5705604).sum := by decide
  have hdescent : baseEnd_5705604 < baseStart_5705604 := by decide
  rcases family_descends (prefixWord ++ tailWord_5705604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5705617 : List Nat := [1, 2, 2, 1, 1, 1, 4, 4, 1, 4, 2]
def baseStart_5705617 : Nat := 118140960795 + 5705617 * 2 ^ 59
def prefixEnd_5705617 : Nat := 4983230072969 + 3 ^ 40 * 5705617 * 2
def baseEnd_5705617 : Nat := 2929723951464108480947851

theorem tailTrace_5705617 : CollatzResearch.WordTrace tailWord_5705617 prefixEnd_5705617 2929723951464108480947851 := by
  unfold tailWord_5705617
  simp only [CollatzResearch.WordTrace]
  refine ⟨208100948170531525649435105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138733965447021017099623403 208100948170531525649435105)
  ·
    refine ⟨156075711127898644237076329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208100948170531525649435105 156075711127898644237076329)
    ·
      refine ⟨117056783345923983177807247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156075711127898644237076329 117056783345923983177807247)
      ·
        refine ⟨175585175018885974766710871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117056783345923983177807247 175585175018885974766710871)
        ·
          refine ⟨263377762528328962150066307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175585175018885974766710871 263377762528328962150066307)
          ·
            refine ⟨395066643792493443225099461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 263377762528328962150066307 395066643792493443225099461)
            ·
              refine ⟨74074995711092520604706149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 395066643792493443225099461 74074995711092520604706149)
              ·
                refine ⟨13889061695829847613382403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74074995711092520604706149 13889061695829847613382403)
                ·
                  refine ⟨20833592543744771420073605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13889061695829847613382403 20833592543744771420073605)
                  ·
                    refine ⟨3906298601952144641263801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20833592543744771420073605 3906298601952144641263801)
                    ·
                      refine ⟨2929723951464108480947851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3906298601952144641263801 2929723951464108480947851)
                      ·
                        rfl

theorem cell23_5705617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 4, 2].length) (baseStart_5705617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5705617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5705617 prefixEnd_5705617 := by exact prefixLift 5705617
  have htrace : WordTrace (prefixWord ++ tailWord_5705617) baseStart_5705617 baseEnd_5705617 := by
    simpa [prefixWord, tailWord_5705617, baseEnd_5705617] using wordTrace_append hprefix tailTrace_5705617
  have hstable : (prefixWord ++ tailWord_5705617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5705617).length < 2 ^ (prefixWord ++ tailWord_5705617).sum := by decide
  have hdescent : baseEnd_5705617 < baseStart_5705617 := by decide
  rcases family_descends (prefixWord ++ tailWord_5705617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5705680 : List Nat := [2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 5]
def baseStart_5705680 : Nat := 118140960795 + 5705680 * 2 ^ 59
def prefixEnd_5705680 : Nat := 4983230072969 + 3 ^ 40 * 5705680 * 2
def baseEnd_5705680 : Nat := 2929756300745341734460061

theorem tailTrace_5705680 : CollatzResearch.WordTrace tailWord_5705680 prefixEnd_5705680 2929756300745341734460061 := by
  unfold tailWord_5705680
  simp only [CollatzResearch.WordTrace]
  refine ⟨104051622984651643704489247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138735497312868858272652329 104051622984651643704489247)
  ·
    refine ⟨156077434476977465556733871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104051622984651643704489247 156077434476977465556733871)
    ·
      refine ⟨234116151715466198335100807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156077434476977465556733871 234116151715466198335100807)
      ·
        refine ⟨351174227573199297502651211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234116151715466198335100807 351174227573199297502651211)
        ·
          refine ⟨526761341359798946253976817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 351174227573199297502651211 526761341359798946253976817)
          ·
            refine ⟨395071006019849209690482613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 526761341359798946253976817 395071006019849209690482613)
            ·
              refine ⟨37037906814360863408482745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 395071006019849209690482613 37037906814360863408482745)
              ·
                refine ⟨27778430110770647556362059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37037906814360863408482745 27778430110770647556362059)
                ·
                  refine ⟨41667645166155971334543089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27778430110770647556362059 41667645166155971334543089)
                  ·
                    refine ⟨31250733874616978500907317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41667645166155971334543089 31250733874616978500907317)
                    ·
                      refine ⟨2929756300745341734460061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31250733874616978500907317 2929756300745341734460061)
                      ·
                        rfl

theorem cell23_5705680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 5].length) (baseStart_5705680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5705680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5705680 prefixEnd_5705680 := by exact prefixLift 5705680
  have htrace : WordTrace (prefixWord ++ tailWord_5705680) baseStart_5705680 baseEnd_5705680 := by
    simpa [prefixWord, tailWord_5705680, baseEnd_5705680] using wordTrace_append hprefix tailTrace_5705680
  have hstable : (prefixWord ++ tailWord_5705680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5705680).length < 2 ^ (prefixWord ++ tailWord_5705680).sum := by decide
  have hdescent : baseEnd_5705680 < baseStart_5705680 := by decide
  rcases family_descends (prefixWord ++ tailWord_5705680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5705747 : List Nat := [1, 1, 1, 2, 1, 4, 5, 2, 6]
def baseStart_5705747 : Nat := 118140960795 + 5705747 * 2 ^ 59
def prefixEnd_5705747 : Nat := 4983230072969 + 3 ^ 40 * 5705747 * 2
def baseEnd_5705747 : Nat := 325532300438799219146917

theorem tailTrace_5705747 : CollatzResearch.WordTrace tailWord_5705747 prefixEnd_5705747 325532300438799219146917 := by
  unfold tailWord_5705747
  simp only [CollatzResearch.WordTrace]
  refine ⟨208105689660060557851667495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138737126440040371901111663 208105689660060557851667495)
  ·
    refine ⟨312158534490090836777501243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208105689660060557851667495 312158534490090836777501243)
    ·
      refine ⟨468237801735136255166251865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312158534490090836777501243 468237801735136255166251865)
      ·
        refine ⟨351178351301352191374688899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 468237801735136255166251865 351178351301352191374688899)
        ·
          refine ⟨526767526952028287062033349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 351178351301352191374688899 526767526952028287062033349)
          ·
            refine ⟨98768911303505303824131253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 526767526952028287062033349 98768911303505303824131253)
            ·
              refine ⟨9259585434703622233512305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 98768911303505303824131253 9259585434703622233512305)
              ·
                refine ⟨6944689076027716675134229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9259585434703622233512305 6944689076027716675134229)
                ·
                  refine ⟨325532300438799219146917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6944689076027716675134229 325532300438799219146917)
                  ·
                    rfl

theorem cell23_5705747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 2, 6].length) (baseStart_5705747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5705747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5705747 prefixEnd_5705747 := by exact prefixLift 5705747
  have htrace : WordTrace (prefixWord ++ tailWord_5705747) baseStart_5705747 baseEnd_5705747 := by
    simpa [prefixWord, tailWord_5705747, baseEnd_5705747] using wordTrace_append hprefix tailTrace_5705747
  have hstable : (prefixWord ++ tailWord_5705747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5705747).length < 2 ^ (prefixWord ++ tailWord_5705747).sum := by decide
  have hdescent : baseEnd_5705747 < baseStart_5705747 := by decide
  rcases family_descends (prefixWord ++ tailWord_5705747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5705751 : List Nat := [1, 1, 3, 5, 2, 1, 2, 1, 3, 4]
def baseStart_5705751 : Nat := 118140960795 + 5705751 * 2 ^ 59
def prefixEnd_5705751 : Nat := 4983230072969 + 3 ^ 40 * 5705751 * 2
def baseEnd_5705751 : Nat := 976597585957270318890745

theorem tailTrace_5705751 : CollatzResearch.WordTrace tailWord_5705751 prefixEnd_5705751 976597585957270318890745 := by
  unfold tailWord_5705751
  simp only [CollatzResearch.WordTrace]
  refine ⟨208105835552046066534813107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138737223701364044356542071 208105835552046066534813107)
  ·
    refine ⟨312158753328069099802219661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208105835552046066534813107 312158753328069099802219661)
    ·
      refine ⟨117059532498025912425832373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 312158753328069099802219661 117059532498025912425832373)
      ·
        refine ⟨10974331171689929289921785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 117059532498025912425832373 10974331171689929289921785)
        ·
          refine ⟨8230748378767446967441339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10974331171689929289921785 8230748378767446967441339)
          ·
            refine ⟨12346122568151170451162009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8230748378767446967441339 12346122568151170451162009)
            ·
              refine ⟨9259591926113377838371507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12346122568151170451162009 9259591926113377838371507)
              ·
                refine ⟨13889387889170066757557261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9259591926113377838371507 13889387889170066757557261)
                ·
                  refine ⟨5208520458438775034083973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13889387889170066757557261 5208520458438775034083973)
                  ·
                    refine ⟨976597585957270318890745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5208520458438775034083973 976597585957270318890745)
                    ·
                      rfl

theorem cell23_5705751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 1, 3, 4].length) (baseStart_5705751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5705751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5705751 prefixEnd_5705751 := by exact prefixLift 5705751
  have htrace : WordTrace (prefixWord ++ tailWord_5705751) baseStart_5705751 baseEnd_5705751 := by
    simpa [prefixWord, tailWord_5705751, baseEnd_5705751] using wordTrace_append hprefix tailTrace_5705751
  have hstable : (prefixWord ++ tailWord_5705751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5705751).length < 2 ^ (prefixWord ++ tailWord_5705751).sum := by decide
  have hdescent : baseEnd_5705751 < baseStart_5705751 := by decide
  rcases family_descends (prefixWord ++ tailWord_5705751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5705785 : List Nat := [1, 2, 1, 5, 4, 1, 1, 3, 1, 4]
def baseStart_5705785 : Nat := 118140960795 + 5705785 * 2 ^ 59
def prefixEnd_5705785 : Nat := 4983230072969 + 3 ^ 40 * 5705785 * 2
def baseEnd_5705785 : Nat := 976603405404687941215693

theorem tailTrace_5705785 : CollatzResearch.WordTrace tailWord_5705785 prefixEnd_5705785 976603405404687941215693 := by
  unfold tailWord_5705785
  simp only [CollatzResearch.WordTrace]
  refine ⟨208107075633922890341550809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138738050422615260227700539 208107075633922890341550809)
  ·
    refine ⟨156080306725442167756163107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208107075633922890341550809 156080306725442167756163107)
    ·
      refine ⟨234120460088163251634244661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156080306725442167756163107 234120460088163251634244661)
      ·
        refine ⟨21948793133265304840710437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 234120460088163251634244661 21948793133265304840710437)
        ·
          refine ⟨4115398712487244657633207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21948793133265304840710437 4115398712487244657633207)
          ·
            refine ⟨6173098068730866986449811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4115398712487244657633207 6173098068730866986449811)
            ·
              refine ⟨9259647103096300479674717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6173098068730866986449811 9259647103096300479674717)
              ·
                refine ⟨3472367663661112679878019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9259647103096300479674717 3472367663661112679878019)
                ·
                  refine ⟨5208551495491669019817029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3472367663661112679878019 5208551495491669019817029)
                  ·
                    refine ⟨976603405404687941215693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5208551495491669019817029 976603405404687941215693)
                    ·
                      rfl

theorem cell23_5705785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 3, 1, 4].length) (baseStart_5705785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5705785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5705785 prefixEnd_5705785 := by exact prefixLift 5705785
  have htrace : WordTrace (prefixWord ++ tailWord_5705785) baseStart_5705785 baseEnd_5705785 := by
    simpa [prefixWord, tailWord_5705785, baseEnd_5705785] using wordTrace_append hprefix tailTrace_5705785
  have hstable : (prefixWord ++ tailWord_5705785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5705785).length < 2 ^ (prefixWord ++ tailWord_5705785).sum := by decide
  have hdescent : baseEnd_5705785 < baseStart_5705785 := by decide
  rcases family_descends (prefixWord ++ tailWord_5705785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5705797 : List Nat := [1, 3, 1, 1, 1, 3, 1, 2, 5, 1, 4]
def baseStart_5705797 : Nat := 118140960795 + 5705797 * 2 ^ 59
def prefixEnd_5705797 : Nat := 4983230072969 + 3 ^ 40 * 5705797 * 2
def baseEnd_5705797 : Nat := 2929816377981917776697023

theorem tailTrace_5705797 : CollatzResearch.WordTrace tailWord_5705797 prefixEnd_5705797 2929816377981917776697023 := by
  unfold tailWord_5705797
  simp only [CollatzResearch.WordTrace]
  refine ⟨208107513309879416390987645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138738342206586277593991763 208107513309879416390987645)
  ·
    refine ⟨78040317491204781146620367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208107513309879416390987645 78040317491204781146620367)
    ·
      refine ⟨117060476236807171719930551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78040317491204781146620367 117060476236807171719930551)
      ·
        refine ⟨175590714355210757579895827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117060476236807171719930551 175590714355210757579895827)
        ·
          refine ⟨263386071532816136369843741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175590714355210757579895827 263386071532816136369843741)
          ·
            refine ⟨98769776824806051138691403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 263386071532816136369843741 98769776824806051138691403)
            ·
              refine ⟨148154665237209076708037105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98769776824806051138691403 148154665237209076708037105)
              ·
                refine ⟨111115998927906807531027829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 148154665237209076708037105 111115998927906807531027829)
                ·
                  refine ⟨10417124899491263206033859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 111115998927906807531027829 10417124899491263206033859)
                  ·
                    refine ⟨15625687349236894809050789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10417124899491263206033859 15625687349236894809050789)
                    ·
                      refine ⟨2929816377981917776697023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15625687349236894809050789 2929816377981917776697023)
                      ·
                        rfl

theorem cell23_5705797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 5, 1, 4].length) (baseStart_5705797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5705797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5705797 prefixEnd_5705797 := by exact prefixLift 5705797
  have htrace : WordTrace (prefixWord ++ tailWord_5705797) baseStart_5705797 baseEnd_5705797 := by
    simpa [prefixWord, tailWord_5705797, baseEnd_5705797] using wordTrace_append hprefix tailTrace_5705797
  have hstable : (prefixWord ++ tailWord_5705797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5705797).length < 2 ^ (prefixWord ++ tailWord_5705797).sum := by decide
  have hdescent : baseEnd_5705797 < baseStart_5705797 := by decide
  rcases family_descends (prefixWord ++ tailWord_5705797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5705817 : List Nat := [1, 2, 1, 2, 2, 1, 3, 4, 1, 1, 5]
def baseStart_5705817 : Nat := 118140960795 + 5705817 * 2 ^ 59
def prefixEnd_5705817 : Nat := 4983230072969 + 3 ^ 40 * 5705817 * 2
def baseEnd_5705817 : Nat := 2929826647595007698446931

theorem tailTrace_5705817 : CollatzResearch.WordTrace tailWord_5705817 prefixEnd_5705817 2929826647595007698446931 := by
  unfold tailWord_5705817
  simp only [CollatzResearch.WordTrace]
  refine ⟨208108242769806959806715705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138738828513204639871143803 208108242769806959806715705)
  ·
    refine ⟨156081182077355219855036779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208108242769806959806715705 156081182077355219855036779)
    ·
      refine ⟨234121773116032829782555169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156081182077355219855036779 234121773116032829782555169)
      ·
        refine ⟨175591329837024622336916377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 234121773116032829782555169 175591329837024622336916377)
        ·
          refine ⟨131693497377768466752687283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175591329837024622336916377 131693497377768466752687283)
          ·
            refine ⟨197540246066652700129030925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131693497377768466752687283 197540246066652700129030925)
            ·
              refine ⟨74077592274994762548386597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 197540246066652700129030925 74077592274994762548386597)
              ·
                refine ⟨13889548551561517977822487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74077592274994762548386597 13889548551561517977822487)
                ·
                  refine ⟨20834322827342276966733731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13889548551561517977822487 20834322827342276966733731)
                  ·
                    refine ⟨31251484241013415450100597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20834322827342276966733731 31251484241013415450100597)
                    ·
                      refine ⟨2929826647595007698446931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31251484241013415450100597 2929826647595007698446931)
                      ·
                        rfl

theorem cell23_5705817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 4, 1, 1, 5].length) (baseStart_5705817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5705817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5705817 prefixEnd_5705817 := by exact prefixLift 5705817
  have htrace : WordTrace (prefixWord ++ tailWord_5705817) baseStart_5705817 baseEnd_5705817 := by
    simpa [prefixWord, tailWord_5705817, baseEnd_5705817] using wordTrace_append hprefix tailTrace_5705817
  have hstable : (prefixWord ++ tailWord_5705817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5705817).length < 2 ^ (prefixWord ++ tailWord_5705817).sum := by decide
  have hdescent : baseEnd_5705817 < baseStart_5705817 := by decide
  rcases family_descends (prefixWord ++ tailWord_5705817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5705827 : List Nat := [1, 1, 1, 5, 1, 1, 4, 1, 1, 1, 6]
def baseStart_5705827 : Nat := 118140960795 + 5705827 * 2 ^ 59
def prefixEnd_5705827 : Nat := 4983230072969 + 3 ^ 40 * 5705827 * 2
def baseEnd_5705827 : Nat := 2929831782401552659321885

theorem tailTrace_5705827 : CollatzResearch.WordTrace tailWord_5705827 prefixEnd_5705827 2929831782401552659321885 := by
  unfold tailWord_5705827
  simp only [CollatzResearch.WordTrace]
  refine ⟨208108607499770731514579735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138739071666513821009719823 208108607499770731514579735)
  ·
    refine ⟨312162911249656097271869603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208108607499770731514579735 312162911249656097271869603)
    ·
      refine ⟨468244366874484145907804405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312162911249656097271869603 468244366874484145907804405)
      ·
        refine ⟨43897909394482888678856663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 468244366874484145907804405 43897909394482888678856663)
        ·
          refine ⟨65846864091724333018284995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43897909394482888678856663 65846864091724333018284995)
          ·
            refine ⟨98770296137586499527427493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65846864091724333018284995 98770296137586499527427493)
            ·
              refine ⟨18519430525797468661392655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 98770296137586499527427493 18519430525797468661392655)
              ·
                refine ⟨27779145788696202992088983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18519430525797468661392655 27779145788696202992088983)
                ·
                  refine ⟨41668718683044304488133475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27779145788696202992088983 41668718683044304488133475)
                  ·
                    refine ⟨62503078024566456732200213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41668718683044304488133475 62503078024566456732200213)
                    ·
                      refine ⟨2929831782401552659321885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62503078024566456732200213 2929831782401552659321885)
                      ·
                        rfl

theorem cell23_5705827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 1, 1, 1, 6].length) (baseStart_5705827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5705827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5705827 prefixEnd_5705827 := by exact prefixLift 5705827
  have htrace : WordTrace (prefixWord ++ tailWord_5705827) baseStart_5705827 baseEnd_5705827 := by
    simpa [prefixWord, tailWord_5705827, baseEnd_5705827] using wordTrace_append hprefix tailTrace_5705827
  have hstable : (prefixWord ++ tailWord_5705827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5705827).length < 2 ^ (prefixWord ++ tailWord_5705827).sum := by decide
  have hdescent : baseEnd_5705827 < baseStart_5705827 := by decide
  rcases family_descends (prefixWord ++ tailWord_5705827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5705831 : List Nat := [1, 1, 5, 1, 1, 2, 2, 1, 5, 2, 2]
def baseStart_5705831 : Nat := 118140960795 + 5705831 * 2 ^ 59
def prefixEnd_5705831 : Nat := 4983230072969 + 3 ^ 40 * 5705831 * 2
def baseEnd_5705831 : Nat := 2929833836324170643671867

theorem tailTrace_5705831 : CollatzResearch.WordTrace tailWord_5705831 prefixEnd_5705831 2929833836324170643671867 := by
  unfold tailWord_5705831
  simp only [CollatzResearch.WordTrace]
  refine ⟨208108753391756240197725347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138739168927837493465150231 208108753391756240197725347)
  ·
    refine ⟨312163130087634360296588021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208108753391756240197725347 312163130087634360296588021)
    ·
      refine ⟨29265293445715721277805127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 312163130087634360296588021 29265293445715721277805127)
      ·
        refine ⟨43897940168573581916707691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29265293445715721277805127 43897940168573581916707691)
        ·
          refine ⟨65846910252860372875061537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43897940168573581916707691 65846910252860372875061537)
          ·
            refine ⟨49385182689645279656296153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65846910252860372875061537 49385182689645279656296153)
            ·
              refine ⟨37038887017233959742222115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49385182689645279656296153 37038887017233959742222115)
              ·
                refine ⟨55558330525850939613333173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37038887017233959742222115 55558330525850939613333173)
                ·
                  refine ⟨5208593486798525588749985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55558330525850939613333173 5208593486798525588749985)
                  ·
                    refine ⟨3906445115098894191562489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5208593486798525588749985 3906445115098894191562489)
                    ·
                      refine ⟨2929833836324170643671867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3906445115098894191562489 2929833836324170643671867)
                      ·
                        rfl

theorem cell23_5705831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 1, 5, 2, 2].length) (baseStart_5705831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5705831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5705831 prefixEnd_5705831 := by exact prefixLift 5705831
  have htrace : WordTrace (prefixWord ++ tailWord_5705831) baseStart_5705831 baseEnd_5705831 := by
    simpa [prefixWord, tailWord_5705831, baseEnd_5705831] using wordTrace_append hprefix tailTrace_5705831
  have hstable : (prefixWord ++ tailWord_5705831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5705831).length < 2 ^ (prefixWord ++ tailWord_5705831).sum := by decide
  have hdescent : baseEnd_5705831 < baseStart_5705831 := by decide
  rcases family_descends (prefixWord ++ tailWord_5705831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5705837 : List Nat := [1, 5, 1, 1, 2, 1, 1, 11]
def baseStart_5705837 : Nat := 118140960795 + 5705837 * 2 ^ 59
def prefixEnd_5705837 : Nat := 4983230072969 + 3 ^ 40 * 5705837 * 2
def baseEnd_5705837 : Nat := 108512478415114726673957

theorem tailTrace_5705837 : CollatzResearch.WordTrace tailWord_5705837 prefixEnd_5705837 108512478415114726673957 := by
  unfold tailWord_5705837
  simp only [CollatzResearch.WordTrace]
  refine ⟨208108972229734503222443765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138739314819823002148295843 208108972229734503222443765)
  ·
    refine ⟨19510216146537609677104103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 208108972229734503222443765 19510216146537609677104103)
    ·
      refine ⟨29265324219806414515656155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19510216146537609677104103 29265324219806414515656155)
      ·
        refine ⟨43897986329709621773484233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29265324219806414515656155 43897986329709621773484233)
        ·
          refine ⟨32923489747282216330113175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43897986329709621773484233 32923489747282216330113175)
          ·
            refine ⟨49385234620923324495169763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32923489747282216330113175 49385234620923324495169763)
            ·
              refine ⟨74077851931384986742754645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49385234620923324495169763 74077851931384986742754645)
              ·
                refine ⟨108512478415114726673957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 74077851931384986742754645 108512478415114726673957)
                ·
                  rfl

theorem cell23_5705837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 11].length) (baseStart_5705837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5705837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5705837 prefixEnd_5705837 := by exact prefixLift 5705837
  have htrace : WordTrace (prefixWord ++ tailWord_5705837) baseStart_5705837 baseEnd_5705837 := by
    simpa [prefixWord, tailWord_5705837, baseEnd_5705837] using wordTrace_append hprefix tailTrace_5705837
  have hstable : (prefixWord ++ tailWord_5705837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5705837).length < 2 ^ (prefixWord ++ tailWord_5705837).sum := by decide
  have hdescent : baseEnd_5705837 < baseStart_5705837 := by decide
  rcases family_descends (prefixWord ++ tailWord_5705837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5705848 : List Nat := [2, 1, 2, 1, 1, 1, 3, 7, 1, 2, 2]
def baseStart_5705848 : Nat := 118140960795 + 5705848 * 2 ^ 59
def prefixEnd_5705848 : Nat := 4983230072969 + 3 ^ 40 * 5705848 * 2
def baseEnd_5705848 : Nat := 2929842565495297077159289

theorem tailTrace_5705848 : CollatzResearch.WordTrace tailWord_5705848 prefixEnd_5705848 2929842565495297077159289 := by
  unfold tailWord_5705848
  simp only [CollatzResearch.WordTrace]
  refine ⟨104054686716347326050547099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138739582288463101400729465 104054686716347326050547099)
  ·
    refine ⟨156082030074520989075820649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104054686716347326050547099 156082030074520989075820649)
    ·
      refine ⟨117061522555890741806865487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156082030074520989075820649 117061522555890741806865487)
      ·
        refine ⟨175592283833836112710298231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117061522555890741806865487 175592283833836112710298231)
        ·
          refine ⟨263388425750754169065447347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175592283833836112710298231 263388425750754169065447347)
          ·
            refine ⟨395082638626131253598171021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 263388425750754169065447347 395082638626131253598171021)
            ·
              refine ⟨148155989484799220099314133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 395082638626131253598171021 148155989484799220099314133)
              ·
                refine ⟨3472406003549981721077675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 148155989484799220099314133 3472406003549981721077675)
                ·
                  refine ⟨5208609005324972581616513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3472406003549981721077675 5208609005324972581616513)
                  ·
                    refine ⟨3906456753993729436212385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5208609005324972581616513 3906456753993729436212385)
                    ·
                      refine ⟨2929842565495297077159289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3906456753993729436212385 2929842565495297077159289)
                      ·
                        rfl

theorem cell23_5705848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 7, 1, 2, 2].length) (baseStart_5705848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5705848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5705848 prefixEnd_5705848 := by exact prefixLift 5705848
  have htrace : WordTrace (prefixWord ++ tailWord_5705848) baseStart_5705848 baseEnd_5705848 := by
    simpa [prefixWord, tailWord_5705848, baseEnd_5705848] using wordTrace_append hprefix tailTrace_5705848
  have hstable : (prefixWord ++ tailWord_5705848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5705848).length < 2 ^ (prefixWord ++ tailWord_5705848).sum := by decide
  have hdescent : baseEnd_5705848 < baseStart_5705848 := by decide
  rcases family_descends (prefixWord ++ tailWord_5705848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5705854 : List Nat := [4, 2, 4, 13]
def baseStart_5705854 : Nat := 118140960795 + 5705854 * 2 ^ 59
def prefixEnd_5705854 : Nat := 4983230072969 + 3 ^ 40 * 5705854 * 2
def baseEnd_5705854 : Nat := 1339664218737642457103

theorem tailTrace_5705854 : CollatzResearch.WordTrace tailWord_5705854 prefixEnd_5705854 1339664218737642457103 := by
  unfold tailWord_5705854
  simp only [CollatzResearch.WordTrace]
  refine ⟨26013699033834114390726577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138739728180448610083875077 26013699033834114390726577)
  ·
    refine ⟨19510274275375585793044933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26013699033834114390726577 19510274275375585793044933)
    ·
      refine ⟨3658176426632922336195925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19510274275375585793044933 3658176426632922336195925)
      ·
        refine ⟨1339664218737642457103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 3658176426632922336195925 1339664218737642457103)
        ·
          rfl

theorem cell23_5705854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 13].length) (baseStart_5705854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5705854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5705854 prefixEnd_5705854 := by exact prefixLift 5705854
  have htrace : WordTrace (prefixWord ++ tailWord_5705854) baseStart_5705854 baseEnd_5705854 := by
    simpa [prefixWord, tailWord_5705854, baseEnd_5705854] using wordTrace_append hprefix tailTrace_5705854
  have hstable : (prefixWord ++ tailWord_5705854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5705854).length < 2 ^ (prefixWord ++ tailWord_5705854).sum := by decide
  have hdescent : baseEnd_5705854 < baseStart_5705854 := by decide
  rcases family_descends (prefixWord ++ tailWord_5705854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5705907 : List Nat := [1, 1, 1, 2, 3, 2, 1, 3, 1, 3, 5]
def baseStart_5705907 : Nat := 118140960795 + 5705907 * 2 ^ 59
def prefixEnd_5705907 : Nat := 4983230072969 + 3 ^ 40 * 5705907 * 2
def baseEnd_5705907 : Nat := 2929872860853912346321517

theorem tailTrace_5705907 : CollatzResearch.WordTrace tailWord_5705907 prefixEnd_5705907 2929872860853912346321517 := by
  unfold tailWord_5705907
  simp only [CollatzResearch.WordTrace]
  refine ⟨208111525339480905177491975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138741016892987270118327983 208111525339480905177491975)
  ·
    refine ⟨312167288009221357766237963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208111525339480905177491975 312167288009221357766237963)
    ·
      refine ⟨468250932013832036649356945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312167288009221357766237963 468250932013832036649356945)
      ·
        refine ⟨351188199010374027487017709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 468250932013832036649356945 351188199010374027487017709)
        ·
          refine ⟨131695574628890260307631641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 351188199010374027487017709 131695574628890260307631641)
          ·
            refine ⟨98771680971667695230723731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131695574628890260307631641 98771680971667695230723731)
            ·
              refine ⟨148157521457501542846085597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98771680971667695230723731 148157521457501542846085597)
              ·
                refine ⟨55559070546563078567282099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 148157521457501542846085597 55559070546563078567282099)
                ·
                  refine ⟨83338605819844617850923149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55559070546563078567282099 83338605819844617850923149)
                  ·
                    refine ⟨31251977182441731694096181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 83338605819844617850923149 31251977182441731694096181)
                    ·
                      refine ⟨2929872860853912346321517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31251977182441731694096181 2929872860853912346321517)
                      ·
                        rfl

theorem cell23_5705907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 3, 1, 3, 5].length) (baseStart_5705907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5705907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5705907 prefixEnd_5705907 := by exact prefixLift 5705907
  have htrace : WordTrace (prefixWord ++ tailWord_5705907) baseStart_5705907 baseEnd_5705907 := by
    simpa [prefixWord, tailWord_5705907, baseEnd_5705907] using wordTrace_append hprefix tailTrace_5705907
  have hstable : (prefixWord ++ tailWord_5705907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5705907).length < 2 ^ (prefixWord ++ tailWord_5705907).sum := by decide
  have hdescent : baseEnd_5705907 < baseStart_5705907 := by decide
  rcases family_descends (prefixWord ++ tailWord_5705907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5705932 : List Nat := [2, 2, 1, 6, 1, 1, 3, 1, 2, 1, 3]
def baseStart_5705932 : Nat := 118140960795 + 5705932 * 2 ^ 59
def prefixEnd_5705932 : Nat := 4983230072969 + 3 ^ 40 * 5705932 * 2
def baseEnd_5705932 : Nat := 2929885697870274748508903

theorem tailTrace_5705932 : CollatzResearch.WordTrace tailWord_5705932 prefixEnd_5705932 2929885697870274748508903 := by
  unfold tailWord_5705932
  simp only [CollatzResearch.WordTrace]
  refine ⟨104056218582195167223576025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138741624776260222964768033 104056218582195167223576025)
  ·
    refine ⟨78042163936646375417682019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104056218582195167223576025 78042163936646375417682019)
    ·
      refine ⟨117063245904969563126523029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78042163936646375417682019 117063245904969563126523029)
      ·
        refine ⟨5487339651795448271555767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 117063245904969563126523029 5487339651795448271555767)
        ·
          refine ⟨8231009477693172407333651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5487339651795448271555767 8231009477693172407333651)
          ·
            refine ⟨12346514216539758611000477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8231009477693172407333651 12346514216539758611000477)
            ·
              refine ⟨4629942831202409479125179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12346514216539758611000477 4629942831202409479125179)
              ·
                refine ⟨6944914246803614218687769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4629942831202409479125179 6944914246803614218687769)
                ·
                  refine ⟨5208685685102710664015827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6944914246803614218687769 5208685685102710664015827)
                  ·
                    refine ⟨7813028527654065996023741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5208685685102710664015827 7813028527654065996023741)
                    ·
                      refine ⟨2929885697870274748508903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7813028527654065996023741 2929885697870274748508903)
                      ·
                        rfl

theorem cell23_5705932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_5705932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5705932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5705932 prefixEnd_5705932 := by exact prefixLift 5705932
  have htrace : WordTrace (prefixWord ++ tailWord_5705932) baseStart_5705932 baseEnd_5705932 := by
    simpa [prefixWord, tailWord_5705932, baseEnd_5705932] using wordTrace_append hprefix tailTrace_5705932
  have hstable : (prefixWord ++ tailWord_5705932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5705932).length < 2 ^ (prefixWord ++ tailWord_5705932).sum := by decide
  have hdescent : baseEnd_5705932 < baseStart_5705932 := by decide
  rcases family_descends (prefixWord ++ tailWord_5705932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5705938 : List Nat := [3, 2, 2, 2, 1, 2, 3, 1, 1, 4, 2]
def baseStart_5705938 : Nat := 118140960795 + 5705938 * 2 ^ 59
def prefixEnd_5705938 : Nat := 4983230072969 + 3 ^ 40 * 5705938 * 2
def baseEnd_5705938 : Nat := 2929888778754201725033875

theorem tailTrace_5705938 : CollatzResearch.WordTrace tailWord_5705938 prefixEnd_5705938 2929888778754201725033875 := by
  unfold tailWord_5705938
  simp only [CollatzResearch.WordTrace]
  refine ⟨52028164000592149367967617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138741770668245731647913645 52028164000592149367967617)
  ·
    refine ⟨39021123000444112025975713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52028164000592149367967617 39021123000444112025975713)
    ·
      refine ⟨29265842250333084019481785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39021123000444112025975713 29265842250333084019481785)
      ·
        refine ⟨21949381687749813014611339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29265842250333084019481785 21949381687749813014611339)
        ·
          refine ⟨32924072531624719521917009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21949381687749813014611339 32924072531624719521917009)
          ·
            refine ⟨24693054398718539641437757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32924072531624719521917009 24693054398718539641437757)
            ·
              refine ⟨9259895399519452365539159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24693054398718539641437757 9259895399519452365539159)
              ·
                refine ⟨13889843099279178548308739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9259895399519452365539159 13889843099279178548308739)
                ·
                  refine ⟨20834764648918767822463109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13889843099279178548308739 20834764648918767822463109)
                  ·
                    refine ⟨3906518371672268966711833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20834764648918767822463109 3906518371672268966711833)
                    ·
                      refine ⟨2929888778754201725033875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3906518371672268966711833 2929888778754201725033875)
                      ·
                        rfl

theorem cell23_5705938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 1, 1, 4, 2].length) (baseStart_5705938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5705938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5705938 prefixEnd_5705938 := by exact prefixLift 5705938
  have htrace : WordTrace (prefixWord ++ tailWord_5705938) baseStart_5705938 baseEnd_5705938 := by
    simpa [prefixWord, tailWord_5705938, baseEnd_5705938] using wordTrace_append hprefix tailTrace_5705938
  have hstable : (prefixWord ++ tailWord_5705938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5705938).length < 2 ^ (prefixWord ++ tailWord_5705938).sum := by decide
  have hdescent : baseEnd_5705938 < baseStart_5705938 := by decide
  rcases family_descends (prefixWord ++ tailWord_5705938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5705942 : List Nat := [5, 2, 1, 2, 1, 2, 2, 2, 1, 3, 2]
def baseStart_5705942 : Nat := 118140960795 + 5705942 * 2 ^ 59
def prefixEnd_5705942 : Nat := 4983230072969 + 3 ^ 40 * 5705942 * 2
def baseEnd_5705942 : Nat := 2929890832676819709383857

theorem tailTrace_5705942 : CollatzResearch.WordTrace tailWord_5705942 prefixEnd_5705942 2929890832676819709383857 := by
  unfold tailWord_5705942
  simp only [CollatzResearch.WordTrace]
  refine ⟨13007050118397131634688505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 138741867929569404103344053 13007050118397131634688505)
  ·
    refine ⟨9755287588797848726016379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13007050118397131634688505 9755287588797848726016379)
    ·
      refine ⟨14632931383196773089024569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9755287588797848726016379 14632931383196773089024569)
      ·
        refine ⟨10974698537397579816768427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14632931383196773089024569 10974698537397579816768427)
        ·
          refine ⟨16462047806096369725152641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10974698537397579816768427 16462047806096369725152641)
          ·
            refine ⟨12346535854572277293864481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16462047806096369725152641 12346535854572277293864481)
            ·
              refine ⟨9259901890929207970398361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12346535854572277293864481 9259901890929207970398361)
              ·
                refine ⟨6944926418196905977798771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9259901890929207970398361 6944926418196905977798771)
                ·
                  refine ⟨10417389627295358966698157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6944926418196905977798771 10417389627295358966698157)
                  ·
                    refine ⟨3906521110235759612511809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10417389627295358966698157 3906521110235759612511809)
                    ·
                      refine ⟨2929890832676819709383857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3906521110235759612511809 2929890832676819709383857)
                      ·
                        rfl

theorem cell23_5705942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 2, 1, 3, 2].length) (baseStart_5705942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5705942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5705942 prefixEnd_5705942 := by exact prefixLift 5705942
  have htrace : WordTrace (prefixWord ++ tailWord_5705942) baseStart_5705942 baseEnd_5705942 := by
    simpa [prefixWord, tailWord_5705942, baseEnd_5705942] using wordTrace_append hprefix tailTrace_5705942
  have hstable : (prefixWord ++ tailWord_5705942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5705942).length < 2 ^ (prefixWord ++ tailWord_5705942).sum := by decide
  have hdescent : baseEnd_5705942 < baseStart_5705942 := by decide
  rcases family_descends (prefixWord ++ tailWord_5705942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5705944 : List Nat := [2, 1, 2, 2, 4, 1, 2, 2, 7]
def baseStart_5705944 : Nat := 118140960795 + 5705944 * 2 ^ 59
def prefixEnd_5705944 : Nat := 4983230072969 + 3 ^ 40 * 5705944 * 2
def baseEnd_5705944 : Nat := 325543539959792077950983

theorem tailTrace_5705944 : CollatzResearch.WordTrace tailWord_5705944 prefixEnd_5705944 325543539959792077950983 := by
  unfold tailWord_5705944
  simp only [CollatzResearch.WordTrace]
  refine ⟨104056437420173430248294443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138741916560231240331059257 104056437420173430248294443)
  ·
    refine ⟨156084656130260145372441665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104056437420173430248294443 156084656130260145372441665)
    ·
      refine ⟨117063492097695109029331249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156084656130260145372441665 117063492097695109029331249)
      ·
        refine ⟨87797619073271331771998437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117063492097695109029331249 87797619073271331771998437)
        ·
          refine ⟨16462053576238374707249707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87797619073271331771998437 16462053576238374707249707)
          ·
            refine ⟨24693080364357562060874561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16462053576238374707249707 24693080364357562060874561)
            ·
              refine ⟨18519810273268171545655921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24693080364357562060874561 18519810273268171545655921)
              ·
                refine ⟨13889857704951128659241941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18519810273268171545655921 13889857704951128659241941)
                ·
                  refine ⟨325543539959792077950983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13889857704951128659241941 325543539959792077950983)
                  ·
                    rfl

theorem cell23_5705944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 2, 7].length) (baseStart_5705944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5705944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5705944 prefixEnd_5705944 := by exact prefixLift 5705944
  have htrace : WordTrace (prefixWord ++ tailWord_5705944) baseStart_5705944 baseEnd_5705944 := by
    simpa [prefixWord, tailWord_5705944, baseEnd_5705944] using wordTrace_append hprefix tailTrace_5705944
  have hstable : (prefixWord ++ tailWord_5705944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5705944).length < 2 ^ (prefixWord ++ tailWord_5705944).sum := by decide
  have hdescent : baseEnd_5705944 < baseStart_5705944 := by decide
  rcases family_descends (prefixWord ++ tailWord_5705944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5705978 : List Nat := [3, 1, 1, 1, 1, 6, 3, 2, 5]
def baseStart_5705978 : Nat := 118140960795 + 5705978 * 2 ^ 59
def prefixEnd_5705978 : Nat := 4983230072969 + 3 ^ 40 * 5705978 * 2
def baseEnd_5705978 : Nat := 325545479775597952059299

theorem tailTrace_5705978 : CollatzResearch.WordTrace tailWord_5705978 prefixEnd_5705978 325545479775597952059299 := by
  unfold tailWord_5705978
  simp only [CollatzResearch.WordTrace]
  refine ⟨52028528730555921075831647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138742743281482456202217725 52028528730555921075831647)
  ·
    refine ⟨78042793095833881613747471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52028528730555921075831647 78042793095833881613747471)
    ·
      refine ⟨117064189643750822420621207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78042793095833881613747471 117064189643750822420621207)
      ·
        refine ⟨175596284465626233630931811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117064189643750822420621207 175596284465626233630931811)
        ·
          refine ⟨263394426698439350446397717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175596284465626233630931811 263394426698439350446397717)
          ·
            refine ⟨12346613751489344552174893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 263394426698439350446397717 12346613751489344552174893)
            ·
              refine ⟨4629980156808504207065585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12346613751489344552174893 4629980156808504207065585)
              ·
                refine ⟨3472485117606378155299189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4629980156808504207065585 3472485117606378155299189)
                ·
                  refine ⟨325545479775597952059299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3472485117606378155299189 325545479775597952059299)
                  ·
                    rfl

theorem cell23_5705978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 3, 2, 5].length) (baseStart_5705978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5705978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5705978 prefixEnd_5705978 := by exact prefixLift 5705978
  have htrace : WordTrace (prefixWord ++ tailWord_5705978) baseStart_5705978 baseEnd_5705978 := by
    simpa [prefixWord, tailWord_5705978, baseEnd_5705978] using wordTrace_append hprefix tailTrace_5705978
  have hstable : (prefixWord ++ tailWord_5705978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5705978).length < 2 ^ (prefixWord ++ tailWord_5705978).sum := by decide
  have hdescent : baseEnd_5705978 < baseStart_5705978 := by decide
  rcases family_descends (prefixWord ++ tailWord_5705978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5705994 : List Nat := [3, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4]
def baseStart_5705994 : Nat := 118140960795 + 5705994 * 2 ^ 59
def prefixEnd_5705994 : Nat := 4983230072969 + 3 ^ 40 * 5705994 * 2
def baseEnd_5705994 : Nat := 2929917533670853505933617

theorem tailTrace_5705994 : CollatzResearch.WordTrace tailWord_5705994 prefixEnd_5705994 2929917533670853505933617 := by
  unfold tailWord_5705994
  simp only [CollatzResearch.WordTrace]
  refine ⟨52028674622541429758977259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138743132326777146023939357 52028674622541429758977259)
  ·
    refine ⟨78043011933812144638465889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52028674622541429758977259 78043011933812144638465889)
    ·
      refine ⟨58532258950359108478849417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78043011933812144638465889 58532258950359108478849417)
      ·
        refine ⟨43899194212769331359137063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58532258950359108478849417 43899194212769331359137063)
        ·
          refine ⟨65848791319153997038705595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43899194212769331359137063 65848791319153997038705595)
          ·
            refine ⟨98773186978730995558058393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65848791319153997038705595 98773186978730995558058393)
            ·
              refine ⟨74079890234048246668543795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98773186978730995558058393 74079890234048246668543795)
              ·
                refine ⟨111119835351072370002815693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74079890234048246668543795 111119835351072370002815693)
                ·
                  refine ⟨41669938256652138751055885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 111119835351072370002815693 41669938256652138751055885)
                  ·
                    refine ⟨15626226846244552031645957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41669938256652138751055885 15626226846244552031645957)
                    ·
                      refine ⟨2929917533670853505933617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15626226846244552031645957 2929917533670853505933617)
                      ·
                        rfl

theorem cell23_5705994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4].length) (baseStart_5705994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5705994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5705994 prefixEnd_5705994 := by exact prefixLift 5705994
  have htrace : WordTrace (prefixWord ++ tailWord_5705994) baseStart_5705994 baseEnd_5705994 := by
    simpa [prefixWord, tailWord_5705994, baseEnd_5705994] using wordTrace_append hprefix tailTrace_5705994
  have hstable : (prefixWord ++ tailWord_5705994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5705994).length < 2 ^ (prefixWord ++ tailWord_5705994).sum := by decide
  have hdescent : baseEnd_5705994 < baseStart_5705994 := by decide
  rcases family_descends (prefixWord ++ tailWord_5705994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5706029 : List Nat := [1, 5, 3, 1, 3, 1, 2, 2, 5]
def baseStart_5706029 : Nat := 118140960795 + 5706029 * 2 ^ 59
def prefixEnd_5706029 : Nat := 4983230072969 + 3 ^ 40 * 5706029 * 2
def baseEnd_5706029 : Nat := 325548389499306763221773

theorem tailTrace_5706029 : CollatzResearch.WordTrace tailWord_5706029 prefixEnd_5706029 325548389499306763221773 := by
  unfold tailWord_5706029
  simp only [CollatzResearch.WordTrace]
  refine ⟨208115975045038920013433141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138743983363359280008955427 208115975045038920013433141)
  ·
    refine ⟨19510872660472398751259357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 208115975045038920013433141 19510872660472398751259357)
    ·
      refine ⟨7316577247677149531722259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19510872660472398751259357 7316577247677149531722259)
      ·
        refine ⟨10974865871515724297583389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7316577247677149531722259 10974865871515724297583389)
        ·
          refine ⟨4115574701818396611593771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10974865871515724297583389 4115574701818396611593771)
          ·
            refine ⟨6173362052727594917390657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4115574701818396611593771 6173362052727594917390657)
            ·
              refine ⟨4630021539545696188042993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6173362052727594917390657 4630021539545696188042993)
              ·
                refine ⟨3472516154659272141032245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4630021539545696188042993 3472516154659272141032245)
                ·
                  refine ⟨325548389499306763221773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3472516154659272141032245 325548389499306763221773)
                  ·
                    rfl

theorem cell23_5706029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 2, 2, 5].length) (baseStart_5706029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5706029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5706029 prefixEnd_5706029 := by exact prefixLift 5706029
  have htrace : WordTrace (prefixWord ++ tailWord_5706029) baseStart_5706029 baseEnd_5706029 := by
    simpa [prefixWord, tailWord_5706029, baseEnd_5706029] using wordTrace_append hprefix tailTrace_5706029
  have hstable : (prefixWord ++ tailWord_5706029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5706029).length < 2 ^ (prefixWord ++ tailWord_5706029).sum := by decide
  have hdescent : baseEnd_5706029 < baseStart_5706029 := by decide
  rcases family_descends (prefixWord ++ tailWord_5706029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5706031 : List Nat := [1, 1, 2, 1, 2, 1, 6, 2, 2, 2, 3]
def baseStart_5706031 : Nat := 118140960795 + 5706031 * 2 ^ 59
def prefixEnd_5706031 : Nat := 4983230072969 + 3 ^ 40 * 5706031 * 2
def baseEnd_5706031 : Nat := 2929936532455069861170947

theorem tailTrace_5706031 : CollatzResearch.WordTrace tailWord_5706031 prefixEnd_5706031 2929936532455069861170947 := by
  unfold tailWord_5706031
  simp only [CollatzResearch.WordTrace]
  refine ⟨208116047991031674355005947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138744031994021116236670631 208116047991031674355005947)
  ·
    refine ⟨312174071986547511532508921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208116047991031674355005947 312174071986547511532508921)
    ·
      refine ⟨234130553989910633649381691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 312174071986547511532508921 234130553989910633649381691)
      ·
        refine ⟨351195830984865950474072537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234130553989910633649381691 351195830984865950474072537)
        ·
          refine ⟨263396873238649462855554403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 351195830984865950474072537 263396873238649462855554403)
          ·
            refine ⟨395095309857974194283331605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 263396873238649462855554403 395095309857974194283331605)
            ·
              refine ⟨18520092649592540357031169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 395095309857974194283331605 18520092649592540357031169)
              ·
                refine ⟨13890069487194405267773377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18520092649592540357031169 13890069487194405267773377)
                ·
                  refine ⟨10417552115395803950830033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13890069487194405267773377 10417552115395803950830033)
                  ·
                    refine ⟨7813164086546852963122525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10417552115395803950830033 7813164086546852963122525)
                    ·
                      refine ⟨2929936532455069861170947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7813164086546852963122525 2929936532455069861170947)
                      ·
                        rfl

theorem cell23_5706031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 2, 2, 2, 3].length) (baseStart_5706031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5706031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5706031 prefixEnd_5706031 := by exact prefixLift 5706031
  have htrace : WordTrace (prefixWord ++ tailWord_5706031) baseStart_5706031 baseEnd_5706031 := by
    simpa [prefixWord, tailWord_5706031, baseEnd_5706031] using wordTrace_append hprefix tailTrace_5706031
  have hstable : (prefixWord ++ tailWord_5706031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5706031).length < 2 ^ (prefixWord ++ tailWord_5706031).sum := by decide
  have hdescent : baseEnd_5706031 < baseStart_5706031 := by decide
  rcases family_descends (prefixWord ++ tailWord_5706031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5706074 : List Nat := [3, 1, 1, 2, 1, 2, 1, 1, 2, 4, 5]
def baseStart_5706074 : Nat := 118140960795 + 5706074 * 2 ^ 59
def prefixEnd_5706074 : Nat := 4983230072969 + 3 ^ 40 * 5706074 * 2
def baseEnd_5706074 : Nat := 2929958612123213192933249

theorem tailTrace_5706074 : CollatzResearch.WordTrace tailWord_5706074 prefixEnd_5706074 2929958612123213192933249 := by
  unfold tailWord_5706074
  simp only [CollatzResearch.WordTrace]
  refine ⟨52029404082468973174705319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138745077553250595132547517 52029404082468973174705319)
  ·
    refine ⟨78044106123703459762057979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52029404082468973174705319 78044106123703459762057979)
    ·
      refine ⟨117066159185555189643086969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78044106123703459762057979 117066159185555189643086969)
      ·
        refine ⟨87799619389166392232315227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117066159185555189643086969 87799619389166392232315227)
        ·
          refine ⟨131699429083749588348472841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87799619389166392232315227 131699429083749588348472841)
          ·
            refine ⟨98774571812812191261354631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131699429083749588348472841 98774571812812191261354631)
            ·
              refine ⟨148161857719218286892031947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98774571812812191261354631 148161857719218286892031947)
              ·
                refine ⟨222242786578827430338047921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 148161857719218286892031947 222242786578827430338047921)
                ·
                  refine ⟨166682089934120572753535941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 222242786578827430338047921 166682089934120572753535941)
                  ·
                    refine ⟨31252891862647607391287989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 166682089934120572753535941 31252891862647607391287989)
                    ·
                      refine ⟨2929958612123213192933249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31252891862647607391287989 2929958612123213192933249)
                      ·
                        rfl

theorem cell23_5706074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 2, 4, 5].length) (baseStart_5706074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5706074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5706074 prefixEnd_5706074 := by exact prefixLift 5706074
  have htrace : WordTrace (prefixWord ++ tailWord_5706074) baseStart_5706074 baseEnd_5706074 := by
    simpa [prefixWord, tailWord_5706074, baseEnd_5706074] using wordTrace_append hprefix tailTrace_5706074
  have hstable : (prefixWord ++ tailWord_5706074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5706074).length < 2 ^ (prefixWord ++ tailWord_5706074).sum := by decide
  have hdescent : baseEnd_5706074 < baseStart_5706074 := by decide
  rcases family_descends (prefixWord ++ tailWord_5706074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5706102 : List Nat := [5, 1, 1, 4, 1, 1, 3, 1, 6]
def baseStart_5706102 : Nat := 118140960795 + 5706102 * 2 ^ 59
def prefixEnd_5706102 : Nat := 4983230072969 + 3 ^ 40 * 5706102 * 2
def baseEnd_5706102 : Nat := 325552554397948787042569

theorem tailTrace_5706102 : CollatzResearch.WordTrace tailWord_5706102 prefixEnd_5706102 325552554397948787042569 := by
  unfold tailWord_5706102
  simp only [CollatzResearch.WordTrace]
  refine ⟨13007414848360903342552535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 138745758382516302320560373 13007414848360903342552535)
  ·
    refine ⟨19511122272541355013828803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13007414848360903342552535 19511122272541355013828803)
    ·
      refine ⟨29266683408812032520743205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19511122272541355013828803 29266683408812032520743205)
      ·
        refine ⟨5487503139152256097639351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29266683408812032520743205 5487503139152256097639351)
        ·
          refine ⟨8231254708728384146459027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5487503139152256097639351 8231254708728384146459027)
          ·
            refine ⟨12346882063092576219688541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8231254708728384146459027 12346882063092576219688541)
            ·
              refine ⟨4630080773659716082383203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12346882063092576219688541 4630080773659716082383203)
              ·
                refine ⟨6945121160489574123574805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4630080773659716082383203 6945121160489574123574805)
                ·
                  refine ⟨325552554397948787042569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6945121160489574123574805 325552554397948787042569)
                  ·
                    rfl

theorem cell23_5706102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 3, 1, 6].length) (baseStart_5706102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5706102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5706102 prefixEnd_5706102 := by exact prefixLift 5706102
  have htrace : WordTrace (prefixWord ++ tailWord_5706102) baseStart_5706102 baseEnd_5706102 := by
    simpa [prefixWord, tailWord_5706102, baseEnd_5706102] using wordTrace_append hprefix tailTrace_5706102
  have hstable : (prefixWord ++ tailWord_5706102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5706102).length < 2 ^ (prefixWord ++ tailWord_5706102).sum := by decide
  have hdescent : baseEnd_5706102 < baseStart_5706102 := by decide
  rcases family_descends (prefixWord ++ tailWord_5706102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5706138 : List Nat := [3, 1, 1, 4, 1, 3, 2, 1, 1, 1, 5]
def baseStart_5706138 : Nat := 118140960795 + 5706138 * 2 ^ 59
def prefixEnd_5706138 : Nat := 4983230072969 + 3 ^ 40 * 5706138 * 2
def baseEnd_5706138 : Nat := 2929991474885100942532955

theorem tailTrace_5706138 : CollatzResearch.WordTrace tailWord_5706138 prefixEnd_5706138 2929991474885100942532955 := by
  unfold tailWord_5706138
  simp only [CollatzResearch.WordTrace]
  refine ⟨52029987650411007907287767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138746633734429354419434045 52029987650411007907287767)
  ·
    refine ⟨78044981475616511860931651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52029987650411007907287767 78044981475616511860931651)
    ·
      refine ⟨117067472213424767791397477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78044981475616511860931651 117067472213424767791397477)
      ·
        refine ⟨21950151040017143960887027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 117067472213424767791397477 21950151040017143960887027)
        ·
          refine ⟨32925226560025715941330541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21950151040017143960887027 32925226560025715941330541)
          ·
            refine ⟨12346959960009643477998953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32925226560025715941330541 12346959960009643477998953)
            ·
              refine ⟨9260219970007232608499215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12346959960009643477998953 9260219970007232608499215)
              ·
                refine ⟨13890329955010848912748823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9260219970007232608499215 13890329955010848912748823)
                ·
                  refine ⟨20835494932516273369123235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13890329955010848912748823 20835494932516273369123235)
                  ·
                    refine ⟨31253242398774410053684853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20835494932516273369123235 31253242398774410053684853)
                    ·
                      refine ⟨2929991474885100942532955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31253242398774410053684853 2929991474885100942532955)
                      ·
                        rfl

theorem cell23_5706138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 1, 1, 1, 5].length) (baseStart_5706138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5706138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5706138 prefixEnd_5706138 := by exact prefixLift 5706138
  have htrace : WordTrace (prefixWord ++ tailWord_5706138) baseStart_5706138 baseEnd_5706138 := by
    simpa [prefixWord, tailWord_5706138, baseEnd_5706138] using wordTrace_append hprefix tailTrace_5706138
  have hstable : (prefixWord ++ tailWord_5706138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5706138).length < 2 ^ (prefixWord ++ tailWord_5706138).sum := by decide
  have hdescent : baseEnd_5706138 < baseStart_5706138 := by decide
  rcases family_descends (prefixWord ++ tailWord_5706138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5706172 : List Nat := [2, 2, 2, 4, 1, 3, 1, 2, 1, 2, 3]
def baseStart_5706172 : Nat := 118140960795 + 5706172 * 2 ^ 59
def prefixEnd_5706172 : Nat := 4983230072969 + 3 ^ 40 * 5706172 * 2
def baseEnd_5706172 : Nat := 2930008933227353809507799

theorem tailTrace_5706172 : CollatzResearch.WordTrace tailWord_5706172 prefixEnd_5706172 2930008933227353809507799 := by
  unfold tailWord_5706172
  simp only [CollatzResearch.WordTrace]
  refine ⟨104060595341760427717944385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138747460455680570290592513 104060595341760427717944385)
  ·
    refine ⟨78045446506320320788458289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104060595341760427717944385 78045446506320320788458289)
    ·
      refine ⟨58534084879740240591343717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78045446506320320788458289 58534084879740240591343717)
      ·
        refine ⟨10975140914951295110876947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58534084879740240591343717 10975140914951295110876947)
        ·
          refine ⟨16462711372426942666315421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10975140914951295110876947 16462711372426942666315421)
          ·
            refine ⟨6173516764660103499868283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16462711372426942666315421 6173516764660103499868283)
            ·
              refine ⟨9260275146990155249802425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6173516764660103499868283 9260275146990155249802425)
              ·
                refine ⟨6945206360242616437351819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9260275146990155249802425 6945206360242616437351819)
                ·
                  refine ⟨10417809540363924656027729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6945206360242616437351819 10417809540363924656027729)
                  ·
                    refine ⟨7813357155272943492020797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10417809540363924656027729 7813357155272943492020797)
                    ·
                      refine ⟨2930008933227353809507799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7813357155272943492020797 2930008933227353809507799)
                      ·
                        rfl

theorem cell23_5706172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_5706172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5706172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5706172 prefixEnd_5706172 := by exact prefixLift 5706172
  have htrace : WordTrace (prefixWord ++ tailWord_5706172) baseStart_5706172 baseEnd_5706172 := by
    simpa [prefixWord, tailWord_5706172, baseEnd_5706172] using wordTrace_append hprefix tailTrace_5706172
  have hstable : (prefixWord ++ tailWord_5706172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5706172).length < 2 ^ (prefixWord ++ tailWord_5706172).sum := by decide
  have hdescent : baseEnd_5706172 < baseStart_5706172 := by decide
  rcases family_descends (prefixWord ++ tailWord_5706172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5706201 : List Nat := [1, 2, 1, 2, 4, 1, 2, 2, 2, 6]
def baseStart_5706201 : Nat := 118140960795 + 5706201 * 2 ^ 59
def prefixEnd_5706201 : Nat := 4983230072969 + 3 ^ 40 * 5706201 * 2
def baseEnd_5706201 : Nat := 976674608055444732015055

theorem tailTrace_5706201 : CollatzResearch.WordTrace tailWord_5706201 prefixEnd_5706201 976674608055444732015055 := by
  unfold tailWord_5706201
  simp only [CollatzResearch.WordTrace]
  refine ⟨208122248400415793388694457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138748165600277195592462971 208122248400415793388694457)
  ·
    refine ⟨156091686300311845041520843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208122248400415793388694457 156091686300311845041520843)
    ·
      refine ⟨234137529450467767562281265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156091686300311845041520843 234137529450467767562281265)
      ·
        refine ⟨175603147087850825671710949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 234137529450467767562281265 175603147087850825671710949)
        ·
          refine ⟨32925590078972029813445803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 175603147087850825671710949 32925590078972029813445803)
          ·
            refine ⟨49388385118458044720168705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32925590078972029813445803 49388385118458044720168705)
            ·
              refine ⟨37041288838843533540126529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49388385118458044720168705 37041288838843533540126529)
              ·
                refine ⟨27780966629132650155094897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37041288838843533540126529 27780966629132650155094897)
                ·
                  refine ⟨20835724971849487616321173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27780966629132650155094897 20835724971849487616321173)
                  ·
                    refine ⟨976674608055444732015055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20835724971849487616321173 976674608055444732015055)
                    ·
                      rfl

theorem cell23_5706201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 2, 2, 6].length) (baseStart_5706201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5706201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5706201 prefixEnd_5706201 := by exact prefixLift 5706201
  have htrace : WordTrace (prefixWord ++ tailWord_5706201) baseStart_5706201 baseEnd_5706201 := by
    simpa [prefixWord, tailWord_5706201, baseEnd_5706201] using wordTrace_append hprefix tailTrace_5706201
  have hstable : (prefixWord ++ tailWord_5706201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5706201).length < 2 ^ (prefixWord ++ tailWord_5706201).sum := by decide
  have hdescent : baseEnd_5706201 < baseStart_5706201 := by decide
  rcases family_descends (prefixWord ++ tailWord_5706201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5706208 : List Nat := [2, 1, 1, 3, 1, 1, 3, 2, 3, 4, 2]
def baseStart_5706208 : Nat := 118140960795 + 5706208 * 2 ^ 59
def prefixEnd_5706208 : Nat := 4983230072969 + 3 ^ 40 * 5706208 * 2
def baseEnd_5706208 : Nat := 2930027418530915668657633

theorem tailTrace_5706208 : CollatzResearch.WordTrace tailWord_5706208 prefixEnd_5706208 2930027418530915668657633 := by
  unfold tailWord_5706208
  simp only [CollatzResearch.WordTrace]
  refine ⟨104061251855695216792099639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138748335807593622389466185 104061251855695216792099639)
  ·
    refine ⟨156091877783542825188149459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104061251855695216792099639 156091877783542825188149459)
    ·
      refine ⟨234137816675314237782224189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156091877783542825188149459 234137816675314237782224189)
      ·
        refine ⟨87801681253242839168334071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 234137816675314237782224189 87801681253242839168334071)
        ·
          refine ⟨131702521879864258752501107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87801681253242839168334071 131702521879864258752501107)
          ·
            refine ⟨197553782819796388128751661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131702521879864258752501107 197553782819796388128751661)
            ·
              refine ⟨74082668557423645548281873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 197553782819796388128751661 74082668557423645548281873)
              ·
                refine ⟨55562001418067734161211405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74082668557423645548281873 55562001418067734161211405)
                ·
                  refine ⟨20835750531775400310454277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55562001418067734161211405 20835750531775400310454277)
                  ·
                    refine ⟨3906703224707887558210177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20835750531775400310454277 3906703224707887558210177)
                    ·
                      refine ⟨2930027418530915668657633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3906703224707887558210177 2930027418530915668657633)
                      ·
                        rfl

theorem cell23_5706208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 2, 3, 4, 2].length) (baseStart_5706208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5706208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5706208 prefixEnd_5706208 := by exact prefixLift 5706208
  have htrace : WordTrace (prefixWord ++ tailWord_5706208) baseStart_5706208 baseEnd_5706208 := by
    simpa [prefixWord, tailWord_5706208, baseEnd_5706208] using wordTrace_append hprefix tailTrace_5706208
  have hstable : (prefixWord ++ tailWord_5706208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5706208).length < 2 ^ (prefixWord ++ tailWord_5706208).sum := by decide
  have hdescent : baseEnd_5706208 < baseStart_5706208 := by decide
  rcases family_descends (prefixWord ++ tailWord_5706208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5706218 : List Nat := [3, 1, 3, 1, 3, 2, 1, 1, 2, 6]
def baseStart_5706218 : Nat := 118140960795 + 5706218 * 2 ^ 59
def prefixEnd_5706218 : Nat := 4983230072969 + 3 ^ 40 * 5706218 * 2
def baseEnd_5706218 : Nat := 976677517779153543177529

theorem tailTrace_5706218 : CollatzResearch.WordTrace tailWord_5706218 prefixEnd_5706218 976677517779153543177529 := by
  unfold tailWord_5706218
  simp only [CollatzResearch.WordTrace]
  refine ⟨52030717110338551323015827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138748578960902803528042205 52030717110338551323015827)
  ·
    refine ⟨78046075665507826984523741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52030717110338551323015827 78046075665507826984523741)
    ·
      refine ⟨29267278374565435119196403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78046075665507826984523741 29267278374565435119196403)
      ·
        refine ⟨43900917561848152678794605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29267278374565435119196403 43900917561848152678794605)
        ·
          refine ⟨16462844085693057254547977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43900917561848152678794605 16462844085693057254547977)
          ·
            refine ⟨12347133064269792940910983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16462844085693057254547977 12347133064269792940910983)
            ·
              refine ⟨18520699596404689411366475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12347133064269792940910983 18520699596404689411366475)
              ·
                refine ⟨27781049394607034117049713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18520699596404689411366475 27781049394607034117049713)
                ·
                  refine ⟨20835787045955275587787285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27781049394607034117049713 20835787045955275587787285)
                  ·
                    refine ⟨976677517779153543177529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20835787045955275587787285 976677517779153543177529)
                    ·
                      rfl

theorem cell23_5706218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 1, 2, 6].length) (baseStart_5706218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5706218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5706218 prefixEnd_5706218 := by exact prefixLift 5706218
  have htrace : WordTrace (prefixWord ++ tailWord_5706218) baseStart_5706218 baseEnd_5706218 := by
    simpa [prefixWord, tailWord_5706218, baseEnd_5706218] using wordTrace_append hprefix tailTrace_5706218
  have hstable : (prefixWord ++ tailWord_5706218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5706218).length < 2 ^ (prefixWord ++ tailWord_5706218).sum := by decide
  have hdescent : baseEnd_5706218 < baseStart_5706218 := by decide
  rcases family_descends (prefixWord ++ tailWord_5706218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5706225 : List Nat := [1, 2, 2, 2, 3, 1, 4, 1, 1, 4, 2]
def baseStart_5706225 : Nat := 118140960795 + 5706225 * 2 ^ 59
def prefixEnd_5706225 : Nat := 4983230072969 + 3 ^ 40 * 5706225 * 2
def baseEnd_5706225 : Nat := 2930036147702042102145055

theorem tailTrace_5706225 : CollatzResearch.WordTrace tailWord_5706225 prefixEnd_5706225 2930036147702042102145055 := by
  unfold tailWord_5706225
  simp only [CollatzResearch.WordTrace]
  refine ⟨208123123752328845487568129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138748749168219230325045419 208123123752328845487568129)
  ·
    refine ⟨156092342814246634115676097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208123123752328845487568129 156092342814246634115676097)
    ·
      refine ⟨117069257110684975586757073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156092342814246634115676097 117069257110684975586757073)
      ·
        refine ⟨87801942833013731690067805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117069257110684975586757073 87801942833013731690067805)
        ·
          refine ⟨32925728562380149383775427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87801942833013731690067805 32925728562380149383775427)
          ·
            refine ⟨49388592843570224075663141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32925728562380149383775427 49388592843570224075663141)
            ·
              refine ⟨9260361158169417014186839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49388592843570224075663141 9260361158169417014186839)
              ·
                refine ⟨13890541737254125521280259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9260361158169417014186839 13890541737254125521280259)
                ·
                  refine ⟨20835812605881188281920389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13890541737254125521280259 20835812605881188281920389)
                  ·
                    refine ⟨3906714863602722802860073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20835812605881188281920389 3906714863602722802860073)
                    ·
                      refine ⟨2930036147702042102145055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3906714863602722802860073 2930036147702042102145055)
                      ·
                        rfl

theorem cell23_5706225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 1, 1, 4, 2].length) (baseStart_5706225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5706225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5706225 prefixEnd_5706225 := by exact prefixLift 5706225
  have htrace : WordTrace (prefixWord ++ tailWord_5706225) baseStart_5706225 baseEnd_5706225 := by
    simpa [prefixWord, tailWord_5706225, baseEnd_5706225] using wordTrace_append hprefix tailTrace_5706225
  have hstable : (prefixWord ++ tailWord_5706225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5706225).length < 2 ^ (prefixWord ++ tailWord_5706225).sum := by decide
  have hdescent : baseEnd_5706225 < baseStart_5706225 := by decide
  rcases family_descends (prefixWord ++ tailWord_5706225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5706271 : List Nat := [1, 1, 2, 4, 1, 1, 1, 3, 1, 1, 7]
def baseStart_5706271 : Nat := 118140960795 + 5706271 * 2 ^ 59
def prefixEnd_5706271 : Nat := 4983230072969 + 3 ^ 40 * 5706271 * 2
def baseEnd_5706271 : Nat := 2930059767812148922169843

theorem tailTrace_5706271 : CollatzResearch.WordTrace tailWord_5706271 prefixEnd_5706271 2930059767812148922169843 := by
  unfold tailWord_5706271
  simp only [CollatzResearch.WordTrace]
  refine ⟨208124801510162195343742667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138749867673441463562495111 208124801510162195343742667)
  ·
    refine ⟨312187202265243293015614001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208124801510162195343742667 312187202265243293015614001)
    ·
      refine ⟨234140401698932469761710501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 312187202265243293015614001 234140401698932469761710501)
      ·
        refine ⟨43901325318549838080320719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 234140401698932469761710501 43901325318549838080320719)
        ·
          refine ⟨65851987977824757120481079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43901325318549838080320719 65851987977824757120481079)
          ·
            refine ⟨98777981966737135680721619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65851987977824757120481079 98777981966737135680721619)
            ·
              refine ⟨148166972950105703521082429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98777981966737135680721619 148166972950105703521082429)
              ·
                refine ⟨55562614856289638820405911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 148166972950105703521082429 55562614856289638820405911)
                ·
                  refine ⟨83343922284434458230608867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55562614856289638820405911 83343922284434458230608867)
                  ·
                    refine ⟨125015883426651687345913301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 83343922284434458230608867 125015883426651687345913301)
                    ·
                      refine ⟨2930059767812148922169843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 125015883426651687345913301 2930059767812148922169843)
                      ·
                        rfl

theorem cell23_5706271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_5706271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5706271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5706271 prefixEnd_5706271 := by exact prefixLift 5706271
  have htrace : WordTrace (prefixWord ++ tailWord_5706271) baseStart_5706271 baseEnd_5706271 := by
    simpa [prefixWord, tailWord_5706271, baseEnd_5706271] using wordTrace_append hprefix tailTrace_5706271
  have hstable : (prefixWord ++ tailWord_5706271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5706271).length < 2 ^ (prefixWord ++ tailWord_5706271).sum := by decide
  have hdescent : baseEnd_5706271 < baseStart_5706271 := by decide
  rcases family_descends (prefixWord ++ tailWord_5706271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5706276 : List Nat := [2, 3, 1, 5, 2, 1, 1, 1, 1, 4, 2]
def baseStart_5706276 : Nat := 118140960795 + 5706276 * 2 ^ 59
def prefixEnd_5706276 : Nat := 4983230072969 + 3 ^ 40 * 5706276 * 2
def baseEnd_5706276 : Nat := 2930062335215421402607321

theorem tailTrace_5706276 : CollatzResearch.WordTrace tailWord_5706276 prefixEnd_5706276 2930062335215421402607321 := by
  unfold tailWord_5706276
  simp only [CollatzResearch.WordTrace]
  refine ⟨104062491937572040598837341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138749989250096054131783121 104062491937572040598837341)
  ·
    refine ⟨39023434476589515224564003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104062491937572040598837341 39023434476589515224564003)
    ·
      refine ⟨58535151714884272836846005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39023434476589515224564003 58535151714884272836846005)
      ·
        refine ⟨5487670473270400578454313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 58535151714884272836846005 5487670473270400578454313)
        ·
          refine ⟨4115752854952800433840735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5487670473270400578454313 4115752854952800433840735)
          ·
            refine ⟨6173629282429200650761103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4115752854952800433840735 6173629282429200650761103)
            ·
              refine ⟨9260443923643800976141655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6173629282429200650761103 9260443923643800976141655)
              ·
                refine ⟨13890665885465701464212483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9260443923643800976141655 13890665885465701464212483)
                ·
                  refine ⟨20835998828198552196318725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13890665885465701464212483 20835998828198552196318725)
                  ·
                    refine ⟨3906749780287228536809761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20835998828198552196318725 3906749780287228536809761)
                    ·
                      refine ⟨2930062335215421402607321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3906749780287228536809761 2930062335215421402607321)
                      ·
                        rfl

theorem cell23_5706276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_5706276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5706276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5706276 prefixEnd_5706276 := by exact prefixLift 5706276
  have htrace : WordTrace (prefixWord ++ tailWord_5706276) baseStart_5706276 baseEnd_5706276 := by
    simpa [prefixWord, tailWord_5706276, baseEnd_5706276] using wordTrace_append hprefix tailTrace_5706276
  have hstable : (prefixWord ++ tailWord_5706276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5706276).length < 2 ^ (prefixWord ++ tailWord_5706276).sum := by decide
  have hdescent : baseEnd_5706276 < baseStart_5706276 := by decide
  rcases family_descends (prefixWord ++ tailWord_5706276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5706291 : List Nat := [1, 1, 1, 2, 4, 2, 1, 1, 2, 8]
def baseStart_5706291 : Nat := 118140960795 + 5706291 * 2 ^ 59
def prefixEnd_5706291 : Nat := 4983230072969 + 3 ^ 40 * 5706291 * 2
def baseEnd_5706291 : Nat := 976690012475079614639917

theorem tailTrace_5706291 : CollatzResearch.WordTrace tailWord_5706291 prefixEnd_5706291 976690012475079614639917 := by
  unfold tailWord_5706291
  simp only [CollatzResearch.WordTrace]
  refine ⟨208125530970089738759470727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138750353980059825839647151 208125530970089738759470727)
  ·
    refine ⟨312188296455134608139206091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208125530970089738759470727 312188296455134608139206091)
    ·
      refine ⟨468282444682701912208809137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312188296455134608139206091 468282444682701912208809137)
      ·
        refine ⟨351211833512026434156606853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 468282444682701912208809137 351211833512026434156606853)
        ·
          refine ⟨65852218783504956404363785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 351211833512026434156606853 65852218783504956404363785)
          ·
            refine ⟨49389164087628717303272839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65852218783504956404363785 49389164087628717303272839)
            ·
              refine ⟨74083746131443075954909259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49389164087628717303272839 74083746131443075954909259)
              ·
                refine ⟨111125619197164613932363889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74083746131443075954909259 111125619197164613932363889)
                ·
                  refine ⟨83344214397873460449272917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 111125619197164613932363889 83344214397873460449272917)
                  ·
                    refine ⟨976690012475079614639917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 83344214397873460449272917 976690012475079614639917)
                    ·
                      rfl

theorem cell23_5706291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 2, 8].length) (baseStart_5706291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5706291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5706291 prefixEnd_5706291 := by exact prefixLift 5706291
  have htrace : WordTrace (prefixWord ++ tailWord_5706291) baseStart_5706291 baseEnd_5706291 := by
    simpa [prefixWord, tailWord_5706291, baseEnd_5706291] using wordTrace_append hprefix tailTrace_5706291
  have hstable : (prefixWord ++ tailWord_5706291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5706291).length < 2 ^ (prefixWord ++ tailWord_5706291).sum := by decide
  have hdescent : baseEnd_5706291 < baseStart_5706291 := by decide
  rcases family_descends (prefixWord ++ tailWord_5706291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5706298 : List Nat := [3, 1, 1, 1, 3, 3, 2, 1, 1, 3, 4]
def baseStart_5706298 : Nat := 118140960795 + 5706298 * 2 ^ 59
def prefixEnd_5706298 : Nat := 4983230072969 + 3 ^ 40 * 5706298 * 2
def baseEnd_5706298 : Nat := 2930073631789820316532219

theorem tailTrace_5706298 : CollatzResearch.WordTrace tailWord_5706298 prefixEnd_5706298 2930073631789820316532219 := by
  unfold tailWord_5706298
  simp only [CollatzResearch.WordTrace]
  refine ⟨52031446570266094738743887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138750524187376252636650365 52031446570266094738743887)
  ·
    refine ⟨78047169855399142108115831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52031446570266094738743887 78047169855399142108115831)
    ·
      refine ⟨117070754783098713162173747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78047169855399142108115831 117070754783098713162173747)
      ·
        refine ⟨175606132174648069743260621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117070754783098713162173747 175606132174648069743260621)
        ·
          refine ⟨65852299565493026153722733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 175606132174648069743260621 65852299565493026153722733)
          ·
            refine ⟨24694612337059884807646025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65852299565493026153722733 24694612337059884807646025)
            ·
              refine ⟨18520959252794913605734519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24694612337059884807646025 18520959252794913605734519)
              ·
                refine ⟨27781438879192370408601779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18520959252794913605734519 27781438879192370408601779)
                ·
                  refine ⟨41672158318788555612902669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27781438879192370408601779 41672158318788555612902669)
                  ·
                    refine ⟨15627059369545708354838501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41672158318788555612902669 15627059369545708354838501)
                    ·
                      refine ⟨2930073631789820316532219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15627059369545708354838501 2930073631789820316532219)
                      ·
                        rfl

theorem cell23_5706298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 1, 1, 3, 4].length) (baseStart_5706298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5706298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5706298 prefixEnd_5706298 := by exact prefixLift 5706298
  have htrace : WordTrace (prefixWord ++ tailWord_5706298) baseStart_5706298 baseEnd_5706298 := by
    simpa [prefixWord, tailWord_5706298, baseEnd_5706298] using wordTrace_append hprefix tailTrace_5706298
  have hstable : (prefixWord ++ tailWord_5706298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5706298).length < 2 ^ (prefixWord ++ tailWord_5706298).sum := by decide
  have hdescent : baseEnd_5706298 < baseStart_5706298 := by decide
  rcases family_descends (prefixWord ++ tailWord_5706298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5706325 : List Nat := [1, 3, 2, 2, 1, 1, 5, 1, 3, 4]
def baseStart_5706325 : Nat := 118140960795 + 5706325 * 2 ^ 59
def prefixEnd_5706325 : Nat := 4983230072969 + 3 ^ 40 * 5706325 * 2
def baseEnd_5706325 : Nat := 976695831922497236964865

theorem tailTrace_5706325 : CollatzResearch.WordTrace tailWord_5706325 prefixEnd_5706325 976695831922497236964865 := by
  unfold tailWord_5706325
  simp only [CollatzResearch.WordTrace]
  refine ⟨208126771051966562566208429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138751180701311041710805619 208126771051966562566208429)
  ·
    refine ⟨78047539144487460962328161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208126771051966562566208429 78047539144487460962328161)
    ·
      refine ⟨58535654358365595721746121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78047539144487460962328161 58535654358365595721746121)
      ·
        refine ⟨43901740768774196791309591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58535654358365595721746121 43901740768774196791309591)
        ·
          refine ⟨65852611153161295186964387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43901740768774196791309591 65852611153161295186964387)
          ·
            refine ⟨98778916729741942780446581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65852611153161295186964387 98778916729741942780446581)
            ·
              refine ⟨9260523443413307135666867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 98778916729741942780446581 9260523443413307135666867)
              ·
                refine ⟨13890785165119960703500301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9260523443413307135666867 13890785165119960703500301)
                ·
                  refine ⟨5209044436919985263812613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13890785165119960703500301 5209044436919985263812613)
                  ·
                    refine ⟨976695831922497236964865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5209044436919985263812613 976695831922497236964865)
                    ·
                      rfl

theorem cell23_5706325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 1, 3, 4].length) (baseStart_5706325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5706325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5706325 prefixEnd_5706325 := by exact prefixLift 5706325
  have htrace : WordTrace (prefixWord ++ tailWord_5706325) baseStart_5706325 baseEnd_5706325 := by
    simpa [prefixWord, tailWord_5706325, baseEnd_5706325] using wordTrace_append hprefix tailTrace_5706325
  have hstable : (prefixWord ++ tailWord_5706325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5706325).length < 2 ^ (prefixWord ++ tailWord_5706325).sum := by decide
  have hdescent : baseEnd_5706325 < baseStart_5706325 := by decide
  rcases family_descends (prefixWord ++ tailWord_5706325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5706348 : List Nat := [2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 3]
def baseStart_5706348 : Nat := 118140960795 + 5706348 * 2 ^ 59
def prefixEnd_5706348 : Nat := 4983230072969 + 3 ^ 40 * 5706348 * 2
def baseEnd_5706348 : Nat := 2930099305822545120906989

theorem tailTrace_5706348 : CollatzResearch.WordTrace tailWord_5706348 prefixEnd_5706348 2930099305822545120906989 := by
  unfold tailWord_5706348
  simp only [CollatzResearch.WordTrace]
  refine ⟨104063804965441618747147849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138751739953922158329530465 104063804965441618747147849)
  ·
    refine ⟨78047853724081214060360887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104063804965441618747147849 78047853724081214060360887)
    ·
      refine ⟨117071780586121821090541331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78047853724081214060360887 117071780586121821090541331)
      ·
        refine ⟨175607670879182731635811997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117071780586121821090541331 175607670879182731635811997)
        ·
          refine ⟨65852876579693524363429499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 175607670879182731635811997 65852876579693524363429499)
          ·
            refine ⟨98779314869540286545144249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65852876579693524363429499 98779314869540286545144249)
            ·
              refine ⟨74084486152155214908858187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98779314869540286545144249 74084486152155214908858187)
              ·
                refine ⟨111126729228232822363287281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74084486152155214908858187 111126729228232822363287281)
                ·
                  refine ⟨83345046921174616772465461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 111126729228232822363287281 83345046921174616772465461)
                  ·
                    refine ⟨7813598148860120322418637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 83345046921174616772465461 7813598148860120322418637)
                    ·
                      refine ⟨2930099305822545120906989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7813598148860120322418637 2930099305822545120906989)
                      ·
                        rfl

theorem cell23_5706348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 3].length) (baseStart_5706348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5706348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5706348 prefixEnd_5706348 := by exact prefixLift 5706348
  have htrace : WordTrace (prefixWord ++ tailWord_5706348) baseStart_5706348 baseEnd_5706348 := by
    simpa [prefixWord, tailWord_5706348, baseEnd_5706348] using wordTrace_append hprefix tailTrace_5706348
  have hstable : (prefixWord ++ tailWord_5706348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5706348).length < 2 ^ (prefixWord ++ tailWord_5706348).sum := by decide
  have hdescent : baseEnd_5706348 < baseStart_5706348 := by decide
  rcases family_descends (prefixWord ++ tailWord_5706348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5706352 : List Nat := [2, 1, 1, 1, 7, 1, 2, 1, 2, 2, 3]
def baseStart_5706352 : Nat := 118140960795 + 5706352 * 2 ^ 59
def prefixEnd_5706352 : Nat := 4983230072969 + 3 ^ 40 * 5706352 * 2
def baseEnd_5706352 : Nat := 2930101359745163105256971

theorem tailTrace_5706352 : CollatzResearch.WordTrace tailWord_5706352 prefixEnd_5706352 2930101359745163105256971 := by
  unfold tailWord_5706352
  simp only [CollatzResearch.WordTrace]
  refine ⟨104063877911434373088720655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138751837215245830784960873 104063877911434373088720655)
  ·
    refine ⟨156095816867151559633080983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104063877911434373088720655 156095816867151559633080983)
    ·
      refine ⟨234143725300727339449621475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156095816867151559633080983 234143725300727339449621475)
      ·
        refine ⟨351215587951091009174432213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234143725300727339449621475 351215587951091009174432213)
        ·
          refine ⟨8231615342603695527525755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 351215587951091009174432213 8231615342603695527525755)
          ·
            refine ⟨12347423013905543291288633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8231615342603695527525755 12347423013905543291288633)
            ·
              refine ⟨9260567260429157468466475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12347423013905543291288633 9260567260429157468466475)
              ·
                refine ⟨13890850890643736202699713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9260567260429157468466475 13890850890643736202699713)
                ·
                  refine ⟨10418138167982802152024785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13890850890643736202699713 10418138167982802152024785)
                  ·
                    refine ⟨7813603625987101614018589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10418138167982802152024785 7813603625987101614018589)
                    ·
                      refine ⟨2930101359745163105256971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7813603625987101614018589 2930101359745163105256971)
                      ·
                        rfl

theorem cell23_5706352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 1, 2, 2, 3].length) (baseStart_5706352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5706352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5706352 prefixEnd_5706352 := by exact prefixLift 5706352
  have htrace : WordTrace (prefixWord ++ tailWord_5706352) baseStart_5706352 baseEnd_5706352 := by
    simpa [prefixWord, tailWord_5706352, baseEnd_5706352] using wordTrace_append hprefix tailTrace_5706352
  have hstable : (prefixWord ++ tailWord_5706352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5706352).length < 2 ^ (prefixWord ++ tailWord_5706352).sum := by decide
  have hdescent : baseEnd_5706352 < baseStart_5706352 := by decide
  rcases family_descends (prefixWord ++ tailWord_5706352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5706382 : List Nat := [4, 1, 1, 3, 1, 1, 2, 3, 3, 1, 3]
def baseStart_5706382 : Nat := 118140960795 + 5706382 * 2 ^ 59
def prefixEnd_5706382 : Nat := 4983230072969 + 3 ^ 40 * 5706382 * 2
def baseEnd_5706382 : Nat := 2930116764164797987881833

theorem tailTrace_5706382 : CollatzResearch.WordTrace tailWord_5706382 prefixEnd_5706382 2930116764164797987881833 := by
  unfold tailWord_5706382
  simp only [CollatzResearch.WordTrace]
  refine ⟨26016106251595007662629175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138752566675173374200688933 26016106251595007662629175)
  ·
    refine ⟨39024159377392511493943763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26016106251595007662629175 39024159377392511493943763)
    ·
      refine ⟨58536239066088767240915645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39024159377392511493943763 58536239066088767240915645)
      ·
        refine ⟨21951089649783287715343367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58536239066088767240915645 21951089649783287715343367)
        ·
          refine ⟨32926634474674931573015051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21951089649783287715343367 32926634474674931573015051)
          ·
            refine ⟨49389951712012397359522577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32926634474674931573015051 49389951712012397359522577)
            ·
              refine ⟨37042463784009298019641933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49389951712012397359522577 37042463784009298019641933)
              ·
                refine ⟨13890923919003486757365725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37042463784009298019641933 13890923919003486757365725)
                ·
                  refine ⟨5209096469626307534012147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13890923919003486757365725 5209096469626307534012147)
                  ·
                    refine ⟨7813644704439461301018221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5209096469626307534012147 7813644704439461301018221)
                    ·
                      refine ⟨2930116764164797987881833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7813644704439461301018221 2930116764164797987881833)
                      ·
                        rfl

theorem cell23_5706382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 3, 3, 1, 3].length) (baseStart_5706382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5706382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5706382 prefixEnd_5706382 := by exact prefixLift 5706382
  have htrace : WordTrace (prefixWord ++ tailWord_5706382) baseStart_5706382 baseEnd_5706382 := by
    simpa [prefixWord, tailWord_5706382, baseEnd_5706382] using wordTrace_append hprefix tailTrace_5706382
  have hstable : (prefixWord ++ tailWord_5706382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5706382).length < 2 ^ (prefixWord ++ tailWord_5706382).sum := by decide
  have hdescent : baseEnd_5706382 < baseStart_5706382 := by decide
  rcases family_descends (prefixWord ++ tailWord_5706382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5706405 : List Nat := [1, 3, 1, 2, 1, 2, 1, 6, 1, 1, 4]
def baseStart_5706405 : Nat := 118140960795 + 5706405 * 2 ^ 59
def prefixEnd_5706405 : Nat := 4983230072969 + 3 ^ 40 * 5706405 * 2
def baseEnd_5706405 : Nat := 2930128574219851397894227

theorem tailTrace_5706405 : CollatzResearch.WordTrace tailWord_5706405 prefixEnd_5706405 2930128574219851397894227 := by
  unfold tailWord_5706405
  simp only [CollatzResearch.WordTrace]
  refine ⟨208129688891676736229120669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138753125927784490819413779 208129688891676736229120669)
  ·
    refine ⟨78048633334378776085920251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208129688891676736229120669 78048633334378776085920251)
    ·
      refine ⟨117072950001568164128880377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78048633334378776085920251 117072950001568164128880377)
      ·
        refine ⟨87804712501176123096660283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117072950001568164128880377 87804712501176123096660283)
        ·
          refine ⟨131707068751764184644990425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87804712501176123096660283 131707068751764184644990425)
          ·
            refine ⟨98780301563823138483742819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131707068751764184644990425 98780301563823138483742819)
            ·
              refine ⟨148170452345734707725614229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98780301563823138483742819 148170452345734707725614229)
              ·
                refine ⟨6945489953706314424638167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 148170452345734707725614229 6945489953706314424638167)
                ·
                  refine ⟨10418234930559471636957251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6945489953706314424638167 10418234930559471636957251)
                  ·
                    refine ⟨15627352395839207455435877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10418234930559471636957251 15627352395839207455435877)
                    ·
                      refine ⟨2930128574219851397894227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15627352395839207455435877 2930128574219851397894227)
                      ·
                        rfl

theorem cell23_5706405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 6, 1, 1, 4].length) (baseStart_5706405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5706405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5706405 prefixEnd_5706405 := by exact prefixLift 5706405
  have htrace : WordTrace (prefixWord ++ tailWord_5706405) baseStart_5706405 baseEnd_5706405 := by
    simpa [prefixWord, tailWord_5706405, baseEnd_5706405] using wordTrace_append hprefix tailTrace_5706405
  have hstable : (prefixWord ++ tailWord_5706405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5706405).length < 2 ^ (prefixWord ++ tailWord_5706405).sum := by decide
  have hdescent : baseEnd_5706405 < baseStart_5706405 := by decide
  rcases family_descends (prefixWord ++ tailWord_5706405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5706418 : List Nat := [3, 2, 1, 1, 1, 2, 1, 2, 3, 1, 6]
def baseStart_5706418 : Nat := 118140960795 + 5706418 * 2 ^ 59
def prefixEnd_5706418 : Nat := 4983230072969 + 3 ^ 40 * 5706418 * 2
def baseEnd_5706418 : Nat := 2930135249468359847031667

theorem tailTrace_5706418 : CollatzResearch.WordTrace tailWord_5706418 prefixEnd_5706418 2930135249468359847031667 := by
  unfold tailWord_5706418
  simp only [CollatzResearch.WordTrace]
  refine ⟨52032540760157409862335977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138753442027086426299562605 52032540760157409862335977)
  ·
    refine ⟨39024405570118057396751983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52032540760157409862335977 39024405570118057396751983)
    ·
      refine ⟨58536608355177086095127975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39024405570118057396751983 58536608355177086095127975)
      ·
        refine ⟨87804912532765629142691963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58536608355177086095127975 87804912532765629142691963)
        ·
          refine ⟨131707368799148443714037945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87804912532765629142691963 131707368799148443714037945)
          ·
            refine ⟨98780526599361332785528459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131707368799148443714037945 98780526599361332785528459)
            ·
              refine ⟨148170789899041999178292689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98780526599361332785528459 148170789899041999178292689)
              ·
                refine ⟨111128092424281499383719517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 148170789899041999178292689 111128092424281499383719517)
                ·
                  refine ⟨41673034659105562268894819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 111128092424281499383719517 41673034659105562268894819)
                  ·
                    refine ⟨62509551988658343403342229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41673034659105562268894819 62509551988658343403342229)
                    ·
                      refine ⟨2930135249468359847031667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62509551988658343403342229 2930135249468359847031667)
                      ·
                        rfl

theorem cell23_5706418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 3, 1, 6].length) (baseStart_5706418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5706418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5706418 prefixEnd_5706418 := by exact prefixLift 5706418
  have htrace : WordTrace (prefixWord ++ tailWord_5706418) baseStart_5706418 baseEnd_5706418 := by
    simpa [prefixWord, tailWord_5706418, baseEnd_5706418] using wordTrace_append hprefix tailTrace_5706418
  have hstable : (prefixWord ++ tailWord_5706418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5706418).length < 2 ^ (prefixWord ++ tailWord_5706418).sum := by decide
  have hdescent : baseEnd_5706418 < baseStart_5706418 := by decide
  rcases family_descends (prefixWord ++ tailWord_5706418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5706428 : List Nat := [2, 2, 2, 3, 1, 1, 12]
def baseStart_5706428 : Nat := 118140960795 + 5706428 * 2 ^ 59
def prefixEnd_5706428 : Nat := 4983230072969 + 3 ^ 40 * 5706428 * 2
def baseEnd_5706428 : Nat := 36174572645369195159341

theorem tailTrace_5706428 : CollatzResearch.WordTrace tailWord_5706428 prefixEnd_5706428 36174572645369195159341 := by
  unfold tailWord_5706428
  simp only [CollatzResearch.WordTrace]
  refine ⟨104065263885296705578603969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138753685180395607438138625 104065263885296705578603969)
  ·
    refine ⟨78048947913972529183952977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104065263885296705578603969 78048947913972529183952977)
    ·
      refine ⟨58536710935479396887964733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78048947913972529183952977 58536710935479396887964733)
      ·
        refine ⟨21951266600804773832986775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58536710935479396887964733 21951266600804773832986775)
        ·
          refine ⟨32926899901207160749480163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21951266600804773832986775 32926899901207160749480163)
          ·
            refine ⟨49390349851810741124220245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32926899901207160749480163 49390349851810741124220245)
            ·
              refine ⟨36174572645369195159341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 49390349851810741124220245 36174572645369195159341)
              ·
                rfl

theorem cell23_5706428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 12].length) (baseStart_5706428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5706428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5706428 prefixEnd_5706428 := by exact prefixLift 5706428
  have htrace : WordTrace (prefixWord ++ tailWord_5706428) baseStart_5706428 baseEnd_5706428 := by
    simpa [prefixWord, tailWord_5706428, baseEnd_5706428] using wordTrace_append hprefix tailTrace_5706428
  have hstable : (prefixWord ++ tailWord_5706428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5706428).length < 2 ^ (prefixWord ++ tailWord_5706428).sum := by decide
  have hdescent : baseEnd_5706428 < baseStart_5706428 := by decide
  rcases family_descends (prefixWord ++ tailWord_5706428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5706432 : List Nat := [2, 1, 1, 2, 4, 2, 3, 2, 2, 4]
def baseStart_5706432 : Nat := 118140960795 + 5706432 * 2 ^ 59
def prefixEnd_5706432 : Nat := 4983230072969 + 3 ^ 40 * 5706432 * 2
def baseEnd_5706432 : Nat := 976714146065840930752201

theorem tailTrace_5706432 : CollatzResearch.WordTrace tailWord_5706432 prefixEnd_5706432 976714146065840930752201 := by
  unfold tailWord_5706432
  simp only [CollatzResearch.WordTrace]
  refine ⟨104065336831289459920176775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138753782441719279893569033 104065336831289459920176775)
  ·
    refine ⟨156098005246934189880265163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104065336831289459920176775 156098005246934189880265163)
    ·
      refine ⟨234147007870401284820397745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156098005246934189880265163 234147007870401284820397745)
      ·
        refine ⟨175610255902800963615298309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 234147007870401284820397745 175610255902800963615298309)
        ·
          refine ⟨32926922981775180677868433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 175610255902800963615298309 32926922981775180677868433)
          ·
            refine ⟨24695192236331385508401325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32926922981775180677868433 24695192236331385508401325)
            ·
              refine ⟨9260697088624269565650497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24695192236331385508401325 9260697088624269565650497)
              ·
                refine ⟨6945522816468202174237873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9260697088624269565650497 6945522816468202174237873)
                ·
                  refine ⟨5209142112351151630678405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6945522816468202174237873 5209142112351151630678405)
                  ·
                    refine ⟨976714146065840930752201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5209142112351151630678405 976714146065840930752201)
                    ·
                      rfl

theorem cell23_5706432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 2, 2, 4].length) (baseStart_5706432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5706432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5706432 prefixEnd_5706432 := by exact prefixLift 5706432
  have htrace : WordTrace (prefixWord ++ tailWord_5706432) baseStart_5706432 baseEnd_5706432 := by
    simpa [prefixWord, tailWord_5706432, baseEnd_5706432] using wordTrace_append hprefix tailTrace_5706432
  have hstable : (prefixWord ++ tailWord_5706432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5706432).length < 2 ^ (prefixWord ++ tailWord_5706432).sum := by decide
  have hdescent : baseEnd_5706432 < baseStart_5706432 := by decide
  rcases family_descends (prefixWord ++ tailWord_5706432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5706452 : List Nat := [2, 4, 1, 3, 2, 1, 1, 1, 1, 1, 6]
def baseStart_5706452 : Nat := 118140960795 + 5706452 * 2 ^ 59
def prefixEnd_5706452 : Nat := 4983230072969 + 3 ^ 40 * 5706452 * 2
def baseEnd_5706452 : Nat := 2930152707810612714006511

theorem tailTrace_5706452 : CollatzResearch.WordTrace tailWord_5706452 prefixEnd_5706452 2930152707810612714006511 := by
  unfold tailWord_5706452
  simp only [CollatzResearch.WordTrace]
  refine ⟨104065701561253231628040805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138754268748337642170721073 104065701561253231628040805)
  ·
    refine ⟨19512319042734980930257651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104065701561253231628040805 19512319042734980930257651)
    ·
      refine ⟨29268478564102471395386477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19512319042734980930257651 29268478564102471395386477)
      ·
        refine ⟨10975679461538426773269929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29268478564102471395386477 10975679461538426773269929)
        ·
          refine ⟨8231759596153820079952447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10975679461538426773269929 8231759596153820079952447)
          ·
            refine ⟨12347639394230730119928671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8231759596153820079952447 12347639394230730119928671)
            ·
              refine ⟨18521459091346095179893007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12347639394230730119928671 18521459091346095179893007)
              ·
                refine ⟨27782188637019142769839511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18521459091346095179893007 27782188637019142769839511)
                ·
                  refine ⟨41673282955528714154759267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27782188637019142769839511 41673282955528714154759267)
                  ·
                    refine ⟨62509924433293071232138901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41673282955528714154759267 62509924433293071232138901)
                    ·
                      refine ⟨2930152707810612714006511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62509924433293071232138901 2930152707810612714006511)
                      ·
                        rfl

theorem cell23_5706452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_5706452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5706452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5706452 prefixEnd_5706452 := by exact prefixLift 5706452
  have htrace : WordTrace (prefixWord ++ tailWord_5706452) baseStart_5706452 baseEnd_5706452 := by
    simpa [prefixWord, tailWord_5706452, baseEnd_5706452] using wordTrace_append hprefix tailTrace_5706452
  have hstable : (prefixWord ++ tailWord_5706452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5706452).length < 2 ^ (prefixWord ++ tailWord_5706452).sum := by decide
  have hdescent : baseEnd_5706452 < baseStart_5706452 := by decide
  rcases family_descends (prefixWord ++ tailWord_5706452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5706546 : List Nat := [3, 2, 1, 1, 3, 1, 4, 2, 2, 2, 2]
def baseStart_5706546 : Nat := 118140960795 + 5706546 * 2 ^ 59
def prefixEnd_5706546 : Nat := 4983230072969 + 3 ^ 40 * 5706546 * 2
def baseEnd_5706546 : Nat := 2930200974992135346231079

theorem tailTrace_5706546 : CollatzResearch.WordTrace tailWord_5706546 prefixEnd_5706546 2930200974992135346231079 := by
  unfold tailWord_5706546
  simp only [CollatzResearch.WordTrace]
  refine ⟨52033707896041479327500873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138756554389443944873335661 52033707896041479327500873)
  ·
    refine ⟨39025280922031109495625655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52033707896041479327500873 39025280922031109495625655)
    ·
      refine ⟨58537921383046664243438483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39025280922031109495625655 58537921383046664243438483)
      ·
        refine ⟨87806882074569996365157725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58537921383046664243438483 87806882074569996365157725)
        ·
          refine ⟨32927580777963748636934147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87806882074569996365157725 32927580777963748636934147)
          ·
            refine ⟨49391371166945622955401221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32927580777963748636934147 49391371166945622955401221)
            ·
              refine ⟨9260882093802304304137729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49391371166945622955401221 9260882093802304304137729)
              ·
                refine ⟨6945661570351728228103297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9260882093802304304137729 6945661570351728228103297)
                ·
                  refine ⟨5209246177763796171077473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6945661570351728228103297 5209246177763796171077473)
                  ·
                    refine ⟨3906934633322847128308105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5209246177763796171077473 3906934633322847128308105)
                    ·
                      refine ⟨2930200974992135346231079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3906934633322847128308105 2930200974992135346231079)
                      ·
                        rfl

theorem cell23_5706546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 2, 2, 2, 2].length) (baseStart_5706546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5706546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5706546 prefixEnd_5706546 := by exact prefixLift 5706546
  have htrace : WordTrace (prefixWord ++ tailWord_5706546) baseStart_5706546 baseEnd_5706546 := by
    simpa [prefixWord, tailWord_5706546, baseEnd_5706546] using wordTrace_append hprefix tailTrace_5706546
  have hstable : (prefixWord ++ tailWord_5706546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5706546).length < 2 ^ (prefixWord ++ tailWord_5706546).sum := by decide
  have hdescent : baseEnd_5706546 < baseStart_5706546 := by decide
  rcases family_descends (prefixWord ++ tailWord_5706546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5706552 : List Nat := [2, 1, 2, 1, 3, 2, 3, 4, 5]
def baseStart_5706552 : Nat := 118140960795 + 5706552 * 2 ^ 59
def prefixEnd_5706552 : Nat := 4983230072969 + 3 ^ 40 * 5706552 * 2
def baseEnd_5706552 : Nat := 325578228430673591417339

theorem tailTrace_5706552 : CollatzResearch.WordTrace tailWord_5706552 prefixEnd_5706552 325578228430673591417339 := by
  unfold tailWord_5706552
  simp only [CollatzResearch.WordTrace]
  refine ⟨104067525211072090167360955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138756700281429453556481273 104067525211072090167360955)
  ·
    refine ⟨156101287816608135251041433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104067525211072090167360955 156101287816608135251041433)
    ·
      refine ⟨117075965862456101438281075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156101287816608135251041433 117075965862456101438281075)
      ·
        refine ⟨175613948793684152157421613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117075965862456101438281075 175613948793684152157421613)
        ·
          refine ⟨65855230797631557059033105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 175613948793684152157421613 65855230797631557059033105)
          ·
            refine ⟨49391423098223667794274829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65855230797631557059033105 49391423098223667794274829)
            ·
              refine ⟨18521783661833875422853061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49391423098223667794274829 18521783661833875422853061)
              ·
                refine ⟨3472834436593851641784949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18521783661833875422853061 3472834436593851641784949)
                ·
                  refine ⟨325578228430673591417339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3472834436593851641784949 325578228430673591417339)
                  ·
                    rfl

theorem cell23_5706552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 4, 5].length) (baseStart_5706552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5706552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5706552 prefixEnd_5706552 := by exact prefixLift 5706552
  have htrace : WordTrace (prefixWord ++ tailWord_5706552) baseStart_5706552 baseEnd_5706552 := by
    simpa [prefixWord, tailWord_5706552, baseEnd_5706552] using wordTrace_append hprefix tailTrace_5706552
  have hstable : (prefixWord ++ tailWord_5706552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5706552).length < 2 ^ (prefixWord ++ tailWord_5706552).sum := by decide
  have hdescent : baseEnd_5706552 < baseStart_5706552 := by decide
  rcases family_descends (prefixWord ++ tailWord_5706552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5706663 : List Nat := [1, 1, 6, 1, 4, 1, 1, 1, 3, 4]
def baseStart_5706663 : Nat := 118140960795 + 5706663 * 2 ^ 59
def prefixEnd_5706663 : Nat := 4983230072969 + 3 ^ 40 * 5706663 * 2
def baseEnd_5706663 : Nat := 976753684076237129489347

theorem tailTrace_5706663 : CollatzResearch.WordTrace tailWord_5706663 prefixEnd_5706663 976753684076237129489347 := by
  unfold tailWord_5706663
  simp only [CollatzResearch.WordTrace]
  refine ⟨208139098924742046292012643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138759399283161364194675095 208139098924742046292012643)
  ·
    refine ⟨312208648387113069438018965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208139098924742046292012643 312208648387113069438018965)
    ·
      refine ⟨14634780393145925129907139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 312208648387113069438018965 14634780393145925129907139)
      ·
        refine ⟨21952170589718887694860709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14634780393145925129907139 21952170589718887694860709)
        ·
          refine ⟨4116031985572291442786383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21952170589718887694860709 4116031985572291442786383)
          ·
            refine ⟨6174047978358437164179575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4116031985572291442786383 6174047978358437164179575)
            ·
              refine ⟨9261071967537655746269363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6174047978358437164179575 9261071967537655746269363)
              ·
                refine ⟨13891607951306483619404045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9261071967537655746269363 13891607951306483619404045)
                ·
                  refine ⟨5209352981739931357276517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13891607951306483619404045 5209352981739931357276517)
                  ·
                    refine ⟨976753684076237129489347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5209352981739931357276517 976753684076237129489347)
                    ·
                      rfl

theorem cell23_5706663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 1, 3, 4].length) (baseStart_5706663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5706663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5706663 prefixEnd_5706663 := by exact prefixLift 5706663
  have htrace : WordTrace (prefixWord ++ tailWord_5706663) baseStart_5706663 baseEnd_5706663 := by
    simpa [prefixWord, tailWord_5706663, baseEnd_5706663] using wordTrace_append hprefix tailTrace_5706663
  have hstable : (prefixWord ++ tailWord_5706663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5706663).length < 2 ^ (prefixWord ++ tailWord_5706663).sum := by decide
  have hdescent : baseEnd_5706663 < baseStart_5706663 := by decide
  rcases family_descends (prefixWord ++ tailWord_5706663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5706676 : List Nat := [2, 5, 2, 1, 1, 2, 1, 3, 6]
def baseStart_5706676 : Nat := 118140960795 + 5706676 * 2 ^ 59
def prefixEnd_5706676 : Nat := 4983230072969 + 3 ^ 40 * 5706676 * 2
def baseEnd_5706676 : Nat := 325585303053024426400609

theorem tailTrace_5706676 : CollatzResearch.WordTrace tailWord_5706676 prefixEnd_5706676 325585303053024426400609 := by
  unfold tailWord_5706676
  simp only [CollatzResearch.WordTrace]
  refine ⟨104069786536847474756117941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138759715382463299674823921 104069786536847474756117941)
  ·
    refine ⟨9756542487829450758386057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 104069786536847474756117941 9756542487829450758386057)
    ·
      refine ⟨7317406865872088068789543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9756542487829450758386057 7317406865872088068789543)
      ·
        refine ⟨10976110298808132103184315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7317406865872088068789543 10976110298808132103184315)
        ·
          refine ⟨16464165448212198154776473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10976110298808132103184315 16464165448212198154776473)
          ·
            refine ⟨12348124086159148616082355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16464165448212198154776473 12348124086159148616082355)
            ·
              refine ⟨18522186129238722924123533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12348124086159148616082355 18522186129238722924123533)
              ·
                refine ⟨6945819798464521096546325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18522186129238722924123533 6945819798464521096546325)
                ·
                  refine ⟨325585303053024426400609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6945819798464521096546325 325585303053024426400609)
                  ·
                    rfl

theorem cell23_5706676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 3, 6].length) (baseStart_5706676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5706676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5706676 prefixEnd_5706676 := by exact prefixLift 5706676
  have htrace : WordTrace (prefixWord ++ tailWord_5706676) baseStart_5706676 baseEnd_5706676 := by
    simpa [prefixWord, tailWord_5706676, baseEnd_5706676] using wordTrace_append hprefix tailTrace_5706676
  have hstable : (prefixWord ++ tailWord_5706676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5706676).length < 2 ^ (prefixWord ++ tailWord_5706676).sum := by decide
  have hdescent : baseEnd_5706676 < baseStart_5706676 := by decide
  rcases family_descends (prefixWord ++ tailWord_5706676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5706702 : List Nat := [4, 1, 1, 1, 2, 3, 1, 1, 3, 6]
def baseStart_5706702 : Nat := 118140960795 + 5706702 * 2 ^ 59
def prefixEnd_5706702 : Nat := 4983230072969 + 3 ^ 40 * 5706702 * 2
def baseEnd_5706702 : Nat := 976760359324745578626787

theorem tailTrace_5706702 : CollatzResearch.WordTrace tailWord_5706702 prefixEnd_5706702 976760359324745578626787 := by
  unfold tailWord_5706702
  simp only [CollatzResearch.WordTrace]
  refine ⟨26017565171450094494085295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138760347581067170635121573 26017565171450094494085295)
  ·
    refine ⟨39026347757175141741127943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26017565171450094494085295 39026347757175141741127943)
    ·
      refine ⟨58539521635762712611691915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39026347757175141741127943 58539521635762712611691915)
      ·
        refine ⟨87809282453644068917537873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58539521635762712611691915 87809282453644068917537873)
        ·
          refine ⟨65856961840233051688153405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87809282453644068917537873 65856961840233051688153405)
          ·
            refine ⟨24696360690087394383057527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65856961840233051688153405 24696360690087394383057527)
            ·
              refine ⟨37044541035131091574586291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24696360690087394383057527 37044541035131091574586291)
              ·
                refine ⟨55566811552696637361879437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37044541035131091574586291 55566811552696637361879437)
                ·
                  refine ⟨20837554332261239010704789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55566811552696637361879437 20837554332261239010704789)
                  ·
                    refine ⟨976760359324745578626787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20837554332261239010704789 976760359324745578626787)
                    ·
                      rfl

theorem cell23_5706702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 1, 3, 6].length) (baseStart_5706702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5706702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5706702 prefixEnd_5706702 := by exact prefixLift 5706702
  have htrace : WordTrace (prefixWord ++ tailWord_5706702) baseStart_5706702 baseEnd_5706702 := by
    simpa [prefixWord, tailWord_5706702, baseEnd_5706702] using wordTrace_append hprefix tailTrace_5706702
  have hstable : (prefixWord ++ tailWord_5706702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5706702).length < 2 ^ (prefixWord ++ tailWord_5706702).sum := by decide
  have hdescent : baseEnd_5706702 < baseStart_5706702 := by decide
  rcases family_descends (prefixWord ++ tailWord_5706702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5706759 : List Nat := [1, 1, 4, 3, 1, 1, 1, 4, 1, 3, 3]
def baseStart_5706759 : Nat := 118140960795 + 5706759 * 2 ^ 59
def prefixEnd_5706759 : Nat := 4983230072969 + 3 ^ 40 * 5706759 * 2
def baseEnd_5706759 : Nat := 2930310346371543012867599

theorem tailTrace_5706759 : CollatzResearch.WordTrace tailWord_5706759 prefixEnd_5706759 2930310346371543012867599 := by
  unfold tailWord_5706759
  simp only [CollatzResearch.WordTrace]
  refine ⟨208142600332394254687507331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138761733554929503125004887 208142600332394254687507331)
  ·
    refine ⟨312213900498591382031260997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208142600332394254687507331 312213900498591382031260997)
    ·
      refine ⟨58540106343485884130861437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 312213900498591382031260997 58540106343485884130861437)
      ·
        refine ⟨21952539878807206549073039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58540106343485884130861437 21952539878807206549073039)
        ·
          refine ⟨32928809818210809823609559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21952539878807206549073039 32928809818210809823609559)
          ·
            refine ⟨49393214727316214735414339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32928809818210809823609559 49393214727316214735414339)
            ·
              refine ⟨74089822090974322103121509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49393214727316214735414339 74089822090974322103121509)
              ·
                refine ⟨13891841642057685394335283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74089822090974322103121509 13891841642057685394335283)
                ·
                  refine ⟨20837762463086528091502925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13891841642057685394335283 20837762463086528091502925)
                  ·
                    refine ⟨7814160923657448034313597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20837762463086528091502925 7814160923657448034313597)
                    ·
                      refine ⟨2930310346371543012867599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7814160923657448034313597 2930310346371543012867599)
                      ·
                        rfl

theorem cell23_5706759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 4, 1, 3, 3].length) (baseStart_5706759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5706759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5706759 prefixEnd_5706759 := by exact prefixLift 5706759
  have htrace : WordTrace (prefixWord ++ tailWord_5706759) baseStart_5706759 baseEnd_5706759 := by
    simpa [prefixWord, tailWord_5706759, baseEnd_5706759] using wordTrace_append hprefix tailTrace_5706759
  have hstable : (prefixWord ++ tailWord_5706759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5706759).length < 2 ^ (prefixWord ++ tailWord_5706759).sum := by decide
  have hdescent : baseEnd_5706759 < baseStart_5706759 := by decide
  rcases family_descends (prefixWord ++ tailWord_5706759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5706760 : List Nat := [2, 1, 3, 2, 1, 4, 2, 3, 1, 2, 2]
def baseStart_5706760 : Nat := 118140960795 + 5706760 * 2 ^ 59
def prefixEnd_5706760 : Nat := 4983230072969 + 3 ^ 40 * 5706760 * 2
def baseEnd_5706760 : Nat := 2930310859852197508955095

theorem tailTrace_5706760 : CollatzResearch.WordTrace tailWord_5706760 prefixEnd_5706760 2930310859852197508955095 := by
  unfold tailWord_5706760
  simp only [CollatzResearch.WordTrace]
  refine ⟨104071318402695315929146867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138761757870260421238862489 104071318402695315929146867)
  ·
    refine ⟨156106977604042973893720301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104071318402695315929146867 156106977604042973893720301)
    ·
      refine ⟨58540116601516115210145113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156106977604042973893720301 58540116601516115210145113)
      ·
        refine ⟨43905087451137086407608835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58540116601516115210145113 43905087451137086407608835)
        ·
          refine ⟨65857631176705629611413253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43905087451137086407608835 65857631176705629611413253)
          ·
            refine ⟨12348305845632305552139985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65857631176705629611413253 12348305845632305552139985)
            ·
              refine ⟨9261229384224229164104989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12348305845632305552139985 9261229384224229164104989)
              ·
                refine ⟨3472961019084085936539371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9261229384224229164104989 3472961019084085936539371)
                ·
                  refine ⟨5209441528626128904809057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3472961019084085936539371 5209441528626128904809057)
                  ·
                    refine ⟨3907081146469596678606793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5209441528626128904809057 3907081146469596678606793)
                    ·
                      refine ⟨2930310859852197508955095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3907081146469596678606793 2930310859852197508955095)
                      ·
                        rfl

theorem cell23_5706760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 3, 1, 2, 2].length) (baseStart_5706760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5706760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5706760 prefixEnd_5706760 := by exact prefixLift 5706760
  have htrace : WordTrace (prefixWord ++ tailWord_5706760) baseStart_5706760 baseEnd_5706760 := by
    simpa [prefixWord, tailWord_5706760, baseEnd_5706760] using wordTrace_append hprefix tailTrace_5706760
  have hstable : (prefixWord ++ tailWord_5706760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5706760).length < 2 ^ (prefixWord ++ tailWord_5706760).sum := by decide
  have hdescent : baseEnd_5706760 < baseStart_5706760 := by decide
  rcases family_descends (prefixWord ++ tailWord_5706760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5706763 : List Nat := [1, 1, 1, 1, 6, 4, 2, 1, 1, 2, 3]
def baseStart_5706763 : Nat := 118140960795 + 5706763 * 2 ^ 59
def prefixEnd_5706763 : Nat := 4983230072969 + 3 ^ 40 * 5706763 * 2
def baseEnd_5706763 : Nat := 2930312400294160997217581

theorem tailTrace_5706763 : CollatzResearch.WordTrace tailWord_5706763 prefixEnd_5706763 2930312400294160997217581 := by
  unfold tailWord_5706763
  simp only [CollatzResearch.WordTrace]
  refine ⟨208142746224379763370652943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138761830816253175580435295 208142746224379763370652943)
  ·
    refine ⟨312214119336569645055979415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208142746224379763370652943 312214119336569645055979415)
    ·
      refine ⟨468321179004854467583969123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312214119336569645055979415 468321179004854467583969123)
      ·
        refine ⟨702481768507281701375953685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 468321179004854467583969123 702481768507281701375953685)
        ·
          refine ⟨32928832898778829751997829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 702481768507281701375953685 32928832898778829751997829)
          ·
            refine ⟨6174156168521030578499593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32928832898778829751997829 6174156168521030578499593)
            ·
              refine ⟨4630617126390772933874695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6174156168521030578499593 4630617126390772933874695)
              ·
                refine ⟨6945925689586159400812043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4630617126390772933874695 6945925689586159400812043)
                ·
                  refine ⟨10418888534379239101218065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6945925689586159400812043 10418888534379239101218065)
                  ·
                    refine ⟨7814166400784429325913549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10418888534379239101218065 7814166400784429325913549)
                    ·
                      refine ⟨2930312400294160997217581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7814166400784429325913549 2930312400294160997217581)
                      ·
                        rfl

theorem cell23_5706763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 2, 1, 1, 2, 3].length) (baseStart_5706763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5706763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5706763 prefixEnd_5706763 := by exact prefixLift 5706763
  have htrace : WordTrace (prefixWord ++ tailWord_5706763) baseStart_5706763 baseEnd_5706763 := by
    simpa [prefixWord, tailWord_5706763, baseEnd_5706763] using wordTrace_append hprefix tailTrace_5706763
  have hstable : (prefixWord ++ tailWord_5706763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5706763).length < 2 ^ (prefixWord ++ tailWord_5706763).sum := by decide
  have hdescent : baseEnd_5706763 < baseStart_5706763 := by decide
  rcases family_descends (prefixWord ++ tailWord_5706763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5706770 : List Nat := [3, 2, 5, 1, 1, 1, 1, 1, 4, 4]
def baseStart_5706770 : Nat := 118140960795 + 5706770 * 2 ^ 59
def prefixEnd_5706770 : Nat := 4983230072969 + 3 ^ 40 * 5706770 * 2
def baseEnd_5706770 : Nat := 976771998219580823276683

theorem tailTrace_5706770 : CollatzResearch.WordTrace tailWord_5706770 prefixEnd_5706770 976771998219580823276683 := by
  unfold tailWord_5706770
  simp only [CollatzResearch.WordTrace]
  refine ⟨52035750383838600891539441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138762001023569602377438509 52035750383838600891539441)
  ·
    refine ⟨39026812787878950668654581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52035750383838600891539441 39026812787878950668654581)
    ·
      refine ⟨3658763698863651625186367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39026812787878950668654581 3658763698863651625186367)
      ·
        refine ⟨5488145548295477437779551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3658763698863651625186367 5488145548295477437779551)
        ·
          refine ⟨8232218322443216156669327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5488145548295477437779551 8232218322443216156669327)
          ·
            refine ⟨12348327483664824235003991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8232218322443216156669327 12348327483664824235003991)
            ·
              refine ⟨18522491225497236352505987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12348327483664824235003991 18522491225497236352505987)
              ·
                refine ⟨27783736838245854528758981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18522491225497236352505987 27783736838245854528758981)
                ·
                  refine ⟨5209450657171097724142309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27783736838245854528758981 5209450657171097724142309)
                  ·
                    refine ⟨976771998219580823276683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5209450657171097724142309 976771998219580823276683)
                    ·
                      rfl

theorem cell23_5706770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_5706770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5706770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5706770 prefixEnd_5706770 := by exact prefixLift 5706770
  have htrace : WordTrace (prefixWord ++ tailWord_5706770) baseStart_5706770 baseEnd_5706770 := by
    simpa [prefixWord, tailWord_5706770, baseEnd_5706770] using wordTrace_append hprefix tailTrace_5706770
  have hstable : (prefixWord ++ tailWord_5706770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5706770).length < 2 ^ (prefixWord ++ tailWord_5706770).sum := by decide
  have hdescent : baseEnd_5706770 < baseStart_5706770 := by decide
  rcases family_descends (prefixWord ++ tailWord_5706770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5706776 : List Nat := [2, 1, 2, 3, 2, 3, 1, 1, 4, 1, 3]
def baseStart_5706776 : Nat := 118140960795 + 5706776 * 2 ^ 59
def prefixEnd_5706776 : Nat := 4983230072969 + 3 ^ 40 * 5706776 * 2
def baseEnd_5706776 : Nat := 2930319075542669446355021

theorem tailTrace_5706776 : CollatzResearch.WordTrace tailWord_5706776 prefixEnd_5706776 2930319075542669446355021 := by
  unfold tailWord_5706776
  simp only [CollatzResearch.WordTrace]
  refine ⟨104071610186666333295438091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138762146915555111060584121 104071610186666333295438091)
  ·
    refine ⟨156107415279999499943157137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104071610186666333295438091 156107415279999499943157137)
    ·
      refine ⟨117080561459999624957367853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156107415279999499943157137 117080561459999624957367853)
      ·
        refine ⟨43905210547499859359012945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117080561459999624957367853 43905210547499859359012945)
        ·
          refine ⟨32928907910624894519259709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43905210547499859359012945 32928907910624894519259709)
          ·
            refine ⟨12348340466484335444722391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32928907910624894519259709 12348340466484335444722391)
            ·
              refine ⟨18522510699726503167083587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12348340466484335444722391 18522510699726503167083587)
              ·
                refine ⟨27783766049589754750625381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18522510699726503167083587 27783766049589754750625381)
                ·
                  refine ⟨5209456134298079015742259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27783766049589754750625381 5209456134298079015742259)
                  ·
                    refine ⟨7814184201447118523613389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5209456134298079015742259 7814184201447118523613389)
                    ·
                      refine ⟨2930319075542669446355021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7814184201447118523613389 2930319075542669446355021)
                      ·
                        rfl

theorem cell23_5706776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 1, 4, 1, 3].length) (baseStart_5706776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5706776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5706776 prefixEnd_5706776 := by exact prefixLift 5706776
  have htrace : WordTrace (prefixWord ++ tailWord_5706776) baseStart_5706776 baseEnd_5706776 := by
    simpa [prefixWord, tailWord_5706776, baseEnd_5706776] using wordTrace_append hprefix tailTrace_5706776
  have hstable : (prefixWord ++ tailWord_5706776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5706776).length < 2 ^ (prefixWord ++ tailWord_5706776).sum := by decide
  have hdescent : baseEnd_5706776 < baseStart_5706776 := by decide
  rcases family_descends (prefixWord ++ tailWord_5706776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5706816 : List Nat := [2, 1, 1, 2, 2, 3, 1, 1, 6, 2, 2]
def baseStart_5706816 : Nat := 118140960795 + 5706816 * 2 ^ 59
def prefixEnd_5706816 : Nat := 4983230072969 + 3 ^ 40 * 5706816 * 2
def baseEnd_5706816 : Nat := 2930339614768849289854837

theorem tailTrace_5706816 : CollatzResearch.WordTrace tailWord_5706816 prefixEnd_5706816 2930339614768849289854837 := by
  unfold tailWord_5706816
  simp only [CollatzResearch.WordTrace]
  refine ⟨104072339646593876711166151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138763119528791835614888201 104072339646593876711166151)
  ·
    refine ⟨156108509469890815066749227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104072339646593876711166151 156108509469890815066749227)
    ·
      refine ⟨234162764204836222600123841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156108509469890815066749227 234162764204836222600123841)
      ·
        refine ⟨175622073153627166950092881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 234162764204836222600123841 175622073153627166950092881)
        ·
          refine ⟨131716554865220375212569661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175622073153627166950092881 131716554865220375212569661)
          ·
            refine ⟨49393708074457640704713623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 131716554865220375212569661 49393708074457640704713623)
            ·
              refine ⟨74090562111686461057070435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49393708074457640704713623 74090562111686461057070435)
              ·
                refine ⟨111135843167529691585605653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74090562111686461057070435 111135843167529691585605653)
                ·
                  refine ⟨5209492648477954293075265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 111135843167529691585605653 5209492648477954293075265)
                  ·
                    refine ⟨3907119486358465719806449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5209492648477954293075265 3907119486358465719806449)
                    ·
                      refine ⟨2930339614768849289854837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3907119486358465719806449 2930339614768849289854837)
                      ·
                        rfl

theorem cell23_5706816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 6, 2, 2].length) (baseStart_5706816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5706816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5706816 prefixEnd_5706816 := by exact prefixLift 5706816
  have htrace : WordTrace (prefixWord ++ tailWord_5706816) baseStart_5706816 baseEnd_5706816 := by
    simpa [prefixWord, tailWord_5706816, baseEnd_5706816] using wordTrace_append hprefix tailTrace_5706816
  have hstable : (prefixWord ++ tailWord_5706816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5706816).length < 2 ^ (prefixWord ++ tailWord_5706816).sum := by decide
  have hdescent : baseEnd_5706816 < baseStart_5706816 := by decide
  rcases family_descends (prefixWord ++ tailWord_5706816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5706842 : List Nat := [3, 1, 1, 2, 1, 1, 2, 1, 2, 1, 8]
def baseStart_5706842 : Nat := 118140960795 + 5706842 * 2 ^ 59
def prefixEnd_5706842 : Nat := 4983230072969 + 3 ^ 40 * 5706842 * 2
def baseEnd_5706842 : Nat := 2930352965265866188129717

theorem tailTrace_5706842 : CollatzResearch.WordTrace tailWord_5706842 prefixEnd_5706842 2930352965265866188129717 := by
  unfold tailWord_5706842
  simp only [CollatzResearch.WordTrace]
  refine ⟨52036406897773389965694695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138763751727395706575185853 52036406897773389965694695)
  ·
    refine ⟨78054610346660084948542043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52036406897773389965694695 78054610346660084948542043)
    ·
      refine ⟨117081915519990127422813065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78054610346660084948542043 117081915519990127422813065)
      ·
        refine ⟨87811436639992595567109799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117081915519990127422813065 87811436639992595567109799)
        ·
          refine ⟨131717154959988893350664699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87811436639992595567109799 131717154959988893350664699)
          ·
            refine ⟨197575732439983340025997049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131717154959988893350664699 197575732439983340025997049)
            ·
              refine ⟨148181799329987505019497787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 197575732439983340025997049 148181799329987505019497787)
              ·
                refine ⟨222272698994981257529246681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 148181799329987505019497787 222272698994981257529246681)
                ·
                  refine ⟨166704524246235943146935011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 222272698994981257529246681 166704524246235943146935011)
                  ·
                    refine ⟨250056786369353914720402517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 166704524246235943146935011 250056786369353914720402517)
                    ·
                      refine ⟨2930352965265866188129717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 250056786369353914720402517 2930352965265866188129717)
                      ·
                        rfl

theorem cell23_5706842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 2, 1, 8].length) (baseStart_5706842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5706842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5706842 prefixEnd_5706842 := by exact prefixLift 5706842
  have htrace : WordTrace (prefixWord ++ tailWord_5706842) baseStart_5706842 baseEnd_5706842 := by
    simpa [prefixWord, tailWord_5706842, baseEnd_5706842] using wordTrace_append hprefix tailTrace_5706842
  have hstable : (prefixWord ++ tailWord_5706842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5706842).length < 2 ^ (prefixWord ++ tailWord_5706842).sum := by decide
  have hdescent : baseEnd_5706842 < baseStart_5706842 := by decide
  rcases family_descends (prefixWord ++ tailWord_5706842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5706849 : List Nat := [1, 2, 3, 1, 1, 2, 2, 3, 2, 3, 3]
def baseStart_5706849 : Nat := 118140960795 + 5706849 * 2 ^ 59
def prefixEnd_5706849 : Nat := 4983230072969 + 3 ^ 40 * 5706849 * 2
def baseEnd_5706849 : Nat := 2930356559630447660742185

theorem tailTrace_5706849 : CollatzResearch.WordTrace tailWord_5706849 prefixEnd_5706849 2930356559630447660742185 := by
  unfold tailWord_5706849
  simp only [CollatzResearch.WordTrace]
  refine ⟨208145882902068200058283601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138763921934712133372189067 208145882902068200058283601)
  ·
    refine ⟨156109412176551150043712701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208145882902068200058283601 156109412176551150043712701)
    ·
      refine ⟨58541029566206681266392263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156109412176551150043712701 58541029566206681266392263)
      ·
        refine ⟨87811544349310021899588395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58541029566206681266392263 87811544349310021899588395)
        ·
          refine ⟨131717316523965032849382593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87811544349310021899588395 131717316523965032849382593)
          ·
            refine ⟨98787987392973774637036945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131717316523965032849382593 98787987392973774637036945)
            ·
              refine ⟨74090990544730330977777709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98787987392973774637036945 74090990544730330977777709)
              ·
                refine ⟨27784121454273874116666641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74090990544730330977777709 27784121454273874116666641)
                ·
                  refine ⟨20838091090705405587499981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27784121454273874116666641 20838091090705405587499981)
                  ·
                    refine ⟨7814284159014527095312493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20838091090705405587499981 7814284159014527095312493)
                    ·
                      refine ⟨2930356559630447660742185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7814284159014527095312493 2930356559630447660742185)
                      ·
                        rfl

theorem cell23_5706849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 3, 2, 3, 3].length) (baseStart_5706849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5706849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5706849 prefixEnd_5706849 := by exact prefixLift 5706849
  have htrace : WordTrace (prefixWord ++ tailWord_5706849) baseStart_5706849 baseEnd_5706849 := by
    simpa [prefixWord, tailWord_5706849, baseEnd_5706849] using wordTrace_append hprefix tailTrace_5706849
  have hstable : (prefixWord ++ tailWord_5706849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5706849).length < 2 ^ (prefixWord ++ tailWord_5706849).sum := by decide
  have hdescent : baseEnd_5706849 < baseStart_5706849 := by decide
  rcases family_descends (prefixWord ++ tailWord_5706849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5706916 : List Nat := [2, 3, 1, 2, 3, 1, 1, 1, 5, 4]
def baseStart_5706916 : Nat := 118140960795 + 5706916 * 2 ^ 59
def prefixEnd_5706916 : Nat := 4983230072969 + 3 ^ 40 * 5706916 * 2
def baseEnd_5706916 : Nat := 976796987611432966201459

theorem tailTrace_5706916 : CollatzResearch.WordTrace tailWord_5706916 prefixEnd_5706916 976796987611432966201459 := by
  unfold tailWord_5706916
  simp only [CollatzResearch.WordTrace]
  refine ⟨104074163296412735250486301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138765551061883647000648401 104074163296412735250486301)
  ·
    refine ⟨39027811236154775718932363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104074163296412735250486301 39027811236154775718932363)
    ·
      refine ⟨58541716854232163578398545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39027811236154775718932363 58541716854232163578398545)
      ·
        refine ⟨43906287640674122683798909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58541716854232163578398545 43906287640674122683798909)
        ·
          refine ⟨16464857865252796006424591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43906287640674122683798909 16464857865252796006424591)
          ·
            refine ⟨24697286797879194009636887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16464857865252796006424591 24697286797879194009636887)
            ·
              refine ⟨37045930196818791014455331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24697286797879194009636887 37045930196818791014455331)
              ·
                refine ⟨55568895295228186521682997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37045930196818791014455331 55568895295228186521682997)
                ·
                  refine ⟨5209583933927642486407781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55568895295228186521682997 5209583933927642486407781)
                  ·
                    refine ⟨976796987611432966201459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5209583933927642486407781 976796987611432966201459)
                    ·
                      rfl

theorem cell23_5706916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 1, 5, 4].length) (baseStart_5706916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5706916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5706916 prefixEnd_5706916 := by exact prefixLift 5706916
  have htrace : WordTrace (prefixWord ++ tailWord_5706916) baseStart_5706916 baseEnd_5706916 := by
    simpa [prefixWord, tailWord_5706916, baseEnd_5706916] using wordTrace_append hprefix tailTrace_5706916
  have hstable : (prefixWord ++ tailWord_5706916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5706916).length < 2 ^ (prefixWord ++ tailWord_5706916).sum := by decide
  have hdescent : baseEnd_5706916 < baseStart_5706916 := by decide
  rcases family_descends (prefixWord ++ tailWord_5706916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5706959 : List Nat := [1, 1, 2, 1, 1, 3, 2, 4, 3, 5]
def baseStart_5706959 : Nat := 118140960795 + 5706959 * 2 ^ 59
def prefixEnd_5706959 : Nat := 4983230072969 + 3 ^ 40 * 5706959 * 2
def baseEnd_5706959 : Nat := 976804347500814076788893

theorem tailTrace_5706959 : CollatzResearch.WordTrace tailWord_5706959 prefixEnd_5706959 976804347500814076788893 := by
  unfold tailWord_5706959
  simp only [CollatzResearch.WordTrace]
  refine ⟨208149894931669688844787931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138766596621113125896525287 208149894931669688844787931)
  ·
    refine ⟨312224842397504533267181897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208149894931669688844787931 312224842397504533267181897)
    ·
      refine ⟨234168631798128399950386423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 312224842397504533267181897 234168631798128399950386423)
      ·
        refine ⟨351252947697192599925579635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234168631798128399950386423 351252947697192599925579635)
        ·
          refine ⟨526879421545788899888369453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 351252947697192599925579635 526879421545788899888369453)
          ·
            refine ⟨197579783079670837458138545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 526879421545788899888369453 197579783079670837458138545)
            ·
              refine ⟨148184837309753128093603909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 197579783079670837458138545 148184837309753128093603909)
              ·
                refine ⟨27784656995578711517550733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 148184837309753128093603909 27784656995578711517550733)
                ·
                  refine ⟨10419246373342016819081525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27784656995578711517550733 10419246373342016819081525)
                  ·
                    refine ⟨976804347500814076788893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10419246373342016819081525 976804347500814076788893)
                    ·
                      rfl

theorem cell23_5706959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 4, 3, 5].length) (baseStart_5706959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5706959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5706959 prefixEnd_5706959 := by exact prefixLift 5706959
  have htrace : WordTrace (prefixWord ++ tailWord_5706959) baseStart_5706959 baseEnd_5706959 := by
    simpa [prefixWord, tailWord_5706959, baseEnd_5706959] using wordTrace_append hprefix tailTrace_5706959
  have hstable : (prefixWord ++ tailWord_5706959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5706959).length < 2 ^ (prefixWord ++ tailWord_5706959).sum := by decide
  have hdescent : baseEnd_5706959 < baseStart_5706959 := by decide
  rcases family_descends (prefixWord ++ tailWord_5706959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5706976 : List Nat := [2, 1, 1, 3, 1, 4, 1, 4, 1, 5]
def baseStart_5706976 : Nat := 118140960795 + 5706976 * 2 ^ 59
def prefixEnd_5706976 : Nat := 4983230072969 + 3 ^ 40 * 5706976 * 2
def baseEnd_5706976 : Nat := 976807257224522887951367

theorem tailTrace_5706976 : CollatzResearch.WordTrace tailWord_5706976 prefixEnd_5706976 976807257224522887951367 := by
  unfold tailWord_5706976
  simp only [CollatzResearch.WordTrace]
  refine ⟨104075257486304050374078391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138767009981738733832104521 104075257486304050374078391)
  ·
    refine ⟨156112886229456075561117587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104075257486304050374078391 156112886229456075561117587)
    ·
      refine ⟨234169329344184113341676381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156112886229456075561117587 234169329344184113341676381)
      ·
        refine ⟨87813498504069042503128643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 234169329344184113341676381 87813498504069042503128643)
        ·
          refine ⟨131720247756103563754692965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87813498504069042503128643 131720247756103563754692965)
          ·
            refine ⟨24697546454269418204004931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 131720247756103563754692965 24697546454269418204004931)
            ·
              refine ⟨37046319681404127306007397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24697546454269418204004931 37046319681404127306007397)
              ·
                refine ⟨6946184940263273869876387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37046319681404127306007397 6946184940263273869876387)
                ·
                  refine ⟨10419277410394910804814581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6946184940263273869876387 10419277410394910804814581)
                  ·
                    refine ⟨976807257224522887951367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10419277410394910804814581 976807257224522887951367)
                    ·
                      rfl

theorem cell23_5706976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 4, 1, 5].length) (baseStart_5706976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5706976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5706976 prefixEnd_5706976 := by exact prefixLift 5706976
  have htrace : WordTrace (prefixWord ++ tailWord_5706976) baseStart_5706976 baseEnd_5706976 := by
    simpa [prefixWord, tailWord_5706976, baseEnd_5706976] using wordTrace_append hprefix tailTrace_5706976
  have hstable : (prefixWord ++ tailWord_5706976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5706976).length < 2 ^ (prefixWord ++ tailWord_5706976).sum := by decide
  have hdescent : baseEnd_5706976 < baseStart_5706976 := by decide
  rcases family_descends (prefixWord ++ tailWord_5706976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5706999 : List Nat := [1, 1, 3, 1, 1, 1, 2, 2, 5, 1, 5]
def baseStart_5706999 : Nat := 118140960795 + 5706999 * 2 ^ 59
def prefixEnd_5706999 : Nat := 4983230072969 + 3 ^ 40 * 5706999 * 2
def baseEnd_5706999 : Nat := 2930433581728622073866495

theorem tailTrace_5706999 : CollatzResearch.WordTrace tailWord_5706999 prefixEnd_5706999 2930433581728622073866495 := by
  unfold tailWord_5706999
  simp only [CollatzResearch.WordTrace]
  refine ⟨208151353851524775676244051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138767569234349850450829367 208151353851524775676244051)
  ·
    refine ⟨312227030777287163514366077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208151353851524775676244051 312227030777287163514366077)
    ·
      refine ⟨117085136541482686317887279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 312227030777287163514366077 117085136541482686317887279)
      ·
        refine ⟨175627704812224029476830919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117085136541482686317887279 175627704812224029476830919)
        ·
          refine ⟨263441557218336044215246379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175627704812224029476830919 263441557218336044215246379)
          ·
            refine ⟨395162335827504066322869569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 263441557218336044215246379 395162335827504066322869569)
            ·
              refine ⟨296371751870628049742152177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 395162335827504066322869569 296371751870628049742152177)
              ·
                refine ⟨222278813902971037306614133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 296371751870628049742152177 222278813902971037306614133)
                ·
                  refine ⟨20838638803403534747495075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 222278813902971037306614133 20838638803403534747495075)
                  ·
                    refine ⟨31257958205105302121242613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20838638803403534747495075 31257958205105302121242613)
                    ·
                      refine ⟨2930433581728622073866495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31257958205105302121242613 2930433581728622073866495)
                      ·
                        rfl

theorem cell23_5706999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 5, 1, 5].length) (baseStart_5706999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5706999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5706999 prefixEnd_5706999 := by exact prefixLift 5706999
  have htrace : WordTrace (prefixWord ++ tailWord_5706999) baseStart_5706999 baseEnd_5706999 := by
    simpa [prefixWord, tailWord_5706999, baseEnd_5706999] using wordTrace_append hprefix tailTrace_5706999
  have hstable : (prefixWord ++ tailWord_5706999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5706999).length < 2 ^ (prefixWord ++ tailWord_5706999).sum := by decide
  have hdescent : baseEnd_5706999 < baseStart_5706999 := by decide
  rcases family_descends (prefixWord ++ tailWord_5706999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5707007 : List Nat := [1, 1, 2, 2, 1, 6, 3, 2, 1, 1, 3]
def baseStart_5707007 : Nat := 118140960795 + 5707007 * 2 ^ 59
def prefixEnd_5707007 : Nat := 4983230072969 + 3 ^ 40 * 5707007 * 2
def baseEnd_5707007 : Nat := 2930437689573858042566459

theorem tailTrace_5707007 : CollatzResearch.WordTrace tailWord_5707007 prefixEnd_5707007 2930437689573858042566459 := by
  unfold tailWord_5707007
  simp only [CollatzResearch.WordTrace]
  refine ⟨208151645635495793042535275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138767763756997195361690183 208151645635495793042535275)
  ·
    refine ⟨312227468453243689563802913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208151645635495793042535275 312227468453243689563802913)
    ·
      refine ⟨234170601339932767172852185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 312227468453243689563802913 234170601339932767172852185)
      ·
        refine ⟨175627951004949575379639139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 234170601339932767172852185 175627951004949575379639139)
        ·
          refine ⟨263441926507424363069458709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175627951004949575379639139 263441926507424363069458709)
          ·
            refine ⟨12348840305035517018880877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 263441926507424363069458709 12348840305035517018880877)
            ·
              refine ⟨4630815114388318882080329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12348840305035517018880877 4630815114388318882080329)
              ·
                refine ⟨3473111335791239161560247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4630815114388318882080329 3473111335791239161560247)
                ·
                  refine ⟨5209667003686858742340371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3473111335791239161560247 5209667003686858742340371)
                  ·
                    refine ⟨7814500505530288113510557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5209667003686858742340371 7814500505530288113510557)
                    ·
                      refine ⟨2930437689573858042566459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7814500505530288113510557 2930437689573858042566459)
                      ·
                        rfl

theorem cell23_5707007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 3, 2, 1, 1, 3].length) (baseStart_5707007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5707007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5707007 prefixEnd_5707007 := by exact prefixLift 5707007
  have htrace : WordTrace (prefixWord ++ tailWord_5707007) baseStart_5707007 baseEnd_5707007 := by
    simpa [prefixWord, tailWord_5707007, baseEnd_5707007] using wordTrace_append hprefix tailTrace_5707007
  have hstable : (prefixWord ++ tailWord_5707007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5707007).length < 2 ^ (prefixWord ++ tailWord_5707007).sum := by decide
  have hdescent : baseEnd_5707007 < baseStart_5707007 := by decide
  rcases family_descends (prefixWord ++ tailWord_5707007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5707019 : List Nat := [1, 1, 1, 1, 5, 3, 1, 10]
def baseStart_5707019 : Nat := 118140960795 + 5707019 * 2 ^ 59
def prefixEnd_5707019 : Nat := 4983230072969 + 3 ^ 40 * 5707019 * 2
def baseEnd_5707019 : Nat := 108534957457100444282089

theorem tailTrace_5707019 : CollatzResearch.WordTrace tailWord_5707019 prefixEnd_5707019 108534957457100444282089 := by
  unfold tailWord_5707019
  simp only [CollatzResearch.WordTrace]
  refine ⟨208152083311452319091972111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138768055540968212727981407 208152083311452319091972111)
  ·
    refine ⟨312228124967178478637958167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208152083311452319091972111 312228124967178478637958167)
    ·
      refine ⟨468342187450767717956937251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312228124967178478637958167 468342187450767717956937251)
      ·
        refine ⟨702513281176151576935405877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 468342187450767717956937251 702513281176151576935405877)
        ·
          refine ⟨65860620110264210337694301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 702513281176151576935405877 65860620110264210337694301)
          ·
            refine ⟨24697732541349078876635363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65860620110264210337694301 24697732541349078876635363)
            ·
              refine ⟨37046598812023618314953045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24697732541349078876635363 37046598812023618314953045)
              ·
                refine ⟨108534957457100444282089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 37046598812023618314953045 108534957457100444282089)
                ·
                  rfl

theorem cell23_5707019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 10].length) (baseStart_5707019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5707019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5707019 prefixEnd_5707019 := by exact prefixLift 5707019
  have htrace : WordTrace (prefixWord ++ tailWord_5707019) baseStart_5707019 baseEnd_5707019 := by
    simpa [prefixWord, tailWord_5707019, baseEnd_5707019] using wordTrace_append hprefix tailTrace_5707019
  have hstable : (prefixWord ++ tailWord_5707019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5707019).length < 2 ^ (prefixWord ++ tailWord_5707019).sum := by decide
  have hdescent : baseEnd_5707019 < baseStart_5707019 := by decide
  rcases family_descends (prefixWord ++ tailWord_5707019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5707050 : List Nat := [3, 1, 4, 2, 1, 3, 1, 1, 1, 1, 5]
def baseStart_5707050 : Nat := 118140960795 + 5707050 * 2 ^ 59
def prefixEnd_5707050 : Nat := 4983230072969 + 3 ^ 40 * 5707050 * 2
def baseEnd_5707050 : Nat := 2930459769242001374328761

theorem tailTrace_5707050 : CollatzResearch.WordTrace tailWord_5707050 prefixEnd_5707050 2930459769242001374328761 := by
  unfold tailWord_5707050
  simp only [CollatzResearch.WordTrace]
  refine ⟨52038303493585002846587651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138768809316226674257567069 52038303493585002846587651)
  ·
    refine ⟨78057455240377504269881477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52038303493585002846587651 78057455240377504269881477)
    ·
      refine ⟨14635772857570782050602777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78057455240377504269881477 14635772857570782050602777)
      ·
        refine ⟨10976829643178086537952083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14635772857570782050602777 10976829643178086537952083)
        ·
          refine ⟨16465244464767129806928125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10976829643178086537952083 16465244464767129806928125)
          ·
            refine ⟨6174466674287673677598047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16465244464767129806928125 6174466674287673677598047)
            ·
              refine ⟨9261700011431510516397071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6174466674287673677598047 9261700011431510516397071)
              ·
                refine ⟨13892550017147265774595607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9261700011431510516397071 13892550017147265774595607)
                ·
                  refine ⟨20838825025720898661893411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13892550017147265774595607 20838825025720898661893411)
                  ·
                    refine ⟨31258237538581347992840117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20838825025720898661893411 31258237538581347992840117)
                    ·
                      refine ⟨2930459769242001374328761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31258237538581347992840117 2930459769242001374328761)
                      ·
                        rfl

theorem cell23_5707050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_5707050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5707050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5707050 prefixEnd_5707050 := by exact prefixLift 5707050
  have htrace : WordTrace (prefixWord ++ tailWord_5707050) baseStart_5707050 baseEnd_5707050 := by
    simpa [prefixWord, tailWord_5707050, baseEnd_5707050] using wordTrace_append hprefix tailTrace_5707050
  have hstable : (prefixWord ++ tailWord_5707050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5707050).length < 2 ^ (prefixWord ++ tailWord_5707050).sum := by decide
  have hdescent : baseEnd_5707050 < baseStart_5707050 := by decide
  rcases family_descends (prefixWord ++ tailWord_5707050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5707086 : List Nat := [4, 1, 1, 1, 1, 1, 3, 2, 2, 3, 4]
def baseStart_5707086 : Nat := 118140960795 + 5707086 * 2 ^ 59
def prefixEnd_5707086 : Nat := 4983230072969 + 3 ^ 40 * 5707086 * 2
def baseEnd_5707086 : Nat := 2930478254545563233478595

theorem tailTrace_5707086 : CollatzResearch.WordTrace tailWord_5707086 prefixEnd_5707086 2930478254545563233478595 := by
  unfold tailWord_5707086
  simp only [CollatzResearch.WordTrace]
  refine ⟨26019315875276198691832639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138769684668139726356440741 26019315875276198691832639)
  ·
    refine ⟨39028973812914298037748959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26019315875276198691832639 39028973812914298037748959)
    ·
      refine ⟨58543460719371447056623439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39028973812914298037748959 58543460719371447056623439)
      ·
        refine ⟨87815191079057170584935159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58543460719371447056623439 87815191079057170584935159)
        ·
          refine ⟨131722786618585755877402739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87815191079057170584935159 131722786618585755877402739)
          ·
            refine ⟨197584179927878633816104109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131722786618585755877402739 197584179927878633816104109)
            ·
              refine ⟨74094067472954487681039041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 197584179927878633816104109 74094067472954487681039041)
              ·
                refine ⟨55570550604715865760779281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74094067472954487681039041 55570550604715865760779281)
                ·
                  refine ⟨41677912953536899320584461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55570550604715865760779281 41677912953536899320584461)
                  ·
                    refine ⟨15629217357576337245219173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41677912953536899320584461 15629217357576337245219173)
                    ·
                      refine ⟨2930478254545563233478595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15629217357576337245219173 2930478254545563233478595)
                      ·
                        rfl

theorem cell23_5707086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 2, 2, 3, 4].length) (baseStart_5707086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5707086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5707086 prefixEnd_5707086 := by exact prefixLift 5707086
  have htrace : WordTrace (prefixWord ++ tailWord_5707086) baseStart_5707086 baseEnd_5707086 := by
    simpa [prefixWord, tailWord_5707086, baseEnd_5707086] using wordTrace_append hprefix tailTrace_5707086
  have hstable : (prefixWord ++ tailWord_5707086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5707086).length < 2 ^ (prefixWord ++ tailWord_5707086).sum := by decide
  have hdescent : baseEnd_5707086 < baseStart_5707086 := by decide
  rcases family_descends (prefixWord ++ tailWord_5707086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5707090 : List Nat := [3, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2]
def baseStart_5707090 : Nat := 118140960795 + 5707090 * 2 ^ 59
def prefixEnd_5707090 : Nat := 4983230072969 + 3 ^ 40 * 5707090 * 2
def baseEnd_5707090 : Nat := 2930480308468181217828577

theorem tailTrace_5707090 : CollatzResearch.WordTrace tailWord_5707090 prefixEnd_5707090 2930480308468181217828577 := by
  unfold tailWord_5707090
  simp only [CollatzResearch.WordTrace]
  refine ⟨52038668223548774554451681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138769781929463398811871149 52038668223548774554451681)
  ·
    refine ⟨39029001167661580915838761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52038668223548774554451681 39029001167661580915838761)
    ·
      refine ⟨29271750875746185686879071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39029001167661580915838761 29271750875746185686879071)
      ·
        refine ⟨43907626313619278530318607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29271750875746185686879071 43907626313619278530318607)
        ·
          refine ⟨65861439470428917795477911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43907626313619278530318607 65861439470428917795477911)
          ·
            refine ⟨98792159205643376693216867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65861439470428917795477911 98792159205643376693216867)
            ·
              refine ⟨148188238808465065039825301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98792159205643376693216867 148188238808465065039825301)
              ·
                refine ⟨6946323694146799923741811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 148188238808465065039825301 6946323694146799923741811)
                ·
                  refine ⟨10419485541220199885612717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6946323694146799923741811 10419485541220199885612717)
                  ·
                    refine ⟨3907307077957574957104769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10419485541220199885612717 3907307077957574957104769)
                    ·
                      refine ⟨2930480308468181217828577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3907307077957574957104769 2930480308468181217828577)
                      ·
                        rfl

theorem cell23_5707090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2].length) (baseStart_5707090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5707090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5707090 prefixEnd_5707090 := by exact prefixLift 5707090
  have htrace : WordTrace (prefixWord ++ tailWord_5707090) baseStart_5707090 baseEnd_5707090 := by
    simpa [prefixWord, tailWord_5707090, baseEnd_5707090] using wordTrace_append hprefix tailTrace_5707090
  have hstable : (prefixWord ++ tailWord_5707090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5707090).length < 2 ^ (prefixWord ++ tailWord_5707090).sum := by decide
  have hdescent : baseEnd_5707090 < baseStart_5707090 := by decide
  rcases family_descends (prefixWord ++ tailWord_5707090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5707107 : List Nat := [1, 1, 1, 5, 2, 2, 4, 1, 1, 3, 2]
def baseStart_5707107 : Nat := 118140960795 + 5707107 * 2 ^ 59
def prefixEnd_5707107 : Nat := 4983230072969 + 3 ^ 40 * 5707107 * 2
def baseEnd_5707107 : Nat := 2930489037639307651315999

theorem tailTrace_5707107 : CollatzResearch.WordTrace tailWord_5707107 prefixEnd_5707107 2930489037639307651315999 := by
  unfold tailWord_5707107
  simp only [CollatzResearch.WordTrace]
  refine ⟨208155292935133510121175575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138770195290089006747450383 208155292935133510121175575)
  ·
    refine ⟨312232939402700265181763363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208155292935133510121175575 312232939402700265181763363)
    ·
      refine ⟨468349409104050397772645045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312232939402700265181763363 468349409104050397772645045)
      ·
        refine ⟨43907757103504724791185473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 468349409104050397772645045 43907757103504724791185473)
        ·
          refine ⟨32930817827628543593389105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43907757103504724791185473 32930817827628543593389105)
          ·
            refine ⟨24698113370721407695041829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32930817827628543593389105 24698113370721407695041829)
            ·
              refine ⟨4630896257010263942820343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24698113370721407695041829 4630896257010263942820343)
              ·
                refine ⟨6946344385515395914230515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4630896257010263942820343 6946344385515395914230515)
                ·
                  refine ⟨10419516578273093871345773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6946344385515395914230515 10419516578273093871345773)
                  ·
                    refine ⟨3907318716852410201754665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10419516578273093871345773 3907318716852410201754665)
                    ·
                      refine ⟨2930489037639307651315999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3907318716852410201754665 2930489037639307651315999)
                      ·
                        rfl

theorem cell23_5707107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 4, 1, 1, 3, 2].length) (baseStart_5707107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5707107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5707107 prefixEnd_5707107 := by exact prefixLift 5707107
  have htrace : WordTrace (prefixWord ++ tailWord_5707107) baseStart_5707107 baseEnd_5707107 := by
    simpa [prefixWord, tailWord_5707107, baseEnd_5707107] using wordTrace_append hprefix tailTrace_5707107
  have hstable : (prefixWord ++ tailWord_5707107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5707107).length < 2 ^ (prefixWord ++ tailWord_5707107).sum := by decide
  have hdescent : baseEnd_5707107 < baseStart_5707107 := by decide
  rcases family_descends (prefixWord ++ tailWord_5707107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5707114 : List Nat := [3, 1, 3, 3, 2, 2, 1, 2, 2, 1, 3]
def baseStart_5707114 : Nat := 118140960795 + 5707114 * 2 ^ 59
def prefixEnd_5707114 : Nat := 4983230072969 + 3 ^ 40 * 5707114 * 2
def baseEnd_5707114 : Nat := 2930492632003889123928467

theorem tailTrace_5707114 : CollatzResearch.WordTrace tailWord_5707114 prefixEnd_5707114 2930492632003889123928467 := by
  unfold tailWord_5707114
  simp only [CollatzResearch.WordTrace]
  refine ⟨52038887061527037579170099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138770365497405433544453597 52038887061527037579170099)
  ·
    refine ⟨78058330592290556368755149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52038887061527037579170099 78058330592290556368755149)
    ·
      refine ⟨29271873972108958638283181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78058330592290556368755149 29271873972108958638283181)
      ·
        refine ⟨10976952739540859489356193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29271873972108958638283181 10976952739540859489356193)
        ·
          refine ⟨8232714554655644617017145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10976952739540859489356193 8232714554655644617017145)
          ·
            refine ⟨6174535915991733462762859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8232714554655644617017145 6174535915991733462762859)
            ·
              refine ⟨9261803873987600194144289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6174535915991733462762859 9261803873987600194144289)
              ·
                refine ⟨6946352905490700145608217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9261803873987600194144289 6946352905490700145608217)
                ·
                  refine ⟨5209764679118025109206163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6946352905490700145608217 5209764679118025109206163)
                  ·
                    refine ⟨7814647018677037663809245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5209764679118025109206163 7814647018677037663809245)
                    ·
                      refine ⟨2930492632003889123928467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7814647018677037663809245 2930492632003889123928467)
                      ·
                        rfl

theorem cell23_5707114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_5707114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5707114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5707114 prefixEnd_5707114 := by exact prefixLift 5707114
  have htrace : WordTrace (prefixWord ++ tailWord_5707114) baseStart_5707114 baseEnd_5707114 := by
    simpa [prefixWord, tailWord_5707114, baseEnd_5707114] using wordTrace_append hprefix tailTrace_5707114
  have hstable : (prefixWord ++ tailWord_5707114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5707114).length < 2 ^ (prefixWord ++ tailWord_5707114).sum := by decide
  have hdescent : baseEnd_5707114 < baseStart_5707114 := by decide
  rcases family_descends (prefixWord ++ tailWord_5707114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5707120 : List Nat := [2, 1, 1, 1, 4, 2, 3, 1, 4, 2, 2]
def baseStart_5707120 : Nat := 118140960795 + 5707120 * 2 ^ 59
def prefixEnd_5707120 : Nat := 4983230072969 + 3 ^ 40 * 5707120 * 2
def baseEnd_5707120 : Nat := 2930495712887816100453439

theorem tailTrace_5707120 : CollatzResearch.WordTrace tailWord_5707120 prefixEnd_5707120 2930495712887816100453439 := by
  unfold tailWord_5707120
  simp only [CollatzResearch.WordTrace]
  refine ⟨104077883542043206670699407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138770511389390942227599209 104077883542043206670699407)
  ·
    refine ⟨156116825313064810006049111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104077883542043206670699407 156116825313064810006049111)
    ·
      refine ⟨234175237969597215009073667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156116825313064810006049111 234175237969597215009073667)
      ·
        refine ⟨351262856954395822513610501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234175237969597215009073667 351262856954395822513610501)
        ·
          refine ⟨65861785678949216721301969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 351262856954395822513610501 65861785678949216721301969)
          ·
            refine ⟨49396339259211912540976477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65861785678949216721301969 49396339259211912540976477)
            ·
              refine ⟨18523627222204467202866179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49396339259211912540976477 18523627222204467202866179)
              ·
                refine ⟨27785440833306700804299269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18523627222204467202866179 27785440833306700804299269)
                ·
                  refine ⟨5209770156245006400806113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27785440833306700804299269 5209770156245006400806113)
                  ·
                    refine ⟨3907327617183754800604585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5209770156245006400806113 3907327617183754800604585)
                    ·
                      refine ⟨2930495712887816100453439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3907327617183754800604585 2930495712887816100453439)
                      ·
                        rfl

theorem cell23_5707120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 1, 4, 2, 2].length) (baseStart_5707120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5707120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5707120 prefixEnd_5707120 := by exact prefixLift 5707120
  have htrace : WordTrace (prefixWord ++ tailWord_5707120) baseStart_5707120 baseEnd_5707120 := by
    simpa [prefixWord, tailWord_5707120, baseEnd_5707120] using wordTrace_append hprefix tailTrace_5707120
  have hstable : (prefixWord ++ tailWord_5707120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5707120).length < 2 ^ (prefixWord ++ tailWord_5707120).sum := by decide
  have hdescent : baseEnd_5707120 < baseStart_5707120 := by decide
  rcases family_descends (prefixWord ++ tailWord_5707120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5707186 : List Nat := [3, 2, 1, 1, 1, 1, 2, 2, 2, 8]
def baseStart_5707186 : Nat := 118140960795 + 5707186 * 2 ^ 59
def prefixEnd_5707186 : Nat := 4983230072969 + 3 ^ 40 * 5707186 * 2
def baseEnd_5707186 : Nat := 976843200870337614076045

theorem tailTrace_5707186 : CollatzResearch.WordTrace tailWord_5707186 prefixEnd_5707186 976843200870337614076045 := by
  unfold tailWord_5707186
  simp only [CollatzResearch.WordTrace]
  refine ⟨52039543575461826653325353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138772116201231537742200941 52039543575461826653325353)
  ·
    refine ⟨39029657681596369989994015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52039543575461826653325353 39029657681596369989994015)
    ·
      refine ⟨58544486522394554984991023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39029657681596369989994015 58544486522394554984991023)
      ·
        refine ⟨87816729783591832477486535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58544486522394554984991023 87816729783591832477486535)
        ·
          refine ⟨131725094675387748716229803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87816729783591832477486535 131725094675387748716229803)
          ·
            refine ⟨197587642013081623074344705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131725094675387748716229803 197587642013081623074344705)
            ·
              refine ⟨148190731509811217305758529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 197587642013081623074344705 148190731509811217305758529)
              ·
                refine ⟨111143048632358412979318897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 148190731509811217305758529 111143048632358412979318897)
                ·
                  refine ⟨83357286474268809734489173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 111143048632358412979318897 83357286474268809734489173)
                  ·
                    refine ⟨976843200870337614076045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 83357286474268809734489173 976843200870337614076045)
                    ·
                      rfl

theorem cell23_5707186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 2, 8].length) (baseStart_5707186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5707186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5707186 prefixEnd_5707186 := by exact prefixLift 5707186
  have htrace : WordTrace (prefixWord ++ tailWord_5707186) baseStart_5707186 baseEnd_5707186 := by
    simpa [prefixWord, tailWord_5707186, baseEnd_5707186] using wordTrace_append hprefix tailTrace_5707186
  have hstable : (prefixWord ++ tailWord_5707186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5707186).length < 2 ^ (prefixWord ++ tailWord_5707186).sum := by decide
  have hdescent : baseEnd_5707186 < baseStart_5707186 := by decide
  rcases family_descends (prefixWord ++ tailWord_5707186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5707203 : List Nat := [1, 1, 1, 3, 1, 1, 4, 4, 3, 4]
def baseStart_5707203 : Nat := 118140960795 + 5707203 * 2 ^ 59
def prefixEnd_5707203 : Nat := 4983230072969 + 3 ^ 40 * 5707203 * 2
def baseEnd_5707203 : Nat := 976846110594046425238519

theorem tailTrace_5707203 : CollatzResearch.WordTrace tailWord_5707203 prefixEnd_5707203 976846110594046425238519 := by
  unfold tailWord_5707203
  simp only [CollatzResearch.WordTrace]
  refine ⟨208158794342785718516670263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138772529561857145677780175 208158794342785718516670263)
  ·
    refine ⟨312238191514178577775005395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208158794342785718516670263 312238191514178577775005395)
    ·
      refine ⟨468357287271267866662508093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312238191514178577775005395 468357287271267866662508093)
      ·
        refine ⟨175633982726725449998440535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 468357287271267866662508093 175633982726725449998440535)
        ·
          refine ⟨263450974090088174997660803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175633982726725449998440535 263450974090088174997660803)
          ·
            refine ⟨395176461135132262496491205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 263450974090088174997660803 395176461135132262496491205)
            ·
              refine ⟨74095586462837299218092101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 395176461135132262496491205 74095586462837299218092101)
              ·
                refine ⟨13892922461781993603392269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74095586462837299218092101 13892922461781993603392269)
                ·
                  refine ⟨5209845923168247601272101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13892922461781993603392269 5209845923168247601272101)
                  ·
                    refine ⟨976846110594046425238519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5209845923168247601272101 976846110594046425238519)
                    ·
                      rfl

theorem cell23_5707203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 4, 3, 4].length) (baseStart_5707203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5707203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5707203 prefixEnd_5707203 := by exact prefixLift 5707203
  have htrace : WordTrace (prefixWord ++ tailWord_5707203) baseStart_5707203 baseEnd_5707203 := by
    simpa [prefixWord, tailWord_5707203, baseEnd_5707203] using wordTrace_append hprefix tailTrace_5707203
  have hstable : (prefixWord ++ tailWord_5707203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5707203).length < 2 ^ (prefixWord ++ tailWord_5707203).sum := by decide
  have hdescent : baseEnd_5707203 < baseStart_5707203 := by decide
  rcases family_descends (prefixWord ++ tailWord_5707203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5707210 : List Nat := [3, 1, 2, 1, 2, 4, 2, 1, 2, 1, 4]
def baseStart_5707210 : Nat := 118140960795 + 5707210 * 2 ^ 59
def prefixEnd_5707210 : Nat := 4983230072969 + 3 ^ 40 * 5707210 * 2
def baseEnd_5707210 : Nat := 2930541926146720748328025

theorem tailTrace_5707210 : CollatzResearch.WordTrace tailWord_5707210 prefixEnd_5707210 2930541926146720748328025 := by
  unfold tailWord_5707210
  simp only [CollatzResearch.WordTrace]
  refine ⟨52039762413440089678043771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138772699769173572474783389 52039762413440089678043771)
  ·
    refine ⟨78059643620160134517065657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52039762413440089678043771 78059643620160134517065657)
    ·
      refine ⟨58544732715120100887799243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78059643620160134517065657 58544732715120100887799243)
      ·
        refine ⟨87817099072680151331698865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58544732715120100887799243 87817099072680151331698865)
        ·
          refine ⟨65862824304510113498774149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87817099072680151331698865 65862824304510113498774149)
          ·
            refine ⟨12349279557095646281020153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65862824304510113498774149 12349279557095646281020153)
            ·
              refine ⟨9261959667821734710765115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12349279557095646281020153 9261959667821734710765115)
              ·
                refine ⟨13892939501732602066147673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9261959667821734710765115 13892939501732602066147673)
                ·
                  refine ⟨10419704626299451549610755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13892939501732602066147673 10419704626299451549610755)
                  ·
                    refine ⟨15629556939449177324416133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10419704626299451549610755 15629556939449177324416133)
                    ·
                      refine ⟨2930541926146720748328025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15629556939449177324416133 2930541926146720748328025)
                      ·
                        rfl

theorem cell23_5707210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 1, 2, 1, 4].length) (baseStart_5707210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5707210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5707210 prefixEnd_5707210 := by exact prefixLift 5707210
  have htrace : WordTrace (prefixWord ++ tailWord_5707210) baseStart_5707210 baseEnd_5707210 := by
    simpa [prefixWord, tailWord_5707210, baseEnd_5707210] using wordTrace_append hprefix tailTrace_5707210
  have hstable : (prefixWord ++ tailWord_5707210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5707210).length < 2 ^ (prefixWord ++ tailWord_5707210).sum := by decide
  have hdescent : baseEnd_5707210 < baseStart_5707210 := by decide
  rcases family_descends (prefixWord ++ tailWord_5707210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5707233 : List Nat := [1, 2, 3, 1, 2, 3, 1, 4, 6]
def baseStart_5707233 : Nat := 118140960795 + 5707233 * 2 ^ 59
def prefixEnd_5707233 : Nat := 4983230072969 + 3 ^ 40 * 5707233 * 2
def baseEnd_5707233 : Nat := 325617081800197128704491

theorem tailTrace_5707233 : CollatzResearch.WordTrace tailWord_5707233 prefixEnd_5707233 325617081800197128704491 := by
  unfold tailWord_5707233
  simp only [CollatzResearch.WordTrace]
  refine ⟨208159888532677033640262353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138773259021784689093508235 208159888532677033640262353)
  ·
    refine ⟨156119916399507775230196765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208159888532677033640262353 156119916399507775230196765)
    ·
      refine ⟨58544968649815415711323787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156119916399507775230196765 58544968649815415711323787)
      ·
        refine ⟨87817452974723123566985681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58544968649815415711323787 87817452974723123566985681)
        ·
          refine ⟨65863089731042342675239261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87817452974723123566985681 65863089731042342675239261)
          ·
            refine ⟨24698658649140878503214723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65863089731042342675239261 24698658649140878503214723)
            ·
              refine ⟨37047987973711317754822085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24698658649140878503214723 37047987973711317754822085)
              ·
                refine ⟨6946497745070872079029141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37047987973711317754822085 6946497745070872079029141)
                ·
                  refine ⟨325617081800197128704491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6946497745070872079029141 325617081800197128704491)
                  ·
                    rfl

theorem cell23_5707233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 4, 6].length) (baseStart_5707233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5707233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5707233 prefixEnd_5707233 := by exact prefixLift 5707233
  have htrace : WordTrace (prefixWord ++ tailWord_5707233) baseStart_5707233 baseEnd_5707233 := by
    simpa [prefixWord, tailWord_5707233, baseEnd_5707233] using wordTrace_append hprefix tailTrace_5707233
  have hstable : (prefixWord ++ tailWord_5707233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5707233).length < 2 ^ (prefixWord ++ tailWord_5707233).sum := by decide
  have hdescent : baseEnd_5707233 < baseStart_5707233 := by decide
  rcases family_descends (prefixWord ++ tailWord_5707233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5707250 : List Nat := [3, 2, 1, 4, 1, 1, 2, 3, 6]
def baseStart_5707250 : Nat := 118140960795 + 5707250 * 2 ^ 59
def prefixEnd_5707250 : Nat := 4983230072969 + 3 ^ 40 * 5707250 * 2
def baseEnd_5707250 : Nat := 325618051708100065758649

theorem tailTrace_5707250 : CollatzResearch.WordTrace tailWord_5707250 prefixEnd_5707250 325618051708100065758649 := by
  unfold tailWord_5707250
  simp only [CollatzResearch.WordTrace]
  refine ⟨52040127143403861385907801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138773672382410297029087469 52040127143403861385907801)
  ·
    refine ⟨39030095357552896039430851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52040127143403861385907801 39030095357552896039430851)
    ·
      refine ⟨58545143036329344059146277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39030095357552896039430851 58545143036329344059146277)
      ·
        refine ⟨10977214319311752011089927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58545143036329344059146277 10977214319311752011089927)
        ·
          refine ⟨16465821478967628016634891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10977214319311752011089927 16465821478967628016634891)
          ·
            refine ⟨24698732218451442024952337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16465821478967628016634891 24698732218451442024952337)
            ·
              refine ⟨18524049163838581518714253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24698732218451442024952337 18524049163838581518714253)
              ·
                refine ⟨6946518436439468069517845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18524049163838581518714253 6946518436439468069517845)
                ·
                  refine ⟨325618051708100065758649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6946518436439468069517845 325618051708100065758649)
                  ·
                    rfl

theorem cell23_5707250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 3, 6].length) (baseStart_5707250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5707250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5707250 prefixEnd_5707250 := by exact prefixLift 5707250
  have htrace : WordTrace (prefixWord ++ tailWord_5707250) baseStart_5707250 baseEnd_5707250 := by
    simpa [prefixWord, tailWord_5707250, baseEnd_5707250] using wordTrace_append hprefix tailTrace_5707250
  have hstable : (prefixWord ++ tailWord_5707250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5707250).length < 2 ^ (prefixWord ++ tailWord_5707250).sum := by decide
  have hdescent : baseEnd_5707250 < baseStart_5707250 := by decide
  rcases family_descends (prefixWord ++ tailWord_5707250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5707260 : List Nat := [2, 2, 2, 1, 2, 1, 3, 1, 5, 1, 3]
def baseStart_5707260 : Nat := 118140960795 + 5707260 * 2 ^ 59
def prefixEnd_5707260 : Nat := 4983230072969 + 3 ^ 40 * 5707260 * 2
def baseEnd_5707260 : Nat := 2930567600179445552702795

theorem tailTrace_5707260 : CollatzResearch.WordTrace tailWord_5707260 prefixEnd_5707260 2930567600179445552702795 := by
  unfold tailWord_5707260
  simp only [CollatzResearch.WordTrace]
  refine ⟨104080436651789608625747617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138773915535719478167663489 104080436651789608625747617)
  ·
    refine ⟨78060327488842206469310713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104080436651789608625747617 78060327488842206469310713)
    ·
      refine ⟨58545245616631654851983035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78060327488842206469310713 58545245616631654851983035)
      ·
        refine ⟨87817868424947482277974553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58545245616631654851983035 87817868424947482277974553)
        ·
          refine ⟨65863401318710611708480915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87817868424947482277974553 65863401318710611708480915)
          ·
            refine ⟨98795101978065917562721373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65863401318710611708480915 98795101978065917562721373)
            ·
              refine ⟨37048163241774719086020515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 98795101978065917562721373 37048163241774719086020515)
              ·
                refine ⟨55572244862662078629030773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37048163241774719086020515 55572244862662078629030773)
                ·
                  refine ⟨5209897955874569871471635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55572244862662078629030773 5209897955874569871471635)
                  ·
                    refine ⟨7814846933811854807207453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5209897955874569871471635 7814846933811854807207453)
                    ·
                      refine ⟨2930567600179445552702795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7814846933811854807207453 2930567600179445552702795)
                      ·
                        rfl

theorem cell23_5707260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 1, 5, 1, 3].length) (baseStart_5707260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5707260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5707260 prefixEnd_5707260 := by exact prefixLift 5707260
  have htrace : WordTrace (prefixWord ++ tailWord_5707260) baseStart_5707260 baseEnd_5707260 := by
    simpa [prefixWord, tailWord_5707260, baseEnd_5707260] using wordTrace_append hprefix tailTrace_5707260
  have hstable : (prefixWord ++ tailWord_5707260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5707260).length < 2 ^ (prefixWord ++ tailWord_5707260).sum := by decide
  have hdescent : baseEnd_5707260 < baseStart_5707260 := by decide
  rcases family_descends (prefixWord ++ tailWord_5707260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5707284 : List Nat := [2, 4, 3, 1, 2, 2, 1, 2, 6]
def baseStart_5707284 : Nat := 118140960795 + 5707284 * 2 ^ 59
def prefixEnd_5707284 : Nat := 4983230072969 + 3 ^ 40 * 5707284 * 2
def baseEnd_5707284 : Nat := 325619991523905939866965

theorem tailTrace_5707284 : CollatzResearch.WordTrace tailWord_5707284 prefixEnd_5707284 325619991523905939866965 := by
  unfold tailWord_5707284
  simp only [CollatzResearch.WordTrace]
  refine ⟨104080874327746134675184453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138774499103661512900245937 104080874327746134675184453)
  ·
    refine ⟨19515163936452400251597085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104080874327746134675184453 19515163936452400251597085)
    ·
      refine ⟨7318186476169650094348907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19515163936452400251597085 7318186476169650094348907)
      ·
        refine ⟨10977279714254475141523361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7318186476169650094348907 10977279714254475141523361)
        ·
          refine ⟨8232959785690856356142521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10977279714254475141523361 8232959785690856356142521)
          ·
            refine ⟨6174719839268142267106891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8232959785690856356142521 6174719839268142267106891)
            ·
              refine ⟨9262079758902213400660337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6174719839268142267106891 9262079758902213400660337)
              ·
                refine ⟨6946559819176660050495253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9262079758902213400660337 6946559819176660050495253)
                ·
                  refine ⟨325619991523905939866965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6946559819176660050495253 325619991523905939866965)
                  ·
                    rfl

theorem cell23_5707284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 2, 6].length) (baseStart_5707284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5707284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5707284 prefixEnd_5707284 := by exact prefixLift 5707284
  have htrace : WordTrace (prefixWord ++ tailWord_5707284) baseStart_5707284 baseEnd_5707284 := by
    simpa [prefixWord, tailWord_5707284, baseEnd_5707284] using wordTrace_append hprefix tailTrace_5707284
  have hstable : (prefixWord ++ tailWord_5707284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5707284).length < 2 ^ (prefixWord ++ tailWord_5707284).sum := by decide
  have hdescent : baseEnd_5707284 < baseStart_5707284 := by decide
  rcases family_descends (prefixWord ++ tailWord_5707284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5707317 : List Nat := [1, 3, 3, 1, 1, 4, 2, 2, 1, 1, 4]
def baseStart_5707317 : Nat := 118140960795 + 5707317 * 2 ^ 59
def prefixEnd_5707317 : Nat := 4983230072969 + 3 ^ 40 * 5707317 * 2
def baseEnd_5707317 : Nat := 2930596868576751829690033

theorem tailTrace_5707317 : CollatzResearch.WordTrace tailWord_5707317 prefixEnd_5707317 2930596868576751829690033 := by
  unfold tailWord_5707317
  simp only [CollatzResearch.WordTrace]
  refine ⟨208162952264372715986320205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138775301509581810657546803 208162952264372715986320205)
  ·
    refine ⟨78061107099139768494870077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208162952264372715986320205 78061107099139768494870077)
    ·
      refine ⟨29272915162177413185576279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78061107099139768494870077 29272915162177413185576279)
      ·
        refine ⟨43909372743266119778364419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29272915162177413185576279 43909372743266119778364419)
        ·
          refine ⟨65864059114899179667546629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43909372743266119778364419 65864059114899179667546629)
          ·
            refine ⟨12349511084043596187664993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65864059114899179667546629 12349511084043596187664993)
            ·
              refine ⟨9262133313032697140748745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12349511084043596187664993 9262133313032697140748745)
              ·
                refine ⟨6946599984774522855561559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9262133313032697140748745 6946599984774522855561559)
                ·
                  refine ⟨10419899977161784283342339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6946599984774522855561559 10419899977161784283342339)
                  ·
                    refine ⟨15629849965742676425013509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10419899977161784283342339 15629849965742676425013509)
                    ·
                      refine ⟨2930596868576751829690033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15629849965742676425013509 2930596868576751829690033)
                      ·
                        rfl

theorem cell23_5707317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 2, 1, 1, 4].length) (baseStart_5707317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5707317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5707317 prefixEnd_5707317 := by exact prefixLift 5707317
  have htrace : WordTrace (prefixWord ++ tailWord_5707317) baseStart_5707317 baseEnd_5707317 := by
    simpa [prefixWord, tailWord_5707317, baseEnd_5707317] using wordTrace_append hprefix tailTrace_5707317
  have hstable : (prefixWord ++ tailWord_5707317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5707317).length < 2 ^ (prefixWord ++ tailWord_5707317).sum := by decide
  have hdescent : baseEnd_5707317 < baseStart_5707317 := by decide
  rcases family_descends (prefixWord ++ tailWord_5707317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5707360 : List Nat := [2, 1, 1, 3, 2, 1, 1, 1, 2, 7, 2]
def baseStart_5707360 : Nat := 118140960795 + 5707360 * 2 ^ 59
def prefixEnd_5707360 : Nat := 4983230072969 + 3 ^ 40 * 5707360 * 2
def baseEnd_5707360 : Nat := 2930618948244895161452335

theorem tailTrace_5707360 : CollatzResearch.WordTrace tailWord_5707360 prefixEnd_5707360 2930618948244895161452335 := by
  unfold tailWord_5707360
  simp only [CollatzResearch.WordTrace]
  refine ⟨104082260301608467165067767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138776347068811289553423689 104082260301608467165067767)
  ·
    refine ⟨156123390452412700747601651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104082260301608467165067767 156123390452412700747601651)
    ·
      refine ⟨234185085678619051121402477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156123390452412700747601651 234185085678619051121402477)
      ·
        refine ⟨87819407129482144170525929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 234185085678619051121402477 87819407129482144170525929)
        ·
          refine ⟨65864555347111608127894447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87819407129482144170525929 65864555347111608127894447)
          ·
            refine ⟨98796833020667412191841671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65864555347111608127894447 98796833020667412191841671)
            ·
              refine ⟨148195249531001118287762507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98796833020667412191841671 148195249531001118287762507)
              ·
                refine ⟨222292874296501677431643761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 148195249531001118287762507 222292874296501677431643761)
                ·
                  refine ⟨166719655722376258073732821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 222292874296501677431643761 166719655722376258073732821)
                  ·
                    refine ⟨3907491930993193548603113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 166719655722376258073732821 3907491930993193548603113)
                    ·
                      refine ⟨2930618948244895161452335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3907491930993193548603113 2930618948244895161452335)
                      ·
                        rfl

theorem cell23_5707360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 2, 7, 2].length) (baseStart_5707360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5707360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5707360 prefixEnd_5707360 := by exact prefixLift 5707360
  have htrace : WordTrace (prefixWord ++ tailWord_5707360) baseStart_5707360 baseEnd_5707360 := by
    simpa [prefixWord, tailWord_5707360, baseEnd_5707360] using wordTrace_append hprefix tailTrace_5707360
  have hstable : (prefixWord ++ tailWord_5707360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5707360).length < 2 ^ (prefixWord ++ tailWord_5707360).sum := by decide
  have hdescent : baseEnd_5707360 < baseStart_5707360 := by decide
  rcases family_descends (prefixWord ++ tailWord_5707360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5707383 : List Nat := [1, 1, 3, 1, 1, 3, 1, 2, 4, 6]
def baseStart_5707383 : Nat := 118140960795 + 5707383 * 2 ^ 59
def prefixEnd_5707383 : Nat := 4983230072969 + 3 ^ 40 * 5707383 * 2
def baseEnd_5707383 : Nat := 976876919433316190488243

theorem tailTrace_5707383 : CollatzResearch.WordTrace tailWord_5707383 prefixEnd_5707383 976876919433316190488243 := by
  unfold tailWord_5707383
  simp only [CollatzResearch.WordTrace]
  refine ⟨208165359482133609258222803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138776906321422406172148535 208165359482133609258222803)
  ·
    refine ⟨312248039223200413887334205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208165359482133609258222803 312248039223200413887334205)
    ·
      refine ⟨117093014708700155207750327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 312248039223200413887334205 117093014708700155207750327)
      ·
        refine ⟨175639522063050232811625491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117093014708700155207750327 175639522063050232811625491)
        ·
          refine ⟨263459283094575349217438237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175639522063050232811625491 263459283094575349217438237)
          ·
            refine ⟨98797231160465755956539339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 263459283094575349217438237 98797231160465755956539339)
            ·
              refine ⟨148195846740698633934809009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98797231160465755956539339 148195846740698633934809009)
              ·
                refine ⟨111146885055523975451106757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 148195846740698633934809009 111146885055523975451106757)
                ·
                  refine ⟨20840040947910745397082517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 111146885055523975451106757 20840040947910745397082517)
                  ·
                    refine ⟨976876919433316190488243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20840040947910745397082517 976876919433316190488243)
                    ·
                      rfl

theorem cell23_5707383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 4, 6].length) (baseStart_5707383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5707383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5707383 prefixEnd_5707383 := by exact prefixLift 5707383
  have htrace : WordTrace (prefixWord ++ tailWord_5707383) baseStart_5707383 baseEnd_5707383 := by
    simpa [prefixWord, tailWord_5707383, baseEnd_5707383] using wordTrace_append hprefix tailTrace_5707383
  have hstable : (prefixWord ++ tailWord_5707383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5707383).length < 2 ^ (prefixWord ++ tailWord_5707383).sum := by decide
  have hdescent : baseEnd_5707383 < baseStart_5707383 := by decide
  rcases family_descends (prefixWord ++ tailWord_5707383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
