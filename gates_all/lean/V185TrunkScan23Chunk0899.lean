import V185TrunkScan23Chunk0898

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5320952 : List Nat := [2, 1, 2, 1, 1, 2, 1, 7, 1, 5]
def baseStart_5320952 : Nat := 118140960795 + 5320952 * 2 ^ 59
def prefixEnd_5320952 : Nat := 4983230072969 + 3 ^ 40 * 5320952 * 2
def baseEnd_5320952 : Nat := 910735305167456994843131

theorem tailTrace_5320952 : CollatzResearch.WordTrace tailWord_5320952 prefixEnd_5320952 910735305167456994843131 := by
  unfold tailWord_5320952
  simp only [CollatzResearch.WordTrace]
  refine ⟨97035531509553562548862555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129380708679404750065150073 97035531509553562548862555)
  ·
    refine ⟨145553297264330343823293833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97035531509553562548862555 145553297264330343823293833)
    ·
      refine ⟨109164972948247757867470375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145553297264330343823293833 109164972948247757867470375)
      ·
        refine ⟨163747459422371636801205563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109164972948247757867470375 163747459422371636801205563)
        ·
          refine ⟨245621189133557455201808345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163747459422371636801205563 245621189133557455201808345)
          ·
            refine ⟨184215891850168091401356259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 245621189133557455201808345 184215891850168091401356259)
            ·
              refine ⟨276323837775252137102034389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 184215891850168091401356259 276323837775252137102034389)
              ·
                refine ⟨6476339947857471963328931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 276323837775252137102034389 6476339947857471963328931)
                ·
                  refine ⟨9714509921786207944993397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6476339947857471963328931 9714509921786207944993397)
                  ·
                    refine ⟨910735305167456994843131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9714509921786207944993397 910735305167456994843131)
                    ·
                      rfl

theorem cell23_5320952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 7, 1, 5].length) (baseStart_5320952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5320952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5320952 prefixEnd_5320952 := by exact prefixLift 5320952
  have htrace : WordTrace (prefixWord ++ tailWord_5320952) baseStart_5320952 baseEnd_5320952 := by
    simpa [prefixWord, tailWord_5320952, baseEnd_5320952] using wordTrace_append hprefix tailTrace_5320952
  have hstable : (prefixWord ++ tailWord_5320952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5320952).length < 2 ^ (prefixWord ++ tailWord_5320952).sum := by decide
  have hdescent : baseEnd_5320952 < baseStart_5320952 := by decide
  rcases family_descends (prefixWord ++ tailWord_5320952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5320959 : List Nat := [1, 1, 2, 2, 1, 4, 1, 4, 2, 3, 2]
def baseStart_5320959 : Nat := 118140960795 + 5320959 * 2 ^ 59
def prefixEnd_5320959 : Nat := 4983230072969 + 3 ^ 40 * 5320959 * 2
def baseEnd_5320959 : Nat := 2732209509866952457141861

theorem tailTrace_5320959 : CollatzResearch.WordTrace tailWord_5320959 prefixEnd_5320959 2732209509866952457141861 := by
  unfold tailWord_5320959
  simp only [CollatzResearch.WordTrace]
  refine ⟨194071318330081765293229931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129380878886721176862153287 194071318330081765293229931)
  ·
    refine ⟨291106977495122647939844897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194071318330081765293229931 291106977495122647939844897)
    ·
      refine ⟨218330233121341985954883673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 291106977495122647939844897 218330233121341985954883673)
      ·
        refine ⟨163747674841006489466162755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 218330233121341985954883673 163747674841006489466162755)
        ·
          refine ⟨245621512261509734199244133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163747674841006489466162755 245621512261509734199244133)
          ·
            refine ⟨46054033549033075162358275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 245621512261509734199244133 46054033549033075162358275)
            ·
              refine ⟨69081050323549612743537413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46054033549033075162358275 69081050323549612743537413)
              ·
                refine ⟨12952696935665552389413265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69081050323549612743537413 12952696935665552389413265)
                ·
                  refine ⟨9714522701749164292059949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12952696935665552389413265 9714522701749164292059949)
                  ·
                    refine ⟨3642946013155936609522481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9714522701749164292059949 3642946013155936609522481)
                    ·
                      refine ⟨2732209509866952457141861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3642946013155936609522481 2732209509866952457141861)
                      ·
                        rfl

theorem cell23_5320959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 4, 2, 3, 2].length) (baseStart_5320959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5320959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5320959 prefixEnd_5320959 := by exact prefixLift 5320959
  have htrace : WordTrace (prefixWord ++ tailWord_5320959) baseStart_5320959 baseEnd_5320959 := by
    simpa [prefixWord, tailWord_5320959, baseEnd_5320959] using wordTrace_append hprefix tailTrace_5320959
  have hstable : (prefixWord ++ tailWord_5320959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5320959).length < 2 ^ (prefixWord ++ tailWord_5320959).sum := by decide
  have hdescent : baseEnd_5320959 < baseStart_5320959 := by decide
  rcases family_descends (prefixWord ++ tailWord_5320959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5320972 : List Nat := [2, 2, 1, 2, 2, 2, 1, 1, 5, 1, 4]
def baseStart_5320972 : Nat := 118140960795 + 5320972 * 2 ^ 59
def prefixEnd_5320972 : Nat := 4983230072969 + 3 ^ 40 * 5320972 * 2
def baseEnd_5320972 : Nat := 2732216185115460906279301

theorem tailTrace_5320972 : CollatzResearch.WordTrace tailWord_5320972 prefixEnd_5320972 2732216185115460906279301 := by
  unfold tailWord_5320972
  simp only [CollatzResearch.WordTrace]
  refine ⟨97035896239517334256726585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129381194986023112342302113 97035896239517334256726585)
  ·
    refine ⟨72776922179638000692544939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97035896239517334256726585 72776922179638000692544939)
    ·
      refine ⟨109165383269457001038817409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72776922179638000692544939 109165383269457001038817409)
      ·
        refine ⟨81874037452092750779113057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109165383269457001038817409 81874037452092750779113057)
        ·
          refine ⟨61405528089069563084334793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81874037452092750779113057 61405528089069563084334793)
          ·
            refine ⟨46054146066802172313251095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61405528089069563084334793 46054146066802172313251095)
            ·
              refine ⟨69081219100203258469876643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46054146066802172313251095 69081219100203258469876643)
              ·
                refine ⟨103621828650304887704814965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69081219100203258469876643 103621828650304887704814965)
                ·
                  refine ⟨9714546435966083222326403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 103621828650304887704814965 9714546435966083222326403)
                  ·
                    refine ⟨14571819653949124833489605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9714546435966083222326403 14571819653949124833489605)
                    ·
                      refine ⟨2732216185115460906279301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14571819653949124833489605 2732216185115460906279301)
                      ·
                        rfl

theorem cell23_5320972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 5, 1, 4].length) (baseStart_5320972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5320972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5320972 prefixEnd_5320972 := by exact prefixLift 5320972
  have htrace : WordTrace (prefixWord ++ tailWord_5320972) baseStart_5320972 baseEnd_5320972 := by
    simpa [prefixWord, tailWord_5320972, baseEnd_5320972] using wordTrace_append hprefix tailTrace_5320972
  have hstable : (prefixWord ++ tailWord_5320972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5320972).length < 2 ^ (prefixWord ++ tailWord_5320972).sum := by decide
  have hdescent : baseEnd_5320972 < baseStart_5320972 := by decide
  rcases family_descends (prefixWord ++ tailWord_5320972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5321000 : List Nat := [2, 1, 5, 1, 3, 1, 2, 3, 1, 1, 3]
def baseStart_5321000 : Nat := 118140960795 + 5321000 * 2 ^ 59
def prefixEnd_5321000 : Nat := 4983230072969 + 3 ^ 40 * 5321000 * 2
def baseEnd_5321000 : Nat := 2732230562573786796729173

theorem tailTrace_5321000 : CollatzResearch.WordTrace tailWord_5321000 prefixEnd_5321000 2732230562573786796729173 := by
  unfold tailWord_5321000
  simp only [CollatzResearch.WordTrace]
  refine ⟨97036406861466614647736227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129381875815288819530314969 97036406861466614647736227)
  ·
    refine ⟨145554610292199921971604341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97036406861466614647736227 145554610292199921971604341)
    ·
      refine ⟨13645744714893742684837907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 145554610292199921971604341 13645744714893742684837907)
      ·
        refine ⟨20468617072340614027256861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13645744714893742684837907 20468617072340614027256861)
        ·
          refine ⟨7675731402127730260221323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20468617072340614027256861 7675731402127730260221323)
          ·
            refine ⟨11513597103191595390331985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7675731402127730260221323 11513597103191595390331985)
            ·
              refine ⟨8635197827393696542748989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11513597103191595390331985 8635197827393696542748989)
              ·
                refine ⟨3238199185272636203530871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8635197827393696542748989 3238199185272636203530871)
                ·
                  refine ⟨4857298777908954305296307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3238199185272636203530871 4857298777908954305296307)
                  ·
                    refine ⟨7285948166863431457944461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4857298777908954305296307 7285948166863431457944461)
                    ·
                      refine ⟨2732230562573786796729173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7285948166863431457944461 2732230562573786796729173)
                      ·
                        rfl

theorem cell23_5321000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 3, 1, 1, 3].length) (baseStart_5321000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5321000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5321000 prefixEnd_5321000 := by exact prefixLift 5321000
  have htrace : WordTrace (prefixWord ++ tailWord_5321000) baseStart_5321000 baseEnd_5321000 := by
    simpa [prefixWord, tailWord_5321000, baseEnd_5321000] using wordTrace_append hprefix tailTrace_5321000
  have hstable : (prefixWord ++ tailWord_5321000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5321000).length < 2 ^ (prefixWord ++ tailWord_5321000).sum := by decide
  have hdescent : baseEnd_5321000 < baseStart_5321000 := by decide
  rcases family_descends (prefixWord ++ tailWord_5321000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5321023 : List Nat := [1, 1, 2, 2, 4, 1, 1, 6, 1, 2, 2]
def baseStart_5321023 : Nat := 118140960795 + 5321023 * 2 ^ 59
def prefixEnd_5321023 : Nat := 4983230072969 + 3 ^ 40 * 5321023 * 2
def baseEnd_5321023 : Nat := 2732242372628840206741567

theorem tailTrace_5321023 : CollatzResearch.WordTrace tailWord_5321023 prefixEnd_5321023 2732242372628840206741567 := by
  unfold tailWord_5321023
  simp only [CollatzResearch.WordTrace]
  refine ⟨194073652601849904223559723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129382435067899936149039815 194073652601849904223559723)
  ·
    refine ⟨291110478902774856335339585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194073652601849904223559723 291110478902774856335339585)
    ·
      refine ⟨218332859177081142251504689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 291110478902774856335339585 218332859177081142251504689)
      ·
        refine ⟨163749644382810856688628517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 218332859177081142251504689 163749644382810856688628517)
        ·
          refine ⟨30703058321777035629117847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 163749644382810856688628517 30703058321777035629117847)
          ·
            refine ⟨46054587482665553443676771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30703058321777035629117847 46054587482665553443676771)
            ·
              refine ⟨69081881223998330165515157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46054587482665553443676771 69081881223998330165515157)
              ·
                refine ⟨3238213182374921726508523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 69081881223998330165515157 3238213182374921726508523)
                ·
                  refine ⟨4857319773562382589762785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3238213182374921726508523 4857319773562382589762785)
                  ·
                    refine ⟨3642989830171786942322089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4857319773562382589762785 3642989830171786942322089)
                    ·
                      refine ⟨2732242372628840206741567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3642989830171786942322089 2732242372628840206741567)
                      ·
                        rfl

theorem cell23_5321023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 6, 1, 2, 2].length) (baseStart_5321023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5321023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5321023 prefixEnd_5321023 := by exact prefixLift 5321023
  have htrace : WordTrace (prefixWord ++ tailWord_5321023) baseStart_5321023 baseEnd_5321023 := by
    simpa [prefixWord, tailWord_5321023, baseEnd_5321023] using wordTrace_append hprefix tailTrace_5321023
  have hstable : (prefixWord ++ tailWord_5321023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5321023).length < 2 ^ (prefixWord ++ tailWord_5321023).sum := by decide
  have hdescent : baseEnd_5321023 < baseStart_5321023 := by decide
  rcases family_descends (prefixWord ++ tailWord_5321023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5321042 : List Nat := [3, 2, 2, 1, 1, 1, 2, 2, 2, 7]
def baseStart_5321042 : Nat := 118140960795 + 5321042 * 2 ^ 59
def prefixEnd_5321042 : Nat := 4983230072969 + 3 ^ 40 * 5321042 * 2
def baseEnd_5321042 : Nat := 910750709587091877467993

theorem tailTrace_5321042 : CollatzResearch.WordTrace tailWord_5321042 prefixEnd_5321042 910750709587091877467993 := by
  unfold tailWord_5321042
  simp only [CollatzResearch.WordTrace]
  refine ⟨48518586397195267617125345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129382897059187380312334253 48518586397195267617125345)
  ·
    refine ⟨36388939797896450712844009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48518586397195267617125345 36388939797896450712844009)
    ·
      refine ⟨27291704848422338034633007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36388939797896450712844009 27291704848422338034633007)
      ·
        refine ⟨40937557272633507051949511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27291704848422338034633007 40937557272633507051949511)
        ·
          refine ⟨61406335908950260577924267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40937557272633507051949511 61406335908950260577924267)
          ·
            refine ⟨92109503863425390866886401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61406335908950260577924267 92109503863425390866886401)
            ·
              refine ⟨69082127897569043150164801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92109503863425390866886401 69082127897569043150164801)
              ·
                refine ⟨51811595923176782362623601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69082127897569043150164801 51811595923176782362623601)
                ·
                  refine ⟨38858696942382586771967701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51811595923176782362623601 38858696942382586771967701)
                  ·
                    refine ⟨910750709587091877467993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38858696942382586771967701 910750709587091877467993)
                    ·
                      rfl

theorem cell23_5321042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 2, 2, 7].length) (baseStart_5321042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5321042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5321042 prefixEnd_5321042 := by exact prefixLift 5321042
  have htrace : WordTrace (prefixWord ++ tailWord_5321042) baseStart_5321042 baseEnd_5321042 := by
    simpa [prefixWord, tailWord_5321042, baseEnd_5321042] using wordTrace_append hprefix tailTrace_5321042
  have hstable : (prefixWord ++ tailWord_5321042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5321042).length < 2 ^ (prefixWord ++ tailWord_5321042).sum := by decide
  have hdescent : baseEnd_5321042 < baseStart_5321042 := by decide
  rcases family_descends (prefixWord ++ tailWord_5321042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5321079 : List Nat := [1, 1, 3, 1, 1, 2, 2, 1, 5, 4, 2]
def baseStart_5321079 : Nat := 118140960795 + 5321079 * 2 ^ 59
def prefixEnd_5321079 : Nat := 4983230072969 + 3 ^ 40 * 5321079 * 2
def baseEnd_5321079 : Nat := 2732271127545491987641309

theorem tailTrace_5321079 : CollatzResearch.WordTrace tailWord_5321079 prefixEnd_5321079 2732271127545491987641309 := by
  unfold tailWord_5321079
  simp only [CollatzResearch.WordTrace]
  refine ⟨194075695089647025787598291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129383796726431350525065527 194075695089647025787598291)
  ·
    refine ⟨291113542634470538681397437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194075695089647025787598291 291113542634470538681397437)
    ·
      refine ⟨109167578487926452005524039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 291113542634470538681397437 109167578487926452005524039)
      ·
        refine ⟨163751367731889678008286059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109167578487926452005524039 163751367731889678008286059)
        ·
          refine ⟨245627051597834517012429089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163751367731889678008286059 245627051597834517012429089)
          ·
            refine ⟨184220288698375887759321817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 245627051597834517012429089 184220288698375887759321817)
            ·
              refine ⟨138165216523781915819491363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 184220288698375887759321817 138165216523781915819491363)
              ·
                refine ⟨207247824785672873729237045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 138165216523781915819491363 207247824785672873729237045)
                ·
                  refine ⟨19429483573656831912115973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 207247824785672873729237045 19429483573656831912115973)
                  ·
                    refine ⟨3643028170060655983521745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19429483573656831912115973 3643028170060655983521745)
                    ·
                      refine ⟨2732271127545491987641309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3643028170060655983521745 2732271127545491987641309)
                      ·
                        rfl

theorem cell23_5321079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 5, 4, 2].length) (baseStart_5321079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5321079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5321079 prefixEnd_5321079 := by exact prefixLift 5321079
  have htrace : WordTrace (prefixWord ++ tailWord_5321079) baseStart_5321079 baseEnd_5321079 := by
    simpa [prefixWord, tailWord_5321079, baseEnd_5321079] using wordTrace_append hprefix tailTrace_5321079
  have hstable : (prefixWord ++ tailWord_5321079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5321079).length < 2 ^ (prefixWord ++ tailWord_5321079).sum := by decide
  have hdescent : baseEnd_5321079 < baseStart_5321079 := by decide
  rcases family_descends (prefixWord ++ tailWord_5321079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5321082 : List Nat := [3, 1, 1, 1, 1, 1, 2, 1, 6, 1, 5]
def baseStart_5321082 : Nat := 118140960795 + 5321082 * 2 ^ 59
def prefixEnd_5321082 : Nat := 4983230072969 + 3 ^ 40 * 5321082 * 2
def baseEnd_5321082 : Nat := 2732272667987455475903795

theorem tailTrace_5321082 : CollatzResearch.WordTrace tailWord_5321082 prefixEnd_5321082 2732272667987455475903795 := by
  unfold tailWord_5321082
  simp only [CollatzResearch.WordTrace]
  refine ⟨48518951127159039324989375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129383869672424104866638333 48518951127159039324989375)
  ·
    refine ⟨72778426690738558987484063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48518951127159039324989375 72778426690738558987484063)
    ·
      refine ⟨109167640036107838481226095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72778426690738558987484063 109167640036107838481226095)
      ·
        refine ⟨163751460054161757721839143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109167640036107838481226095 163751460054161757721839143)
        ·
          refine ⟨245627190081242636582758715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163751460054161757721839143 245627190081242636582758715)
          ·
            refine ⟨368440785121863954874138073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 245627190081242636582758715 368440785121863954874138073)
            ·
              refine ⟨276330588841397966155603555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 368440785121863954874138073 276330588841397966155603555)
              ·
                refine ⟨414495883262096949233405333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 276330588841397966155603555 414495883262096949233405333)
                ·
                  refine ⟨19429494527910794495315875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 414495883262096949233405333 19429494527910794495315875)
                  ·
                    refine ⟨29144241791866191742973813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19429494527910794495315875 29144241791866191742973813)
                    ·
                      refine ⟨2732272667987455475903795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29144241791866191742973813 2732272667987455475903795)
                      ·
                        rfl

theorem cell23_5321082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 6, 1, 5].length) (baseStart_5321082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5321082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5321082 prefixEnd_5321082 := by exact prefixLift 5321082
  have htrace : WordTrace (prefixWord ++ tailWord_5321082) baseStart_5321082 baseEnd_5321082 := by
    simpa [prefixWord, tailWord_5321082, baseEnd_5321082] using wordTrace_append hprefix tailTrace_5321082
  have hstable : (prefixWord ++ tailWord_5321082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5321082).length < 2 ^ (prefixWord ++ tailWord_5321082).sum := by decide
  have hdescent : baseEnd_5321082 < baseStart_5321082 := by decide
  rcases family_descends (prefixWord ++ tailWord_5321082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5321096 : List Nat := [2, 1, 3, 3, 1, 1, 2, 3, 1, 4, 2]
def baseStart_5321096 : Nat := 118140960795 + 5321096 * 2 ^ 59
def prefixEnd_5321096 : Nat := 4983230072969 + 3 ^ 40 * 5321096 * 2
def baseEnd_5321096 : Nat := 2732279856716618421128731

theorem tailTrace_5321096 : CollatzResearch.WordTrace tailWord_5321096 prefixEnd_5321096 2732279856716618421128731 := by
  unfold tailWord_5321096
  simp only [CollatzResearch.WordTrace]
  refine ⟨97038157565292718845483571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129384210087056958460644761 97038157565292718845483571)
  ·
    refine ⟨145557236347939078268225357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97038157565292718845483571 145557236347939078268225357)
    ·
      refine ⟨54583963630477154350584509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145557236347939078268225357 54583963630477154350584509)
      ·
        refine ⟨20468986361428932881469191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54583963630477154350584509 20468986361428932881469191)
        ·
          refine ⟨30703479542143399322203787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20468986361428932881469191 30703479542143399322203787)
          ·
            refine ⟨46055219313215098983305681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30703479542143399322203787 46055219313215098983305681)
            ·
              refine ⟨34541414484911324237479261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46055219313215098983305681 34541414484911324237479261)
              ·
                refine ⟨12953030431841746589054723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34541414484911324237479261 12953030431841746589054723)
                ·
                  refine ⟨19429545647762619883582085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12953030431841746589054723 19429545647762619883582085)
                  ·
                    refine ⟨3643039808955491228171641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19429545647762619883582085 3643039808955491228171641)
                    ·
                      refine ⟨2732279856716618421128731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3643039808955491228171641 2732279856716618421128731)
                      ·
                        rfl

theorem cell23_5321096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 3, 1, 4, 2].length) (baseStart_5321096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5321096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5321096 prefixEnd_5321096 := by exact prefixLift 5321096
  have htrace : WordTrace (prefixWord ++ tailWord_5321096) baseStart_5321096 baseEnd_5321096 := by
    simpa [prefixWord, tailWord_5321096, baseEnd_5321096] using wordTrace_append hprefix tailTrace_5321096
  have hstable : (prefixWord ++ tailWord_5321096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5321096).length < 2 ^ (prefixWord ++ tailWord_5321096).sum := by decide
  have hdescent : baseEnd_5321096 < baseStart_5321096 := by decide
  rcases family_descends (prefixWord ++ tailWord_5321096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5321132 : List Nat := [2, 2, 1, 1, 1, 1, 3, 2, 3, 7]
def baseStart_5321132 : Nat := 118140960795 + 5321132 * 2 ^ 59
def prefixEnd_5321132 : Nat := 4983230072969 + 3 ^ 40 * 5321132 * 2
def baseEnd_5321132 : Nat := 910766114006726760092855

theorem tailTrace_5321132 : CollatzResearch.WordTrace tailWord_5321132 prefixEnd_5321132 910766114006726760092855 := by
  unfold tailWord_5321132
  simp only [CollatzResearch.WordTrace]
  refine ⟨97038814079227507919638825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129385085438970010559518433 97038814079227507919638825)
  ·
    refine ⟨72779110559420630939729119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97038814079227507919638825 72779110559420630939729119)
    ·
      refine ⟨109168665839130946409593679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72779110559420630939729119 109168665839130946409593679)
      ·
        refine ⟨163752998758696419614390519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109168665839130946409593679 163752998758696419614390519)
        ·
          refine ⟨245629498138044629421585779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163752998758696419614390519 245629498138044629421585779)
          ·
            refine ⟨368444247207066944132378669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 245629498138044629421585779 368444247207066944132378669)
            ·
              refine ⟨138166592702650104049642001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 368444247207066944132378669 138166592702650104049642001)
              ·
                refine ⟨103624944526987578037231501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 138166592702650104049642001 103624944526987578037231501)
                ·
                  refine ⟨38859354197620341763961813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 103624944526987578037231501 38859354197620341763961813)
                  ·
                    refine ⟨910766114006726760092855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38859354197620341763961813 910766114006726760092855)
                    ·
                      rfl

theorem cell23_5321132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 7].length) (baseStart_5321132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5321132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5321132 prefixEnd_5321132 := by exact prefixLift 5321132
  have htrace : WordTrace (prefixWord ++ tailWord_5321132) baseStart_5321132 baseEnd_5321132 := by
    simpa [prefixWord, tailWord_5321132, baseEnd_5321132] using wordTrace_append hprefix tailTrace_5321132
  have hstable : (prefixWord ++ tailWord_5321132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5321132).length < 2 ^ (prefixWord ++ tailWord_5321132).sum := by decide
  have hdescent : baseEnd_5321132 < baseStart_5321132 := by decide
  rcases family_descends (prefixWord ++ tailWord_5321132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5321170 : List Nat := [3, 2, 2, 4, 1, 1, 2, 3, 5]
def baseStart_5321170 : Nat := 118140960795 + 5321170 * 2 ^ 59
def prefixEnd_5321170 : Nat := 4983230072969 + 3 ^ 40 * 5321170 * 2
def baseEnd_5321170 : Nat := 303590872698339014622599

theorem tailTrace_5321170 : CollatzResearch.WordTrace tailWord_5321170 prefixEnd_5321170 303590872698339014622599 := by
  unfold tailWord_5321170
  simp only [CollatzResearch.WordTrace]
  refine ⟨48519753533079337082290241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129386009421544898886107309 48519753533079337082290241)
  ·
    refine ⟨36389815149809502811717681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48519753533079337082290241 36389815149809502811717681)
    ·
      refine ⟨27292361362357127108788261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36389815149809502811717681 27292361362357127108788261)
      ·
        refine ⟨5117317755441961332897799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27292361362357127108788261 5117317755441961332897799)
        ·
          refine ⟨7675976633162941999346699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5117317755441961332897799 7675976633162941999346699)
          ·
            refine ⟨11513964949744412999020049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7675976633162941999346699 11513964949744412999020049)
            ·
              refine ⟨8635473712308309749265037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11513964949744412999020049 8635473712308309749265037)
              ·
                refine ⟨3238302642115616155974389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8635473712308309749265037 3238302642115616155974389)
                ·
                  refine ⟨303590872698339014622599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3238302642115616155974389 303590872698339014622599)
                  ·
                    rfl

theorem cell23_5321170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 3, 5].length) (baseStart_5321170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5321170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5321170 prefixEnd_5321170 := by exact prefixLift 5321170
  have htrace : WordTrace (prefixWord ++ tailWord_5321170) baseStart_5321170 baseEnd_5321170 := by
    simpa [prefixWord, tailWord_5321170, baseEnd_5321170] using wordTrace_append hprefix tailTrace_5321170
  have hstable : (prefixWord ++ tailWord_5321170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5321170).length < 2 ^ (prefixWord ++ tailWord_5321170).sum := by decide
  have hdescent : baseEnd_5321170 < baseStart_5321170 := by decide
  rcases family_descends (prefixWord ++ tailWord_5321170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5321196 : List Nat := [2, 2, 1, 1, 2, 1, 6, 1, 3, 4]
def baseStart_5321196 : Nat := 118140960795 + 5321196 * 2 ^ 59
def prefixEnd_5321196 : Nat := 4983230072969 + 3 ^ 40 * 5321196 * 2
def baseEnd_5321196 : Nat := 910777068260689343292757

theorem tailTrace_5321196 : CollatzResearch.WordTrace tailWord_5321196 prefixEnd_5321196 910777068260689343292757 := by
  unfold tailWord_5321196
  simp only [CollatzResearch.WordTrace]
  refine ⟨97039981215111577384803721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129386641620148769846404961 97039981215111577384803721)
  ·
    refine ⟨72779985911333683038602791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97039981215111577384803721 72779985911333683038602791)
    ·
      refine ⟨109169978867000524557904187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72779985911333683038602791 109169978867000524557904187)
      ·
        refine ⟨163754968300500786836856281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109169978867000524557904187 163754968300500786836856281)
        ·
          refine ⟨122816226225375590127642211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163754968300500786836856281 122816226225375590127642211)
          ·
            refine ⟨184224339338063385191463317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122816226225375590127642211 184224339338063385191463317)
            ·
              refine ⟨8635515906471721180849843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 184224339338063385191463317 8635515906471721180849843)
              ·
                refine ⟨12953273859707581771274765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8635515906471721180849843 12953273859707581771274765)
                ·
                  refine ⟨4857477697390343164228037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12953273859707581771274765 4857477697390343164228037)
                  ·
                    refine ⟨910777068260689343292757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4857477697390343164228037 910777068260689343292757)
                    ·
                      rfl

theorem cell23_5321196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 4].length) (baseStart_5321196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5321196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5321196 prefixEnd_5321196 := by exact prefixLift 5321196
  have htrace : WordTrace (prefixWord ++ tailWord_5321196) baseStart_5321196 baseEnd_5321196 := by
    simpa [prefixWord, tailWord_5321196, baseEnd_5321196] using wordTrace_append hprefix tailTrace_5321196
  have hstable : (prefixWord ++ tailWord_5321196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5321196).length < 2 ^ (prefixWord ++ tailWord_5321196).sum := by decide
  have hdescent : baseEnd_5321196 < baseStart_5321196 := by decide
  rcases family_descends (prefixWord ++ tailWord_5321196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5321206 : List Nat := [5, 1, 1, 1, 2, 1, 1, 1, 3, 4, 3]
def baseStart_5321206 : Nat := 118140960795 + 5321206 * 2 ^ 59
def prefixEnd_5321206 : Nat := 4983230072969 + 3 ^ 40 * 5321206 * 2
def baseEnd_5321206 : Nat := 2732336339588612990753225

theorem tailTrace_5321206 : CollatzResearch.WordTrace tailWord_5321206 prefixEnd_5321206 2732336339588612990753225 := by
  unfold tailWord_5321206
  simp only [CollatzResearch.WordTrace]
  refine ⟨12130020447511682904841967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 129386884773457950984980981 12130020447511682904841967)
  ·
    refine ⟨18195030671267524357262951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12130020447511682904841967 18195030671267524357262951)
    ·
      refine ⟨27292546006901286535894427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18195030671267524357262951 27292546006901286535894427)
      ·
        refine ⟨40938819010351929803841641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27292546006901286535894427 40938819010351929803841641)
        ·
          refine ⟨30704114257763947352881231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40938819010351929803841641 30704114257763947352881231)
          ·
            refine ⟨46056171386645921029321847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30704114257763947352881231 46056171386645921029321847)
            ·
              refine ⟨69084257079968881543982771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46056171386645921029321847 69084257079968881543982771)
              ·
                refine ⟨103626385619953322315974157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69084257079968881543982771 103626385619953322315974157)
                ·
                  refine ⟨38859894607482495868490309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 103626385619953322315974157 38859894607482495868490309)
                  ·
                    refine ⟨7286230238902967975341933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38859894607482495868490309 7286230238902967975341933)
                    ·
                      refine ⟨2732336339588612990753225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7286230238902967975341933 2732336339588612990753225)
                      ·
                        rfl

theorem cell23_5321206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 3, 4, 3].length) (baseStart_5321206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5321206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5321206 prefixEnd_5321206 := by exact prefixLift 5321206
  have htrace : WordTrace (prefixWord ++ tailWord_5321206) baseStart_5321206 baseEnd_5321206 := by
    simpa [prefixWord, tailWord_5321206, baseEnd_5321206] using wordTrace_append hprefix tailTrace_5321206
  have hstable : (prefixWord ++ tailWord_5321206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5321206).length < 2 ^ (prefixWord ++ tailWord_5321206).sum := by decide
  have hdescent : baseEnd_5321206 < baseStart_5321206 := by decide
  rcases family_descends (prefixWord ++ tailWord_5321206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5321209 : List Nat := [1, 2, 1, 3, 1, 2, 2, 5, 6]
def baseStart_5321209 : Nat := 118140960795 + 5321209 * 2 ^ 59
def prefixEnd_5321209 : Nat := 4983230072969 + 3 ^ 40 * 5321209 * 2
def baseEnd_5321209 : Nat := 303593097781175164335079

theorem tailTrace_5321209 : CollatzResearch.WordTrace tailWord_5321209 prefixEnd_5321209 303593097781175164335079 := by
  unfold tailWord_5321209
  simp only [CollatzResearch.WordTrace]
  refine ⟨194080436579176057989830681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129386957719450705326553787 194080436579176057989830681)
  ·
    refine ⟨145560327434382043492373011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194080436579176057989830681 145560327434382043492373011)
    ·
      refine ⟨218340491151573065238559517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145560327434382043492373011 218340491151573065238559517)
      ·
        refine ⟨81877684181839899464459819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 218340491151573065238559517 81877684181839899464459819)
        ·
          refine ⟨122816526272759849196689729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81877684181839899464459819 122816526272759849196689729)
          ·
            refine ⟨92112394704569886897517297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122816526272759849196689729 92112394704569886897517297)
            ·
              refine ⟨69084296028427415173137973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92112394704569886897517297 69084296028427415173137973)
              ·
                refine ⟨6476652752665070172481685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 69084296028427415173137973 6476652752665070172481685)
                ·
                  refine ⟨303593097781175164335079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6476652752665070172481685 303593097781175164335079)
                  ·
                    rfl

theorem cell23_5321209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 5, 6].length) (baseStart_5321209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5321209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5321209 prefixEnd_5321209 := by exact prefixLift 5321209
  have htrace : WordTrace (prefixWord ++ tailWord_5321209) baseStart_5321209 baseEnd_5321209 := by
    simpa [prefixWord, tailWord_5321209, baseEnd_5321209] using wordTrace_append hprefix tailTrace_5321209
  have hstable : (prefixWord ++ tailWord_5321209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5321209).length < 2 ^ (prefixWord ++ tailWord_5321209).sum := by decide
  have hdescent : baseEnd_5321209 < baseStart_5321209 := by decide
  rcases family_descends (prefixWord ++ tailWord_5321209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5321219 : List Nat := [1, 1, 1, 3, 2, 1, 3, 1, 2, 5, 3]
def baseStart_5321219 : Nat := 118140960795 + 5321219 * 2 ^ 59
def prefixEnd_5321219 : Nat := 4983230072969 + 3 ^ 40 * 5321219 * 2
def baseEnd_5321219 : Nat := 2732343014837121439890665

theorem tailTrace_5321219 : CollatzResearch.WordTrace tailWord_5321219 prefixEnd_5321219 2732343014837121439890665 := by
  unfold tailWord_5321219
  simp only [CollatzResearch.WordTrace]
  refine ⟨194080801309139829697694711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129387200872759886465129807 194080801309139829697694711)
  ·
    refine ⟨291121201963709744546542067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194080801309139829697694711 291121201963709744546542067)
    ·
      refine ⟨436681802945564616819813101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 291121201963709744546542067 436681802945564616819813101)
      ·
        refine ⟨163755676104586731307429913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 436681802945564616819813101 163755676104586731307429913)
        ·
          refine ⟨122816757078440048480572435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163755676104586731307429913 122816757078440048480572435)
          ·
            refine ⟨184225135617660072720858653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122816757078440048480572435 184225135617660072720858653)
            ·
              refine ⟨69084425856622527270321995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 184225135617660072720858653 69084425856622527270321995)
              ·
                refine ⟨103626638784933790905482993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69084425856622527270321995 103626638784933790905482993)
                ·
                  refine ⟨77719979088700343179112245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 103626638784933790905482993 77719979088700343179112245)
                  ·
                    refine ⟨7286248039565657173041773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 77719979088700343179112245 7286248039565657173041773)
                    ·
                      refine ⟨2732343014837121439890665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7286248039565657173041773 2732343014837121439890665)
                      ·
                        rfl

theorem cell23_5321219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 2, 5, 3].length) (baseStart_5321219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5321219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5321219 prefixEnd_5321219 := by exact prefixLift 5321219
  have htrace : WordTrace (prefixWord ++ tailWord_5321219) baseStart_5321219 baseEnd_5321219 := by
    simpa [prefixWord, tailWord_5321219, baseEnd_5321219] using wordTrace_append hprefix tailTrace_5321219
  have hstable : (prefixWord ++ tailWord_5321219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5321219).length < 2 ^ (prefixWord ++ tailWord_5321219).sum := by decide
  have hdescent : baseEnd_5321219 < baseStart_5321219 := by decide
  rcases family_descends (prefixWord ++ tailWord_5321219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5321230 : List Nat := [4, 1, 1, 2, 3, 1, 3, 3, 1, 4]
def baseStart_5321230 : Nat := 118140960795 + 5321230 * 2 ^ 59
def prefixEnd_5321230 : Nat := 4983230072969 + 3 ^ 40 * 5321230 * 2
def baseEnd_5321230 : Nat := 910782887708106965617705

theorem tailTrace_5321230 : CollatzResearch.WordTrace tailWord_5321230 prefixEnd_5321230 910782887708106965617705 := by
  unfold tailWord_5321230
  simp only [CollatzResearch.WordTrace]
  refine ⟨24260150314012497322043143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129387468341399985717563429 24260150314012497322043143)
  ·
    refine ⟨36390225471018745983064715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24260150314012497322043143 36390225471018745983064715)
    ·
      refine ⟨54585338206528118974597073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36390225471018745983064715 54585338206528118974597073)
      ·
        refine ⟨40939003654896089230947805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54585338206528118974597073 40939003654896089230947805)
        ·
          refine ⟨15352126370586033461605427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40939003654896089230947805 15352126370586033461605427)
          ·
            refine ⟨23028189555879050192408141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15352126370586033461605427 23028189555879050192408141)
            ·
              refine ⟨8635571083454643822153053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23028189555879050192408141 8635571083454643822153053)
              ·
                refine ⟨3238339156295491433307395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8635571083454643822153053 3238339156295491433307395)
                ·
                  refine ⟨4857508734443237149961093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3238339156295491433307395 4857508734443237149961093)
                  ·
                    refine ⟨910782887708106965617705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4857508734443237149961093 910782887708106965617705)
                    ·
                      rfl

theorem cell23_5321230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 3, 1, 4].length) (baseStart_5321230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5321230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5321230 prefixEnd_5321230 := by exact prefixLift 5321230
  have htrace : WordTrace (prefixWord ++ tailWord_5321230) baseStart_5321230 baseEnd_5321230 := by
    simpa [prefixWord, tailWord_5321230, baseEnd_5321230] using wordTrace_append hprefix tailTrace_5321230
  have hstable : (prefixWord ++ tailWord_5321230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5321230).length < 2 ^ (prefixWord ++ tailWord_5321230).sum := by decide
  have hdescent : baseEnd_5321230 < baseStart_5321230 := by decide
  rcases family_descends (prefixWord ++ tailWord_5321230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5321253 : List Nat := [1, 3, 1, 2, 2, 1, 5, 1, 3, 1, 3]
def baseStart_5321253 : Nat := 118140960795 + 5321253 * 2 ^ 59
def prefixEnd_5321253 : Nat := 4983230072969 + 3 ^ 40 * 5321253 * 2
def baseEnd_5321253 : Nat := 2732360473179374306865509

theorem tailTrace_5321253 : CollatzResearch.WordTrace tailWord_5321253 prefixEnd_5321253 2732360473179374306865509 := by
  unfold tailWord_5321253
  simp only [CollatzResearch.WordTrace]
  refine ⟨194082041391016653504432413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129388027594011102336288275 194082041391016653504432413)
  ·
    refine ⟨72780765521631245064162155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 194082041391016653504432413 72780765521631245064162155)
    ·
      refine ⟨109171148282446867596243233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72780765521631245064162155 109171148282446867596243233)
      ·
        refine ⟨81878361211835150697182425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109171148282446867596243233 81878361211835150697182425)
        ·
          refine ⟨61408770908876363022886819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81878361211835150697182425 61408770908876363022886819)
          ·
            refine ⟨92113156363314544534330229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61408770908876363022886819 92113156363314544534330229)
            ·
              refine ⟨8635608409060738550093459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 92113156363314544534330229 8635608409060738550093459)
              ·
                refine ⟨12953412613591107825140189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8635608409060738550093459 12953412613591107825140189)
                ·
                  refine ⟨4857529730096665434427571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12953412613591107825140189 4857529730096665434427571)
                  ·
                    refine ⟨7286294595144998151641357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4857529730096665434427571 7286294595144998151641357)
                    ·
                      refine ⟨2732360473179374306865509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7286294595144998151641357 2732360473179374306865509)
                      ·
                        rfl

theorem cell23_5321253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 1, 3, 1, 3].length) (baseStart_5321253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5321253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5321253 prefixEnd_5321253 := by exact prefixLift 5321253
  have htrace : WordTrace (prefixWord ++ tailWord_5321253) baseStart_5321253 baseEnd_5321253 := by
    simpa [prefixWord, tailWord_5321253, baseEnd_5321253] using wordTrace_append hprefix tailTrace_5321253
  have hstable : (prefixWord ++ tailWord_5321253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5321253).length < 2 ^ (prefixWord ++ tailWord_5321253).sum := by decide
  have hdescent : baseEnd_5321253 < baseStart_5321253 := by decide
  rcases family_descends (prefixWord ++ tailWord_5321253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5321303 : List Nat := [1, 1, 3, 2, 2, 2, 4, 2, 2, 4]
def baseStart_5321303 : Nat := 118140960795 + 5321303 * 2 ^ 59
def prefixEnd_5321303 : Nat := 4983230072969 + 3 ^ 40 * 5321303 * 2
def baseEnd_5321303 : Nat := 910795382404033037080093

theorem tailTrace_5321303 : CollatzResearch.WordTrace tailWord_5321303 prefixEnd_5321303 910795382404033037080093 := by
  unfold tailWord_5321303
  simp only [CollatzResearch.WordTrace]
  refine ⟨194083865040835512043752563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129389243360557008029168375 194083865040835512043752563)
  ·
    refine ⟨291125797561253268065628845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194083865040835512043752563 291125797561253268065628845)
    ·
      refine ⟨109172174085469975524610817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 291125797561253268065628845 109172174085469975524610817)
      ·
        refine ⟨81879130564102481643458113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109172174085469975524610817 81879130564102481643458113)
        ·
          refine ⟨61409347923076861232593585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81879130564102481643458113 61409347923076861232593585)
          ·
            refine ⟨46057010942307645924445189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61409347923076861232593585 46057010942307645924445189)
            ·
              refine ⟨8635689551682683610833473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46057010942307645924445189 8635689551682683610833473)
              ·
                refine ⟨6476767163762012708125105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8635689551682683610833473 6476767163762012708125105)
                ·
                  refine ⟨4857575372821509531093829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6476767163762012708125105 4857575372821509531093829)
                  ·
                    refine ⟨910795382404033037080093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4857575372821509531093829 910795382404033037080093)
                    ·
                      rfl

theorem cell23_5321303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 2, 2, 4].length) (baseStart_5321303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5321303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5321303 prefixEnd_5321303 := by exact prefixLift 5321303
  have htrace : WordTrace (prefixWord ++ tailWord_5321303) baseStart_5321303 baseEnd_5321303 := by
    simpa [prefixWord, tailWord_5321303, baseEnd_5321303] using wordTrace_append hprefix tailTrace_5321303
  have hstable : (prefixWord ++ tailWord_5321303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5321303).length < 2 ^ (prefixWord ++ tailWord_5321303).sum := by decide
  have hdescent : baseEnd_5321303 < baseStart_5321303 := by decide
  rcases family_descends (prefixWord ++ tailWord_5321303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5321359 : List Nat := [1, 1, 2, 1, 1, 1, 1, 4, 3, 8]
def baseStart_5321359 : Nat := 118140960795 + 5321359 * 2 ^ 59
def prefixEnd_5321359 : Nat := 4983230072969 + 3 ^ 40 * 5321359 * 2
def baseEnd_5321359 : Nat := 910804967376250297380007

theorem tailTrace_5321359 : CollatzResearch.WordTrace tailWord_5321359 prefixEnd_5321359 910804967376250297380007 := by
  unfold tailWord_5321359
  simp only [CollatzResearch.WordTrace]
  refine ⟨194085907528632633607791131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129390605019088422405194087 194085907528632633607791131)
  ·
    refine ⟨291128861292948950411686697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194085907528632633607791131 291128861292948950411686697)
    ·
      refine ⟨218346645969711712808765023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 291128861292948950411686697 218346645969711712808765023)
      ·
        refine ⟨327519968954567569213147535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218346645969711712808765023 327519968954567569213147535)
        ·
          refine ⟨491279953431851353819721303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 327519968954567569213147535 491279953431851353819721303)
          ·
            refine ⟨736919930147777030729581955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 491279953431851353819721303 736919930147777030729581955)
            ·
              refine ⟨1105379895221665546094372933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 736919930147777030729581955 1105379895221665546094372933)
              ·
                refine ⟨207258730354062289892694925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1105379895221665546094372933 207258730354062289892694925)
                ·
                  refine ⟨77722023882773358709760597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 207258730354062289892694925 77722023882773358709760597)
                  ·
                    refine ⟨910804967376250297380007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 77722023882773358709760597 910804967376250297380007)
                    ·
                      rfl

theorem cell23_5321359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 3, 8].length) (baseStart_5321359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5321359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5321359 prefixEnd_5321359 := by exact prefixLift 5321359
  have htrace : WordTrace (prefixWord ++ tailWord_5321359) baseStart_5321359 baseEnd_5321359 := by
    simpa [prefixWord, tailWord_5321359, baseEnd_5321359] using wordTrace_append hprefix tailTrace_5321359
  have hstable : (prefixWord ++ tailWord_5321359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5321359).length < 2 ^ (prefixWord ++ tailWord_5321359).sum := by decide
  have hdescent : baseEnd_5321359 < baseStart_5321359 := by decide
  rcases family_descends (prefixWord ++ tailWord_5321359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5321377 : List Nat := [1, 2, 3, 3, 4, 1, 1, 1, 1, 3, 3]
def baseStart_5321377 : Nat := 118140960795 + 5321377 * 2 ^ 59
def prefixEnd_5321377 : Nat := 4983230072969 + 3 ^ 40 * 5321377 * 2
def baseEnd_5321377 : Nat := 2732424144780531821714939

theorem tailTrace_5321377 : CollatzResearch.WordTrace tailWord_5321377 prefixEnd_5321377 2732424144780531821714939 := by
  unfold tailWord_5321377
  simp only [CollatzResearch.WordTrace]
  refine ⟨194086564042567422681946385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129391042695044948454630923 194086564042567422681946385)
  ·
    refine ⟨145564923031925567011459789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194086564042567422681946385 145564923031925567011459789)
    ·
      refine ⟨54586846136972087629297421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145564923031925567011459789 54586846136972087629297421)
      ·
        refine ⟨20470067301364532860986533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54586846136972087629297421 20470067301364532860986533)
        ·
          refine ⟨3838137619005849911434975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20470067301364532860986533 3838137619005849911434975)
          ·
            refine ⟨5757206428508774867152463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3838137619005849911434975 5757206428508774867152463)
            ·
              refine ⟨8635809642763162300728695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5757206428508774867152463 8635809642763162300728695)
              ·
                refine ⟨12953714464144743451093043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8635809642763162300728695 12953714464144743451093043)
                ·
                  refine ⟨19430571696217115176639565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12953714464144743451093043 19430571696217115176639565)
                  ·
                    refine ⟨7286464386081418191239837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19430571696217115176639565 7286464386081418191239837)
                    ·
                      refine ⟨2732424144780531821714939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7286464386081418191239837 2732424144780531821714939)
                      ·
                        rfl

theorem cell23_5321377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 1, 1, 3, 3].length) (baseStart_5321377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5321377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5321377 prefixEnd_5321377 := by exact prefixLift 5321377
  have htrace : WordTrace (prefixWord ++ tailWord_5321377) baseStart_5321377 baseEnd_5321377 := by
    simpa [prefixWord, tailWord_5321377, baseEnd_5321377] using wordTrace_append hprefix tailTrace_5321377
  have hstable : (prefixWord ++ tailWord_5321377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5321377).length < 2 ^ (prefixWord ++ tailWord_5321377).sum := by decide
  have hdescent : baseEnd_5321377 < baseStart_5321377 := by decide
  rcases family_descends (prefixWord ++ tailWord_5321377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5321470 : List Nat := [4, 2, 2, 1, 2, 1, 2, 2, 2, 5]
def baseStart_5321470 : Nat := 118140960795 + 5321470 * 2 ^ 59
def prefixEnd_5321470 : Nat := 4983230072969 + 3 ^ 40 * 5321470 * 2
def baseEnd_5321470 : Nat := 910823966160466652617337

theorem tailTrace_5321470 : CollatzResearch.WordTrace tailWord_5321470 prefixEnd_5321470 910823966160466652617337 := by
  unfold tailWord_5321470
  simp only [CollatzResearch.WordTrace]
  refine ⟨24261244503903812445635233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129393304020820333043387909 24261244503903812445635233)
  ·
    refine ⟨18195933377927859334226425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24261244503903812445635233 18195933377927859334226425)
    ·
      refine ⟨13646950033445894500669819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18195933377927859334226425 13646950033445894500669819)
      ·
        refine ⟨20470425050168841751004729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13646950033445894500669819 20470425050168841751004729)
        ·
          refine ⟨15352818787626631313253547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20470425050168841751004729 15352818787626631313253547)
          ·
            refine ⟨23029228181439946969880321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15352818787626631313253547 23029228181439946969880321)
            ·
              refine ⟨17271921136079960227410241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23029228181439946969880321 17271921136079960227410241)
              ·
                refine ⟨12953940852059970170557681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17271921136079960227410241 12953940852059970170557681)
                ·
                  refine ⟨9715455639044977627918261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12953940852059970170557681 9715455639044977627918261)
                  ·
                    refine ⟨910823966160466652617337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9715455639044977627918261 910823966160466652617337)
                    ·
                      rfl

theorem cell23_5321470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_5321470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5321470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5321470 prefixEnd_5321470 := by exact prefixLift 5321470
  have htrace : WordTrace (prefixWord ++ tailWord_5321470) baseStart_5321470 baseEnd_5321470 := by
    simpa [prefixWord, tailWord_5321470, baseEnd_5321470] using wordTrace_append hprefix tailTrace_5321470
  have hstable : (prefixWord ++ tailWord_5321470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5321470).length < 2 ^ (prefixWord ++ tailWord_5321470).sum := by decide
  have hdescent : baseEnd_5321470 < baseStart_5321470 := by decide
  rcases family_descends (prefixWord ++ tailWord_5321470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5321474 : List Nat := [3, 4, 1, 1, 1, 4, 2, 2, 5]
def baseStart_5321474 : Nat := 118140960795 + 5321474 * 2 ^ 59
def prefixEnd_5321474 : Nat := 4983230072969 + 3 ^ 40 * 5321474 * 2
def baseEnd_5321474 : Nat := 303608216933779771355777

theorem tailTrace_5321474 : CollatzResearch.WordTrace tailWord_5321474 prefixEnd_5321474 303608216933779771355777 := by
  unfold tailWord_5321474
  simp only [CollatzResearch.WordTrace]
  refine ⟨48522525480804002062056869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129393401282144005498818317 48522525480804002062056869)
  ·
    refine ⟨9097973527650750386635663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48522525480804002062056869 9097973527650750386635663)
    ·
      refine ⟨13646960291476125579953495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9097973527650750386635663 13646960291476125579953495)
      ·
        refine ⟨20470440437214188369930243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13646960291476125579953495 20470440437214188369930243)
        ·
          refine ⟨30705660655821282554895365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20470440437214188369930243 30705660655821282554895365)
          ·
            refine ⟨5757311372966490479042881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30705660655821282554895365 5757311372966490479042881)
            ·
              refine ⟨4317983529724867859282161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5757311372966490479042881 4317983529724867859282161)
              ·
                refine ⟨3238487647293650894461621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4317983529724867859282161 3238487647293650894461621)
                ·
                  refine ⟨303608216933779771355777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3238487647293650894461621 303608216933779771355777)
                  ·
                    rfl

theorem cell23_5321474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 2, 2, 5].length) (baseStart_5321474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5321474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5321474 prefixEnd_5321474 := by exact prefixLift 5321474
  have htrace : WordTrace (prefixWord ++ tailWord_5321474) baseStart_5321474 baseEnd_5321474 := by
    simpa [prefixWord, tailWord_5321474, baseEnd_5321474] using wordTrace_append hprefix tailTrace_5321474
  have hstable : (prefixWord ++ tailWord_5321474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5321474).length < 2 ^ (prefixWord ++ tailWord_5321474).sum := by decide
  have hdescent : baseEnd_5321474 < baseStart_5321474 := by decide
  rcases family_descends (prefixWord ++ tailWord_5321474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5321483 : List Nat := [1, 1, 1, 1, 5, 1, 1, 5, 3, 4]
def baseStart_5321483 : Nat := 118140960795 + 5321483 * 2 ^ 59
def prefixEnd_5321483 : Nat := 4983230072969 + 3 ^ 40 * 5321483 * 2
def baseEnd_5321483 : Nat := 910826191243302802329817

theorem tailTrace_5321483 : CollatzResearch.WordTrace tailWord_5321483 prefixEnd_5321483 910826191243302802329817 := by
  unfold tailWord_5321483
  simp only [CollatzResearch.WordTrace]
  refine ⟨194090430180183402785305103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129393620120122268523536735 194090430180183402785305103)
  ·
    refine ⟨291135645270275104177957655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194090430180183402785305103 291135645270275104177957655)
    ·
      refine ⟨436703467905412656266936483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 291135645270275104177957655 436703467905412656266936483)
      ·
        refine ⟨655055201858118984400404725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 436703467905412656266936483 655055201858118984400404725)
        ·
          refine ⟨61411425174198654787537943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 655055201858118984400404725 61411425174198654787537943)
          ·
            refine ⟨92117137761297982181306915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61411425174198654787537943 92117137761297982181306915)
            ·
              refine ⟨138175706641946973271960373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92117137761297982181306915 138175706641946973271960373)
              ·
                refine ⟨12953972497682528744246285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 138175706641946973271960373 12953972497682528744246285)
                ·
                  refine ⟨4857739686630948279092357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12953972497682528744246285 4857739686630948279092357)
                  ·
                    refine ⟨910826191243302802329817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4857739686630948279092357 910826191243302802329817)
                    ·
                      rfl

theorem cell23_5321483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 5, 3, 4].length) (baseStart_5321483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5321483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5321483 prefixEnd_5321483 := by exact prefixLift 5321483
  have htrace : WordTrace (prefixWord ++ tailWord_5321483) baseStart_5321483 baseEnd_5321483 := by
    simpa [prefixWord, tailWord_5321483, baseEnd_5321483] using wordTrace_append hprefix tailTrace_5321483
  have hstable : (prefixWord ++ tailWord_5321483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5321483).length < 2 ^ (prefixWord ++ tailWord_5321483).sum := by decide
  have hdescent : baseEnd_5321483 < baseStart_5321483 := by decide
  rcases family_descends (prefixWord ++ tailWord_5321483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5321493 : List Nat := [1, 3, 2, 1, 2, 2, 2, 2, 1, 4, 3]
def baseStart_5321493 : Nat := 118140960795 + 5321493 * 2 ^ 59
def prefixEnd_5321493 : Nat := 4983230072969 + 3 ^ 40 * 5321493 * 2
def baseEnd_5321493 : Nat := 2732483708536453367864405

theorem tailTrace_5321493 : CollatzResearch.WordTrace tailWord_5321493 prefixEnd_5321493 2732483708536453367864405 := by
  unfold tailWord_5321493
  simp only [CollatzResearch.WordTrace]
  refine ⟨194090794910147174493169133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129393863273431449662112755 194090794910147174493169133)
  ·
    refine ⟨72784048091305190434938425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 194090794910147174493169133 72784048091305190434938425)
    ·
      refine ⟨54588036068478892826203819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72784048091305190434938425 54588036068478892826203819)
      ·
        refine ⟨81882054102718339239305729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54588036068478892826203819 81882054102718339239305729)
        ·
          refine ⟨61411540577038754429479297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81882054102718339239305729 61411540577038754429479297)
          ·
            refine ⟨46058655432779065822109473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61411540577038754429479297 46058655432779065822109473)
            ·
              refine ⟨34543991574584299366582105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46058655432779065822109473 34543991574584299366582105)
              ·
                refine ⟨25907993680938224524936579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34543991574584299366582105 25907993680938224524936579)
                ·
                  refine ⟨38861990521407336787404869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25907993680938224524936579 38861990521407336787404869)
                  ·
                    refine ⟨7286623222763875647638413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38861990521407336787404869 7286623222763875647638413)
                    ·
                      refine ⟨2732483708536453367864405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7286623222763875647638413 2732483708536453367864405)
                      ·
                        rfl

theorem cell23_5321493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 2, 1, 4, 3].length) (baseStart_5321493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5321493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5321493 prefixEnd_5321493 := by exact prefixLift 5321493
  have htrace : WordTrace (prefixWord ++ tailWord_5321493) baseStart_5321493 baseEnd_5321493 := by
    simpa [prefixWord, tailWord_5321493, baseEnd_5321493] using wordTrace_append hprefix tailTrace_5321493
  have hstable : (prefixWord ++ tailWord_5321493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5321493).length < 2 ^ (prefixWord ++ tailWord_5321493).sum := by decide
  have hdescent : baseEnd_5321493 < baseStart_5321493 := by decide
  rcases family_descends (prefixWord ++ tailWord_5321493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5321496 : List Nat := [2, 1, 2, 3, 1, 1, 1, 2, 10]
def baseStart_5321496 : Nat := 118140960795 + 5321496 * 2 ^ 59
def prefixEnd_5321496 : Nat := 4983230072969 + 3 ^ 40 * 5321496 * 2
def baseEnd_5321496 : Nat := 303609472108712984014099

theorem tailTrace_5321496 : CollatzResearch.WordTrace tailWord_5321496 prefixEnd_5321496 303609472108712984014099 := by
  unfold tailWord_5321496
  simp only [CollatzResearch.WordTrace]
  refine ⟨97045452164568153002764171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129393936219424204003685561 97045452164568153002764171)
  ·
    refine ⟨145568178246852229504146257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97045452164568153002764171 145568178246852229504146257)
    ·
      refine ⟨109176133685139172128109693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145568178246852229504146257 109176133685139172128109693)
      ·
        refine ⟨40941050131927189548041135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109176133685139172128109693 40941050131927189548041135)
        ·
          refine ⟨61411575197890784322061703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40941050131927189548041135 61411575197890784322061703)
          ·
            refine ⟨92117362796836176483092555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61411575197890784322061703 92117362796836176483092555)
            ·
              refine ⟨138176044195254264724638833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92117362796836176483092555 138176044195254264724638833)
              ·
                refine ⟨103632033146440698543479125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 138176044195254264724638833 103632033146440698543479125)
                ·
                  refine ⟨303609472108712984014099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 103632033146440698543479125 303609472108712984014099)
                  ·
                    rfl

theorem cell23_5321496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 10].length) (baseStart_5321496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5321496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5321496 prefixEnd_5321496 := by exact prefixLift 5321496
  have htrace : WordTrace (prefixWord ++ tailWord_5321496) baseStart_5321496 baseEnd_5321496 := by
    simpa [prefixWord, tailWord_5321496, baseEnd_5321496] using wordTrace_append hprefix tailTrace_5321496
  have hstable : (prefixWord ++ tailWord_5321496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5321496).length < 2 ^ (prefixWord ++ tailWord_5321496).sum := by decide
  have hdescent : baseEnd_5321496 < baseStart_5321496 := by decide
  rcases family_descends (prefixWord ++ tailWord_5321496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5321500 : List Nat := [2, 2, 3, 1, 1, 4, 1, 2, 3, 4]
def baseStart_5321500 : Nat := 118140960795 + 5321500 * 2 ^ 59
def prefixEnd_5321500 : Nat := 4983230072969 + 3 ^ 40 * 5321500 * 2
def baseEnd_5321500 : Nat := 910829100967011613492291

theorem tailTrace_5321500 : CollatzResearch.WordTrace tailWord_5321500 prefixEnd_5321500 910829100967011613492291 := by
  unfold tailWord_5321500
  simp only [CollatzResearch.WordTrace]
  refine ⟨97045525110560907344336977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129394033480747876459115969 97045525110560907344336977)
  ·
    refine ⟨72784143832920680508252733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97045525110560907344336977 72784143832920680508252733)
    ·
      refine ⟨27294053937345255190594775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72784143832920680508252733 27294053937345255190594775)
      ·
        refine ⟨40941080906017882785892163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27294053937345255190594775 40941080906017882785892163)
        ·
          refine ⟨61411621359026824178838245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40941080906017882785892163 61411621359026824178838245)
          ·
            refine ⟨11514679004817529533532171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61411621359026824178838245 11514679004817529533532171)
            ·
              refine ⟨17272018507226294300298257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11514679004817529533532171 17272018507226294300298257)
              ·
                refine ⟨12954013880419720725223693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17272018507226294300298257 12954013880419720725223693)
                ·
                  refine ⟨4857755205157395271958885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12954013880419720725223693 4857755205157395271958885)
                  ·
                    refine ⟨910829100967011613492291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4857755205157395271958885 910829100967011613492291)
                    ·
                      rfl

theorem cell23_5321500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 2, 3, 4].length) (baseStart_5321500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5321500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5321500 prefixEnd_5321500 := by exact prefixLift 5321500
  have htrace : WordTrace (prefixWord ++ tailWord_5321500) baseStart_5321500 baseEnd_5321500 := by
    simpa [prefixWord, tailWord_5321500, baseEnd_5321500] using wordTrace_append hprefix tailTrace_5321500
  have hstable : (prefixWord ++ tailWord_5321500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5321500).length < 2 ^ (prefixWord ++ tailWord_5321500).sum := by decide
  have hdescent : baseEnd_5321500 < baseStart_5321500 := by decide
  rcases family_descends (prefixWord ++ tailWord_5321500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5321573 : List Nat := [1, 3, 1, 3, 1, 1, 2, 4, 1, 6]
def baseStart_5321573 : Nat := 118140960795 + 5321573 * 2 ^ 59
def prefixEnd_5321573 : Nat := 4983230072969 + 3 ^ 40 * 5321573 * 2
def baseEnd_5321573 : Nat := 910841595662937684954679

theorem tailTrace_5321573 : CollatzResearch.WordTrace tailWord_5321573 prefixEnd_5321573 910841595662937684954679 := by
  unfold tailWord_5321573
  simp only [CollatzResearch.WordTrace]
  refine ⟨194093712749857348156081373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129395808499904898770720915 194093712749857348156081373)
  ·
    refine ⟨72785142281196505558530515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 194093712749857348156081373 72785142281196505558530515)
    ·
      refine ⟨109177713421794758337795773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72785142281196505558530515 109177713421794758337795773)
      ·
        refine ⟨40941642533173034376673415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109177713421794758337795773 40941642533173034376673415)
        ·
          refine ⟨61412463799759551565010123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40941642533173034376673415 61412463799759551565010123)
          ·
            refine ⟨92118695699639327347515185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61412463799759551565010123 92118695699639327347515185)
            ·
              refine ⟨69089021774729495510636389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92118695699639327347515185 69089021774729495510636389)
              ·
                refine ⟨12954191582761780408244323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69089021774729495510636389 12954191582761780408244323)
                ·
                  refine ⟨19431287374142670612366485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12954191582761780408244323 19431287374142670612366485)
                  ·
                    refine ⟨910841595662937684954679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19431287374142670612366485 910841595662937684954679)
                    ·
                      rfl

theorem cell23_5321573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 4, 1, 6].length) (baseStart_5321573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5321573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5321573 prefixEnd_5321573 := by exact prefixLift 5321573
  have htrace : WordTrace (prefixWord ++ tailWord_5321573) baseStart_5321573 baseEnd_5321573 := by
    simpa [prefixWord, tailWord_5321573, baseEnd_5321573] using wordTrace_append hprefix tailTrace_5321573
  have hstable : (prefixWord ++ tailWord_5321573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5321573).length < 2 ^ (prefixWord ++ tailWord_5321573).sum := by decide
  have hdescent : baseEnd_5321573 < baseStart_5321573 := by decide
  rcases family_descends (prefixWord ++ tailWord_5321573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5321580 : List Nat := [2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 4]
def baseStart_5321580 : Nat := 118140960795 + 5321580 * 2 ^ 59
def prefixEnd_5321580 : Nat := 4983230072969 + 3 ^ 40 * 5321580 * 2
def baseEnd_5321580 : Nat := 2732528381353394527476505

theorem tailTrace_5321580 : CollatzResearch.WordTrace tailWord_5321580 prefixEnd_5321580 2732528381353394527476505 := by
  unfold tailWord_5321580
  simp only [CollatzResearch.WordTrace]
  refine ⟨97046984030415994175793097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129395978707221325567724129 97046984030415994175793097)
  ·
    refine ⟨72785238022811995631844823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97046984030415994175793097 72785238022811995631844823)
    ·
      refine ⟨109177857034217993447767235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72785238022811995631844823 109177857034217993447767235)
      ·
        refine ⟨163766785551326990171650853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109177857034217993447767235 163766785551326990171650853)
        ·
          refine ⟨30706272290873810657184535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 163766785551326990171650853 30706272290873810657184535)
          ·
            refine ⟨46059408436310715985776803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30706272290873810657184535 46059408436310715985776803)
            ·
              refine ⟨69089112654466073978665205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46059408436310715985776803 69089112654466073978665205)
              ·
                refine ⟨6477104311356194435499863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 69089112654466073978665205 6477104311356194435499863)
                ·
                  refine ⟨9715656467034291653249795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6477104311356194435499863 9715656467034291653249795)
                  ·
                    refine ⟨14573484700551437479874693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9715656467034291653249795 14573484700551437479874693)
                    ·
                      refine ⟨2732528381353394527476505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14573484700551437479874693 2732528381353394527476505)
                      ·
                        rfl

theorem cell23_5321580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 4].length) (baseStart_5321580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5321580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5321580 prefixEnd_5321580 := by exact prefixLift 5321580
  have htrace : WordTrace (prefixWord ++ tailWord_5321580) baseStart_5321580 baseEnd_5321580 := by
    simpa [prefixWord, tailWord_5321580, baseEnd_5321580] using wordTrace_append hprefix tailTrace_5321580
  have hstable : (prefixWord ++ tailWord_5321580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5321580).length < 2 ^ (prefixWord ++ tailWord_5321580).sum := by decide
  have hdescent : baseEnd_5321580 < baseStart_5321580 := by decide
  rcases family_descends (prefixWord ++ tailWord_5321580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5321593 : List Nat := [1, 2, 1, 3, 2, 3, 1, 2, 1, 1, 6]
def baseStart_5321593 : Nat := 118140960795 + 5321593 * 2 ^ 59
def prefixEnd_5321593 : Nat := 4983230072969 + 3 ^ 40 * 5321593 * 2
def baseEnd_5321593 : Nat := 2732535056601902976613945

theorem tailTrace_5321593 : CollatzResearch.WordTrace tailWord_5321593 prefixEnd_5321593 2732535056601902976613945 := by
  unfold tailWord_5321593
  simp only [CollatzResearch.WordTrace]
  refine ⟨194094442209784891571809433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129396294806523261047872955 194094442209784891571809433)
  ·
    refine ⟨145570831657338668678857075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194094442209784891571809433 145570831657338668678857075)
    ·
      refine ⟨218356247486008003018285613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145570831657338668678857075 218356247486008003018285613)
      ·
        refine ⟨81883592807253001131857105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 218356247486008003018285613 81883592807253001131857105)
        ·
          refine ⟨61412694605439750848892829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81883592807253001131857105 61412694605439750848892829)
          ·
            refine ⟨23029760477039906568334811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61412694605439750848892829 23029760477039906568334811)
            ·
              refine ⟨34544640715559859852502217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23029760477039906568334811 34544640715559859852502217)
              ·
                refine ⟨25908480536669894889376663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34544640715559859852502217 25908480536669894889376663)
                ·
                  refine ⟨38862720805004842334064995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25908480536669894889376663 38862720805004842334064995)
                  ·
                    refine ⟨58294081207507263501097493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38862720805004842334064995 58294081207507263501097493)
                    ·
                      refine ⟨2732535056601902976613945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58294081207507263501097493 2732535056601902976613945)
                      ·
                        rfl

theorem cell23_5321593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 2, 1, 1, 6].length) (baseStart_5321593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5321593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5321593 prefixEnd_5321593 := by exact prefixLift 5321593
  have htrace : WordTrace (prefixWord ++ tailWord_5321593) baseStart_5321593 baseEnd_5321593 := by
    simpa [prefixWord, tailWord_5321593, baseEnd_5321593] using wordTrace_append hprefix tailTrace_5321593
  have hstable : (prefixWord ++ tailWord_5321593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5321593).length < 2 ^ (prefixWord ++ tailWord_5321593).sum := by decide
  have hdescent : baseEnd_5321593 < baseStart_5321593 := by decide
  rcases family_descends (prefixWord ++ tailWord_5321593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5321603 : List Nat := [1, 1, 1, 3, 4, 1, 4, 8]
def baseStart_5321603 : Nat := 118140960795 + 5321603 * 2 ^ 59
def prefixEnd_5321603 : Nat := 4983230072969 + 3 ^ 40 * 5321603 * 2
def baseEnd_5321603 : Nat := 101205192274386960647737

theorem tailTrace_5321603 : CollatzResearch.WordTrace tailWord_5321603 prefixEnd_5321603 101205192274386960647737 := by
  unfold tailWord_5321603
  simp only [CollatzResearch.WordTrace]
  refine ⟨194094806939748663279673463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129396537959832442186448975 194094806939748663279673463)
  ·
    refine ⟨291142210409622994919510195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194094806939748663279673463 291142210409622994919510195)
    ·
      refine ⟨436713315614434492379265293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 291142210409622994919510195 436713315614434492379265293)
      ·
        refine ⟨163767493355412934642224485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 436713315614434492379265293 163767493355412934642224485)
        ·
          refine ⟨30706405004139925245417091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 163767493355412934642224485 30706405004139925245417091)
          ·
            refine ⟨46059607506209887868125637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30706405004139925245417091 46059607506209887868125637)
            ·
              refine ⟨8636176407414353975273557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46059607506209887868125637 8636176407414353975273557)
              ·
                refine ⟨101205192274386960647737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8636176407414353975273557 101205192274386960647737)
                ·
                  rfl

theorem cell23_5321603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 8].length) (baseStart_5321603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5321603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5321603 prefixEnd_5321603 := by exact prefixLift 5321603
  have htrace : WordTrace (prefixWord ++ tailWord_5321603) baseStart_5321603 baseEnd_5321603 := by
    simpa [prefixWord, tailWord_5321603, baseEnd_5321603] using wordTrace_append hprefix tailTrace_5321603
  have hstable : (prefixWord ++ tailWord_5321603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5321603).length < 2 ^ (prefixWord ++ tailWord_5321603).sum := by decide
  have hdescent : baseEnd_5321603 < baseStart_5321603 := by decide
  rcases family_descends (prefixWord ++ tailWord_5321603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5321607 : List Nat := [1, 1, 4, 2, 3, 2, 1, 3, 2, 4]
def baseStart_5321607 : Nat := 118140960795 + 5321607 * 2 ^ 59
def prefixEnd_5321607 : Nat := 4983230072969 + 3 ^ 40 * 5321607 * 2
def baseEnd_5321607 : Nat := 910847415110355307279627

theorem tailTrace_5321607 : CollatzResearch.WordTrace tailWord_5321607 prefixEnd_5321607 910847415110355307279627 := by
  unfold tailWord_5321607
  simp only [CollatzResearch.WordTrace]
  refine ⟨194094952831734171962819075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129396635221156114641879383 194094952831734171962819075)
  ·
    refine ⟨291142429247601257944228613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194094952831734171962819075 291142429247601257944228613)
    ·
      refine ⟨54589205483925235864542865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 291142429247601257944228613 54589205483925235864542865)
      ·
        refine ⟨40941904112943926898407149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54589205483925235864542865 40941904112943926898407149)
        ·
          refine ⟨15353214042353972586902681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40941904112943926898407149 15353214042353972586902681)
          ·
            refine ⟨11514910531765479440177011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15353214042353972586902681 11514910531765479440177011)
            ·
              refine ⟨17272365797648219160265517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11514910531765479440177011 17272365797648219160265517)
              ·
                refine ⟨6477137174118082185099569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17272365797648219160265517 6477137174118082185099569)
                ·
                  refine ⟨4857852880588561638824677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6477137174118082185099569 4857852880588561638824677)
                  ·
                    refine ⟨910847415110355307279627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4857852880588561638824677 910847415110355307279627)
                    ·
                      rfl

theorem cell23_5321607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 3, 2, 4].length) (baseStart_5321607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5321607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5321607 prefixEnd_5321607 := by exact prefixLift 5321607
  have htrace : WordTrace (prefixWord ++ tailWord_5321607) baseStart_5321607 baseEnd_5321607 := by
    simpa [prefixWord, tailWord_5321607, baseEnd_5321607] using wordTrace_append hprefix tailTrace_5321607
  have hstable : (prefixWord ++ tailWord_5321607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5321607).length < 2 ^ (prefixWord ++ tailWord_5321607).sum := by decide
  have hdescent : baseEnd_5321607 < baseStart_5321607 := by decide
  rcases family_descends (prefixWord ++ tailWord_5321607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5321610 : List Nat := [3, 1, 2, 4, 1, 1, 2, 1, 1, 1, 6]
def baseStart_5321610 : Nat := 118140960795 + 5321610 * 2 ^ 59
def prefixEnd_5321610 : Nat := 4983230072969 + 3 ^ 40 * 5321610 * 2
def baseEnd_5321610 : Nat := 2732543785773029410101367

theorem tailTrace_5321610 : CollatzResearch.WordTrace tailWord_5321610 prefixEnd_5321610 2732543785773029410101367 := by
  unfold tailWord_5321610
  simp only [CollatzResearch.WordTrace]
  refine ⟨48523765562680825868794571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129396708167148868983452189 48523765562680825868794571)
  ·
    refine ⟨72785648344021238803191857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48523765562680825868794571 72785648344021238803191857)
    ·
      refine ⟨54589236258015929102393893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72785648344021238803191857 54589236258015929102393893)
      ·
        refine ⟨10235481798377986706698855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54589236258015929102393893 10235481798377986706698855)
        ·
          refine ⟨15353222697566980060048283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10235481798377986706698855 15353222697566980060048283)
          ·
            refine ⟨23029834046350470090072425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15353222697566980060048283 23029834046350470090072425)
            ·
              refine ⟨17272375534762852567554319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23029834046350470090072425 17272375534762852567554319)
              ·
                refine ⟨25908563302144278851331479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17272375534762852567554319 25908563302144278851331479)
                ·
                  refine ⟨38862844953216418276997219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25908563302144278851331479 38862844953216418276997219)
                  ·
                    refine ⟨58294267429824627415495829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38862844953216418276997219 58294267429824627415495829)
                    ·
                      refine ⟨2732543785773029410101367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58294267429824627415495829 2732543785773029410101367)
                      ·
                        rfl

theorem cell23_5321610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_5321610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5321610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5321610 prefixEnd_5321610 := by exact prefixLift 5321610
  have htrace : WordTrace (prefixWord ++ tailWord_5321610) baseStart_5321610 baseEnd_5321610 := by
    simpa [prefixWord, tailWord_5321610, baseEnd_5321610] using wordTrace_append hprefix tailTrace_5321610
  have hstable : (prefixWord ++ tailWord_5321610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5321610).length < 2 ^ (prefixWord ++ tailWord_5321610).sum := by decide
  have hdescent : baseEnd_5321610 < baseStart_5321610 := by decide
  rcases family_descends (prefixWord ++ tailWord_5321610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5321657 : List Nat := [1, 2, 1, 4, 2, 2, 1, 2, 3, 3, 2]
def baseStart_5321657 : Nat := 118140960795 + 5321657 * 2 ^ 59
def prefixEnd_5321657 : Nat := 4983230072969 + 3 ^ 40 * 5321657 * 2
def baseEnd_5321657 : Nat := 2732567919363790726213651

theorem tailTrace_5321657 : CollatzResearch.WordTrace tailWord_5321657 prefixEnd_5321657 2732567919363790726213651 := by
  unfold tailWord_5321657
  simp only [CollatzResearch.WordTrace]
  refine ⟨194096776481553030502139225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129397850987702020334759483 194096776481553030502139225)
  ·
    refine ⟨145572582361164772876604419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194096776481553030502139225 145572582361164772876604419)
    ·
      refine ⟨218358873541747159314906629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145572582361164772876604419 218358873541747159314906629)
      ·
        refine ⟨40942288789077592371544993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 218358873541747159314906629 40942288789077592371544993)
        ·
          refine ⟨30706716591808194278658745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40942288789077592371544993 30706716591808194278658745)
          ·
            refine ⟨23030037443856145708994059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30706716591808194278658745 23030037443856145708994059)
            ·
              refine ⟨34545056165784218563491089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23030037443856145708994059 34545056165784218563491089)
              ·
                refine ⟨25908792124338163922618317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34545056165784218563491089 25908792124338163922618317)
                ·
                  refine ⟨9715797046626811470981869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25908792124338163922618317 9715797046626811470981869)
                  ·
                    refine ⟨3643423892485054301618201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9715797046626811470981869 3643423892485054301618201)
                    ·
                      refine ⟨2732567919363790726213651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3643423892485054301618201 2732567919363790726213651)
                      ·
                        rfl

theorem cell23_5321657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 2, 3, 3, 2].length) (baseStart_5321657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5321657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5321657 prefixEnd_5321657 := by exact prefixLift 5321657
  have htrace : WordTrace (prefixWord ++ tailWord_5321657) baseStart_5321657 baseEnd_5321657 := by
    simpa [prefixWord, tailWord_5321657, baseEnd_5321657] using wordTrace_append hprefix tailTrace_5321657
  have hstable : (prefixWord ++ tailWord_5321657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5321657).length < 2 ^ (prefixWord ++ tailWord_5321657).sum := by decide
  have hdescent : baseEnd_5321657 < baseStart_5321657 := by decide
  rcases family_descends (prefixWord ++ tailWord_5321657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5321698 : List Nat := [3, 3, 3, 1, 1, 3, 1, 2, 2, 1, 3]
def baseStart_5321698 : Nat := 118140960795 + 5321698 * 2 ^ 59
def prefixEnd_5321698 : Nat := 4983230072969 + 3 ^ 40 * 5321698 * 2
def baseEnd_5321698 : Nat := 2732588972070625065800963

theorem tailTrace_5321698 : CollatzResearch.WordTrace tailWord_5321698 prefixEnd_5321698 2732588972070625065800963 := by
  unfold tailWord_5321698
  simp only [CollatzResearch.WordTrace]
  refine ⟨48524567968601123626095437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129398847916269663002921165 48524567968601123626095437)
  ·
    refine ⟨18196712988225421359785789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48524567968601123626095437 18196712988225421359785789)
    ·
      refine ⟨6823767370584533009919671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18196712988225421359785789 6823767370584533009919671)
      ·
        refine ⟨10235651055876799514879507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6823767370584533009919671 10235651055876799514879507)
        ·
          refine ⟨15353476583815199272319261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10235651055876799514879507 15353476583815199272319261)
          ·
            refine ⟨5757553718930699727119723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15353476583815199272319261 5757553718930699727119723)
            ·
              refine ⟨8636330578396049590679585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5757553718930699727119723 8636330578396049590679585)
              ·
                refine ⟨6477247933797037193009689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8636330578396049590679585 6477247933797037193009689)
                ·
                  refine ⟨4857935950347777894757267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6477247933797037193009689 4857935950347777894757267)
                  ·
                    refine ⟨7286903925521666842135901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4857935950347777894757267 7286903925521666842135901)
                    ·
                      refine ⟨2732588972070625065800963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7286903925521666842135901 2732588972070625065800963)
                      ·
                        rfl

theorem cell23_5321698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_5321698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5321698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5321698 prefixEnd_5321698 := by exact prefixLift 5321698
  have htrace : WordTrace (prefixWord ++ tailWord_5321698) baseStart_5321698 baseEnd_5321698 := by
    simpa [prefixWord, tailWord_5321698, baseEnd_5321698] using wordTrace_append hprefix tailTrace_5321698
  have hstable : (prefixWord ++ tailWord_5321698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5321698).length < 2 ^ (prefixWord ++ tailWord_5321698).sum := by decide
  have hdescent : baseEnd_5321698 < baseStart_5321698 := by decide
  rcases family_descends (prefixWord ++ tailWord_5321698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5321721 : List Nat := [1, 2, 1, 3, 1, 3, 5, 1, 2, 2, 2]
def baseStart_5321721 : Nat := 118140960795 + 5321721 * 2 ^ 59
def prefixEnd_5321721 : Nat := 4983230072969 + 3 ^ 40 * 5321721 * 2
def baseEnd_5321721 : Nat := 2732600782125678475813357

theorem tailTrace_5321721 : CollatzResearch.WordTrace tailWord_5321721 prefixEnd_5321721 2732600782125678475813357 := by
  unfold tailWord_5321721
  simp only [CollatzResearch.WordTrace]
  refine ⟨194099110753321169432469017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129399407168880779621646011 194099110753321169432469017)
  ·
    refine ⟨145574333064990877074351763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194099110753321169432469017 145574333064990877074351763)
    ·
      refine ⟨218361499597486315611527645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145574333064990877074351763 218361499597486315611527645)
      ·
        refine ⟨81885562349057368354322867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 218361499597486315611527645 81885562349057368354322867)
        ·
          refine ⟨122828343523586052531484301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81885562349057368354322867 122828343523586052531484301)
          ·
            refine ⟨46060628821344769699306613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 122828343523586052531484301 46060628821344769699306613)
            ·
              refine ⟨4318183952001072159309995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46060628821344769699306613 4318183952001072159309995)
              ·
                refine ⟨6477275928001608238964993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4318183952001072159309995 6477275928001608238964993)
                ·
                  refine ⟨4857956946001206179223745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6477275928001608238964993 4857956946001206179223745)
                  ·
                    refine ⟨3643467709500904634417809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4857956946001206179223745 3643467709500904634417809)
                    ·
                      refine ⟨2732600782125678475813357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3643467709500904634417809 2732600782125678475813357)
                      ·
                        rfl

theorem cell23_5321721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 5, 1, 2, 2, 2].length) (baseStart_5321721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5321721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5321721 prefixEnd_5321721 := by exact prefixLift 5321721
  have htrace : WordTrace (prefixWord ++ tailWord_5321721) baseStart_5321721 baseEnd_5321721 := by
    simpa [prefixWord, tailWord_5321721, baseEnd_5321721] using wordTrace_append hprefix tailTrace_5321721
  have hstable : (prefixWord ++ tailWord_5321721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5321721).length < 2 ^ (prefixWord ++ tailWord_5321721).sum := by decide
  have hdescent : baseEnd_5321721 < baseStart_5321721 := by decide
  rcases family_descends (prefixWord ++ tailWord_5321721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5321740 : List Nat := [2, 2, 1, 2, 3, 2, 2, 1, 1, 7]
def baseStart_5321740 : Nat := 118140960795 + 5321740 * 2 ^ 59
def prefixEnd_5321740 : Nat := 4983230072969 + 3 ^ 40 * 5321740 * 2
def baseEnd_5321740 : Nat := 910870179419371300491923

theorem tailTrace_5321740 : CollatzResearch.WordTrace tailWord_5321740 prefixEnd_5321740 910870179419371300491923 := by
  unfold tailWord_5321740
  simp only [CollatzResearch.WordTrace]
  refine ⟨97049901870126167838705337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129399869160168223784940449 97049901870126167838705337)
  ·
    refine ⟨72787426402594625879029003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97049901870126167838705337 72787426402594625879029003)
    ·
      refine ⟨109181139603891938818543505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72787426402594625879029003 109181139603891938818543505)
      ·
        refine ⟨81885854702918954113907629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109181139603891938818543505 81885854702918954113907629)
        ·
          refine ⟨30707195513594607792715361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81885854702918954113907629 30707195513594607792715361)
          ·
            refine ⟨23030396635195955844536521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30707195513594607792715361 23030396635195955844536521)
            ·
              refine ⟨17272797476396966883402391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23030396635195955844536521 17272797476396966883402391)
              ·
                refine ⟨25909196214595450325103587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17272797476396966883402391 25909196214595450325103587)
                ·
                  refine ⟨38863794321893175487655381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25909196214595450325103587 38863794321893175487655381)
                  ·
                    refine ⟨910870179419371300491923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38863794321893175487655381 910870179419371300491923)
                    ·
                      rfl

theorem cell23_5321740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 1, 1, 7].length) (baseStart_5321740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5321740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5321740 prefixEnd_5321740 := by exact prefixLift 5321740
  have htrace : WordTrace (prefixWord ++ tailWord_5321740) baseStart_5321740 baseEnd_5321740 := by
    simpa [prefixWord, tailWord_5321740, baseEnd_5321740] using wordTrace_append hprefix tailTrace_5321740
  have hstable : (prefixWord ++ tailWord_5321740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5321740).length < 2 ^ (prefixWord ++ tailWord_5321740).sum := by decide
  have hdescent : baseEnd_5321740 < baseStart_5321740 := by decide
  rcases family_descends (prefixWord ++ tailWord_5321740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5321767 : List Nat := [1, 1, 7, 1, 1, 1, 1, 1, 1, 1, 7]
def baseStart_5321767 : Nat := 118140960795 + 5321767 * 2 ^ 59
def prefixEnd_5321767 : Nat := 4983230072969 + 3 ^ 40 * 5321767 * 2
def baseEnd_5321767 : Nat := 2732624402235785295838145

theorem tailTrace_5321767 : CollatzResearch.WordTrace tailWord_5321767 prefixEnd_5321767 2732624402235785295838145 := by
  unfold tailWord_5321767
  simp only [CollatzResearch.WordTrace]
  refine ⟨194100788511154519288643555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129400525674103012859095703 194100788511154519288643555)
  ·
    refine ⟨291151182766731778932965333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194100788511154519288643555 291151182766731778932965333)
    ·
      refine ⟨6823855846095276068741375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 291151182766731778932965333 6823855846095276068741375)
      ·
        refine ⟨10235783769142914103112063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6823855846095276068741375 10235783769142914103112063)
        ·
          refine ⟨15353675653714371154668095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10235783769142914103112063 15353675653714371154668095)
          ·
            refine ⟨23030513480571556732002143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15353675653714371154668095 23030513480571556732002143)
            ·
              refine ⟨34545770220857335098003215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23030513480571556732002143 34545770220857335098003215)
              ·
                refine ⟨51818655331286002647004823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34545770220857335098003215 51818655331286002647004823)
                ·
                  refine ⟨77727982996929003970507235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51818655331286002647004823 77727982996929003970507235)
                  ·
                    refine ⟨116591974495393505955760853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 77727982996929003970507235 116591974495393505955760853)
                    ·
                      refine ⟨2732624402235785295838145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 116591974495393505955760853 2732624402235785295838145)
                      ·
                        rfl

theorem cell23_5321767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_5321767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5321767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5321767 prefixEnd_5321767 := by exact prefixLift 5321767
  have htrace : WordTrace (prefixWord ++ tailWord_5321767) baseStart_5321767 baseEnd_5321767 := by
    simpa [prefixWord, tailWord_5321767, baseEnd_5321767] using wordTrace_append hprefix tailTrace_5321767
  have hstable : (prefixWord ++ tailWord_5321767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5321767).length < 2 ^ (prefixWord ++ tailWord_5321767).sum := by decide
  have hdescent : baseEnd_5321767 < baseStart_5321767 := by decide
  rcases family_descends (prefixWord ++ tailWord_5321767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5321777 : List Nat := [1, 2, 2, 3, 1, 2, 2, 1, 1, 6, 2]
def baseStart_5321777 : Nat := 118140960795 + 5321777 * 2 ^ 59
def prefixEnd_5321777 : Nat := 4983230072969 + 3 ^ 40 * 5321777 * 2
def baseEnd_5321777 : Nat := 2732629537042330256713099

theorem tailTrace_5321777 : CollatzResearch.WordTrace tailWord_5321777 prefixEnd_5321777 2732629537042330256713099 := by
  unfold tailWord_5321777
  simp only [CollatzResearch.WordTrace]
  refine ⟨194101153241118290996507585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129400768827412193997671723 194101153241118290996507585)
  ·
    refine ⟨145575864930838718247380689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194101153241118290996507585 145575864930838718247380689)
    ·
      refine ⟨109181898698129038685535517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145575864930838718247380689 109181898698129038685535517)
      ·
        refine ⟨40943212011798389507075819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109181898698129038685535517 40943212011798389507075819)
        ·
          refine ⟨61414818017697584260613729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40943212011798389507075819 61414818017697584260613729)
          ·
            refine ⟨46061113513273188195460297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61414818017697584260613729 46061113513273188195460297)
            ·
              refine ⟨34545835134954891146595223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46061113513273188195460297 34545835134954891146595223)
              ·
                refine ⟨51818752702432336719892835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34545835134954891146595223 51818752702432336719892835)
                ·
                  refine ⟨77728129053648505079839253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51818752702432336719892835 77728129053648505079839253)
                  ·
                    refine ⟨3643506049389773675617465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 77728129053648505079839253 3643506049389773675617465)
                    ·
                      refine ⟨2732629537042330256713099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3643506049389773675617465 2732629537042330256713099)
                      ·
                        rfl

theorem cell23_5321777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 1, 1, 6, 2].length) (baseStart_5321777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5321777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5321777 prefixEnd_5321777 := by exact prefixLift 5321777
  have htrace : WordTrace (prefixWord ++ tailWord_5321777) baseStart_5321777 baseEnd_5321777 := by
    simpa [prefixWord, tailWord_5321777, baseEnd_5321777] using wordTrace_append hprefix tailTrace_5321777
  have hstable : (prefixWord ++ tailWord_5321777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5321777).length < 2 ^ (prefixWord ++ tailWord_5321777).sum := by decide
  have hdescent : baseEnd_5321777 < baseStart_5321777 := by decide
  rcases family_descends (prefixWord ++ tailWord_5321777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5321797 : List Nat := [1, 3, 1, 1, 1, 3, 3, 3, 2, 2, 3]
def baseStart_5321797 : Nat := 118140960795 + 5321797 * 2 ^ 59
def prefixEnd_5321797 : Nat := 4983230072969 + 3 ^ 40 * 5321797 * 2
def baseEnd_5321797 : Nat := 2732639806655420178463007

theorem tailTrace_5321797 : CollatzResearch.WordTrace tailWord_5321797 prefixEnd_5321797 2732639806655420178463007 := by
  unfold tailWord_5321797
  simp only [CollatzResearch.WordTrace]
  refine ⟨194101882701045834412235645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129401255134030556274823763 194101882701045834412235645)
  ·
    refine ⟨72788206012892187904588367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 194101882701045834412235645 72788206012892187904588367)
    ·
      refine ⟨109182309019338281856882551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72788206012892187904588367 109182309019338281856882551)
      ·
        refine ⟨163773463529007422785323827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109182309019338281856882551 163773463529007422785323827)
        ·
          refine ⟨245660195293511134177985741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163773463529007422785323827 245660195293511134177985741)
          ·
            refine ⟨92122573235066675316744653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 245660195293511134177985741 92122573235066675316744653)
            ·
              refine ⟨34545964963150003243779245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92122573235066675316744653 34545964963150003243779245)
              ·
                refine ⟨12954736861181251216417217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34545964963150003243779245 12954736861181251216417217)
                ·
                  refine ⟨9716052645885938412312913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12954736861181251216417217 9716052645885938412312913)
                  ·
                    refine ⟨7287039484414453809234685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9716052645885938412312913 7287039484414453809234685)
                    ·
                      refine ⟨2732639806655420178463007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7287039484414453809234685 2732639806655420178463007)
                      ·
                        rfl

theorem cell23_5321797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 3, 2, 2, 3].length) (baseStart_5321797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5321797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5321797 prefixEnd_5321797 := by exact prefixLift 5321797
  have htrace : WordTrace (prefixWord ++ tailWord_5321797) baseStart_5321797 baseEnd_5321797 := by
    simpa [prefixWord, tailWord_5321797, baseEnd_5321797] using wordTrace_append hprefix tailTrace_5321797
  have hstable : (prefixWord ++ tailWord_5321797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5321797).length < 2 ^ (prefixWord ++ tailWord_5321797).sum := by decide
  have hdescent : baseEnd_5321797 < baseStart_5321797 := by decide
  rcases family_descends (prefixWord ++ tailWord_5321797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5321804 : List Nat := [2, 2, 1, 3, 1, 1, 1, 7, 1, 4]
def baseStart_5321804 : Nat := 118140960795 + 5321804 * 2 ^ 59
def prefixEnd_5321804 : Nat := 4983230072969 + 3 ^ 40 * 5321804 * 2
def baseEnd_5321804 : Nat := 910881133673333883691825

theorem tailTrace_5321804 : CollatzResearch.WordTrace tailWord_5321804 prefixEnd_5321804 910881133673333883691825 := by
  unfold tailWord_5321804
  simp only [CollatzResearch.WordTrace]
  refine ⟨97051069006010237303870233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129401425341346983071826977 97051069006010237303870233)
  ·
    refine ⟨72788301754507677977902675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97051069006010237303870233 72788301754507677977902675)
    ·
      refine ⟨109182452631761516966854013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72788301754507677977902675 109182452631761516966854013)
      ·
        refine ⟨40943419736910568862570255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109182452631761516966854013 40943419736910568862570255)
        ·
          refine ⟨61415129605365853293855383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40943419736910568862570255 61415129605365853293855383)
          ·
            refine ⟨92122694408048779940783075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61415129605365853293855383 92122694408048779940783075)
            ·
              refine ⟨138184041612073169911174613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92122694408048779940783075 138184041612073169911174613)
              ·
                refine ⟨3238688475282964919793155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 138184041612073169911174613 3238688475282964919793155)
                ·
                  refine ⟨4858032712924447379689733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3238688475282964919793155 4858032712924447379689733)
                  ·
                    refine ⟨910881133673333883691825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4858032712924447379689733 910881133673333883691825)
                    ·
                      rfl

theorem cell23_5321804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 7, 1, 4].length) (baseStart_5321804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5321804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5321804 prefixEnd_5321804 := by exact prefixLift 5321804
  have htrace : WordTrace (prefixWord ++ tailWord_5321804) baseStart_5321804 baseEnd_5321804 := by
    simpa [prefixWord, tailWord_5321804, baseEnd_5321804] using wordTrace_append hprefix tailTrace_5321804
  have hstable : (prefixWord ++ tailWord_5321804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5321804).length < 2 ^ (prefixWord ++ tailWord_5321804).sum := by decide
  have hdescent : baseEnd_5321804 < baseStart_5321804 := by decide
  rcases family_descends (prefixWord ++ tailWord_5321804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5321840 : List Nat := [2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 7]
def baseStart_5321840 : Nat := 118140960795 + 5321840 * 2 ^ 59
def prefixEnd_5321840 : Nat := 4983230072969 + 3 ^ 40 * 5321840 * 2
def baseEnd_5321840 : Nat := 2732661886323563510225309

theorem tailTrace_5321840 : CollatzResearch.WordTrace tailWord_5321840 prefixEnd_5321840 2732661886323563510225309 := by
  unfold tailWord_5321840
  simp only [CollatzResearch.WordTrace]
  refine ⟨97051725519945026378025487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129402300693260035170700649 97051725519945026378025487)
  ·
    refine ⟨145577588279917539567038231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97051725519945026378025487 145577588279917539567038231)
    ·
      refine ⟨218366382419876309350557347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145577588279917539567038231 218366382419876309350557347)
      ·
        refine ⟨327549573629814464025836021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218366382419876309350557347 327549573629814464025836021)
        ·
          refine ⟨30707772527795106002422127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 327549573629814464025836021 30707772527795106002422127)
          ·
            refine ⟨46061658791692659003633191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30707772527795106002422127 46061658791692659003633191)
            ·
              refine ⟨69092488187538988505449787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46061658791692659003633191 69092488187538988505449787)
              ·
                refine ⟨103638732281308482758174681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69092488187538988505449787 103638732281308482758174681)
                ·
                  refine ⟨77729049210981362068631011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 103638732281308482758174681 77729049210981362068631011)
                  ·
                    refine ⟨116593573816472043102946517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 77729049210981362068631011 116593573816472043102946517)
                    ·
                      refine ⟨2732661886323563510225309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 116593573816472043102946517 2732661886323563510225309)
                      ·
                        rfl

theorem cell23_5321840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 7].length) (baseStart_5321840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5321840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5321840 prefixEnd_5321840 := by exact prefixLift 5321840
  have htrace : WordTrace (prefixWord ++ tailWord_5321840) baseStart_5321840 baseEnd_5321840 := by
    simpa [prefixWord, tailWord_5321840, baseEnd_5321840] using wordTrace_append hprefix tailTrace_5321840
  have hstable : (prefixWord ++ tailWord_5321840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5321840).length < 2 ^ (prefixWord ++ tailWord_5321840).sum := by decide
  have hdescent : baseEnd_5321840 < baseStart_5321840 := by decide
  rcases family_descends (prefixWord ++ tailWord_5321840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5321847 : List Nat := [1, 1, 3, 1, 1, 4, 2, 4, 1, 5]
def baseStart_5321847 : Nat := 118140960795 + 5321847 * 2 ^ 59
def prefixEnd_5321847 : Nat := 4983230072969 + 3 ^ 40 * 5321847 * 2
def baseEnd_5321847 : Nat := 910888493562714994279259

theorem tailTrace_5321847 : CollatzResearch.WordTrace tailWord_5321847 prefixEnd_5321847 910888493562714994279259 := by
  unfold tailWord_5321847
  simp only [CollatzResearch.WordTrace]
  refine ⟨194103706350864692951555795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129402470900576461967703863 194103706350864692951555795)
  ·
    refine ⟨291155559526297039427333693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194103706350864692951555795 291155559526297039427333693)
    ·
      refine ⟨109183334822361389785250135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 291155559526297039427333693 109183334822361389785250135)
      ·
        refine ⟨163775002233542084677875203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109183334822361389785250135 163775002233542084677875203)
        ·
          refine ⟨245662503350313127016812805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163775002233542084677875203 245662503350313127016812805)
          ·
            refine ⟨46061719378183711315652401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 245662503350313127016812805 46061719378183711315652401)
            ·
              refine ⟨34546289533637783486739301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46061719378183711315652401 34546289533637783486739301)
              ·
                refine ⟨6477429287557084403763619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34546289533637783486739301 6477429287557084403763619)
                ·
                  refine ⟨9716143931335626605645429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6477429287557084403763619 9716143931335626605645429)
                  ·
                    refine ⟨910888493562714994279259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9716143931335626605645429 910888493562714994279259)
                    ·
                      rfl

theorem cell23_5321847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 4, 1, 5].length) (baseStart_5321847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5321847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5321847 prefixEnd_5321847 := by exact prefixLift 5321847
  have htrace : WordTrace (prefixWord ++ tailWord_5321847) baseStart_5321847 baseEnd_5321847 := by
    simpa [prefixWord, tailWord_5321847, baseEnd_5321847] using wordTrace_append hprefix tailTrace_5321847
  have hstable : (prefixWord ++ tailWord_5321847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5321847).length < 2 ^ (prefixWord ++ tailWord_5321847).sum := by decide
  have hdescent : baseEnd_5321847 < baseStart_5321847 := by decide
  rcases family_descends (prefixWord ++ tailWord_5321847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5321867 : List Nat := [1, 1, 1, 1, 4, 1, 1, 2, 1, 8, 2]
def baseStart_5321867 : Nat := 118140960795 + 5321867 * 2 ^ 59
def prefixEnd_5321867 : Nat := 4983230072969 + 3 ^ 40 * 5321867 * 2
def baseEnd_5321867 : Nat := 2732675750301234904587685

theorem tailTrace_5321867 : CollatzResearch.WordTrace tailWord_5321867 prefixEnd_5321867 2732675750301234904587685 := by
  unfold tailWord_5321867
  simp only [CollatzResearch.WordTrace]
  refine ⟨194104435810792236367283855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129402957207194824244855903 194104435810792236367283855)
  ·
    refine ⟨291156653716188354550925783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194104435810792236367283855 291156653716188354550925783)
    ·
      refine ⟨436734980574282531826388675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 291156653716188354550925783 436734980574282531826388675)
      ·
        refine ⟨655102470861423797739583013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 436734980574282531826388675 655102470861423797739583013)
        ·
          refine ⟨122831713286516962076171815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 655102470861423797739583013 122831713286516962076171815)
          ·
            refine ⟨184247569929775443114257723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122831713286516962076171815 184247569929775443114257723)
            ·
              refine ⟨276371354894663164671386585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 184247569929775443114257723 276371354894663164671386585)
              ·
                refine ⟨207278516170997373503539939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 276371354894663164671386585 207278516170997373503539939)
                ·
                  refine ⟨310917774256496060255309909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 207278516170997373503539939 310917774256496060255309909)
                  ·
                    refine ⟨3643567667068313206116913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 310917774256496060255309909 3643567667068313206116913)
                    ·
                      refine ⟨2732675750301234904587685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3643567667068313206116913 2732675750301234904587685)
                      ·
                        rfl

theorem cell23_5321867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 8, 2].length) (baseStart_5321867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5321867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5321867 prefixEnd_5321867 := by exact prefixLift 5321867
  have htrace : WordTrace (prefixWord ++ tailWord_5321867) baseStart_5321867 baseEnd_5321867 := by
    simpa [prefixWord, tailWord_5321867, baseEnd_5321867] using wordTrace_append hprefix tailTrace_5321867
  have hstable : (prefixWord ++ tailWord_5321867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5321867).length < 2 ^ (prefixWord ++ tailWord_5321867).sum := by decide
  have hdescent : baseEnd_5321867 < baseStart_5321867 := by decide
  rcases family_descends (prefixWord ++ tailWord_5321867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5321907 : List Nat := [1, 1, 1, 2, 3, 2, 6, 7]
def baseStart_5321907 : Nat := 118140960795 + 5321907 * 2 ^ 59
def prefixEnd_5321907 : Nat := 4983230072969 + 3 ^ 40 * 5321907 * 2
def baseEnd_5321907 : Nat := 101210973686200546225463

theorem tailTrace_5321907 : CollatzResearch.WordTrace tailWord_5321907 prefixEnd_5321907 101210973686200546225463 := by
  unfold tailWord_5321907
  simp only [CollatzResearch.WordTrace]
  refine ⟨194105894730647323198739975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129403929820431548799159983 194105894730647323198739975)
  ·
    refine ⟨291158842095970984798109963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194105894730647323198739975 291158842095970984798109963)
    ·
      refine ⟨436738263143956477197164945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 291158842095970984798109963 436738263143956477197164945)
      ·
        refine ⟨327553697357967357897873709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 436738263143956477197164945 327553697357967357897873709)
        ·
          refine ⟨122832636509237759211702641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 327553697357967357897873709 122832636509237759211702641)
          ·
            refine ⟨92124477381928319408776981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122832636509237759211702641 92124477381928319408776981)
            ·
              refine ⟨4318334877277889972286421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 92124477381928319408776981 4318334877277889972286421)
              ·
                refine ⟨101210973686200546225463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4318334877277889972286421 101210973686200546225463)
                ·
                  rfl

theorem cell23_5321907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 6, 7].length) (baseStart_5321907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5321907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5321907 prefixEnd_5321907 := by exact prefixLift 5321907
  have htrace : WordTrace (prefixWord ++ tailWord_5321907) baseStart_5321907 baseEnd_5321907 := by
    simpa [prefixWord, tailWord_5321907, baseEnd_5321907] using wordTrace_append hprefix tailTrace_5321907
  have hstable : (prefixWord ++ tailWord_5321907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5321907).length < 2 ^ (prefixWord ++ tailWord_5321907).sum := by decide
  have hdescent : baseEnd_5321907 < baseStart_5321907 := by decide
  rcases family_descends (prefixWord ++ tailWord_5321907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5321921 : List Nat := [1, 2, 6, 1, 1, 2, 2, 1, 1, 1, 5]
def baseStart_5321921 : Nat := 118140960795 + 5321921 * 2 ^ 59
def prefixEnd_5321921 : Nat := 4983230072969 + 3 ^ 40 * 5321921 * 2
def baseEnd_5321921 : Nat := 2732703478256577693312437

theorem tailTrace_5321921 : CollatzResearch.WordTrace tailWord_5321921 prefixEnd_5321921 2732703478256577693312437 := by
  unfold tailWord_5321921
  simp only [CollatzResearch.WordTrace]
  refine ⟨194106405352596603589749617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129404270235064402393166411 194106405352596603589749617)
  ·
    refine ⟨145579804014447452692312213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194106405352596603589749617 145579804014447452692312213)
    ·
      refine ⟨6824053313177224344952135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 145579804014447452692312213 6824053313177224344952135)
      ·
        refine ⟨10236079969765836517428203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6824053313177224344952135 10236079969765836517428203)
        ·
          refine ⟨15354119954648754776142305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10236079969765836517428203 15354119954648754776142305)
          ·
            refine ⟨11515589965986566082106729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15354119954648754776142305 11515589965986566082106729)
            ·
              refine ⟨8636692474489924561580047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11515589965986566082106729 8636692474489924561580047)
              ·
                refine ⟨12955038711734886842370071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8636692474489924561580047 12955038711734886842370071)
                ·
                  refine ⟨19432558067602330263555107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12955038711734886842370071 19432558067602330263555107)
                  ·
                    refine ⟨29148837101403495395332661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19432558067602330263555107 29148837101403495395332661)
                    ·
                      refine ⟨2732703478256577693312437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29148837101403495395332661 2732703478256577693312437)
                      ·
                        rfl

theorem cell23_5321921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_5321921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5321921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5321921 prefixEnd_5321921 := by exact prefixLift 5321921
  have htrace : WordTrace (prefixWord ++ tailWord_5321921) baseStart_5321921 baseEnd_5321921 := by
    simpa [prefixWord, tailWord_5321921, baseEnd_5321921] using wordTrace_append hprefix tailTrace_5321921
  have hstable : (prefixWord ++ tailWord_5321921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5321921).length < 2 ^ (prefixWord ++ tailWord_5321921).sum := by decide
  have hdescent : baseEnd_5321921 < baseStart_5321921 := by decide
  rcases family_descends (prefixWord ++ tailWord_5321921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5321924 : List Nat := [2, 3, 3, 1, 3, 2, 9]
def baseStart_5321924 : Nat := 118140960795 + 5321924 * 2 ^ 59
def prefixEnd_5321924 : Nat := 4983230072969 + 3 ^ 40 * 5321924 * 2
def baseEnd_5321924 : Nat := 33737098996278286192283

theorem tailTrace_5321924 : CollatzResearch.WordTrace tailWord_5321924 prefixEnd_5321924 33737098996278286192283 := by
  unfold tailWord_5321924
  simp only [CollatzResearch.WordTrace]
  refine ⟨97053257385792867551054413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129404343181057156734739217 97053257385792867551054413)
  ·
    refine ⟨36394971519672325331645405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97053257385792867551054413 36394971519672325331645405)
    ·
      refine ⟨13648114319877121999367027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36394971519672325331645405 13648114319877121999367027)
      ·
        refine ⟨20472171479815682999050541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13648114319877121999367027 20472171479815682999050541)
        ·
          refine ⟨7677064304930881124643953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20472171479815682999050541 7677064304930881124643953)
          ·
            refine ⟨5757798228698160843482965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7677064304930881124643953 5757798228698160843482965)
            ·
              refine ⟨33737098996278286192283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5757798228698160843482965 33737098996278286192283)
              ·
                rfl

theorem cell23_5321924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 9].length) (baseStart_5321924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5321924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5321924 prefixEnd_5321924 := by exact prefixLift 5321924
  have htrace : WordTrace (prefixWord ++ tailWord_5321924) baseStart_5321924 baseEnd_5321924 := by
    simpa [prefixWord, tailWord_5321924, baseEnd_5321924] using wordTrace_append hprefix tailTrace_5321924
  have hstable : (prefixWord ++ tailWord_5321924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5321924).length < 2 ^ (prefixWord ++ tailWord_5321924).sum := by decide
  have hdescent : baseEnd_5321924 < baseStart_5321924 := by decide
  rcases family_descends (prefixWord ++ tailWord_5321924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5321972 : List Nat := [2, 6, 1, 2, 2, 1, 1, 1, 1, 1, 5]
def baseStart_5321972 : Nat := 118140960795 + 5321972 * 2 ^ 59
def prefixEnd_5321972 : Nat := 4983230072969 + 3 ^ 40 * 5321972 * 2
def baseEnd_5321972 : Nat := 2732729665769956993774703

theorem tailTrace_5321972 : CollatzResearch.WordTrace tailWord_5321972 prefixEnd_5321972 2732729665769956993774703 := by
  unfold tailWord_5321972
  simp only [CollatzResearch.WordTrace]
  refine ⟨97054132737705919649928085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129405510316941226199904113 97054132737705919649928085)
  ·
    refine ⟨4549412472079964983590379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 97054132737705919649928085 4549412472079964983590379)
    ·
      refine ⟨6824118708119947475385569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4549412472079964983590379 6824118708119947475385569)
      ·
        refine ⟨5118089031089960606539177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6824118708119947475385569 5118089031089960606539177)
        ·
          refine ⟨3838566773317470454904383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5118089031089960606539177 3838566773317470454904383)
          ·
            refine ⟨5757850159976205682356575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3838566773317470454904383 5757850159976205682356575)
            ·
              refine ⟨8636775239964308523534863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5757850159976205682356575 8636775239964308523534863)
              ·
                refine ⟨12955162859946462785302295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8636775239964308523534863 12955162859946462785302295)
                ·
                  refine ⟨19432744289919694177953443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12955162859946462785302295 19432744289919694177953443)
                  ·
                    refine ⟨29149116434879541266930165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19432744289919694177953443 29149116434879541266930165)
                    ·
                      refine ⟨2732729665769956993774703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29149116434879541266930165 2732729665769956993774703)
                      ·
                        rfl

theorem cell23_5321972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_5321972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5321972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5321972 prefixEnd_5321972 := by exact prefixLift 5321972
  have htrace : WordTrace (prefixWord ++ tailWord_5321972) baseStart_5321972 baseEnd_5321972 := by
    simpa [prefixWord, tailWord_5321972, baseEnd_5321972] using wordTrace_append hprefix tailTrace_5321972
  have hstable : (prefixWord ++ tailWord_5321972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5321972).length < 2 ^ (prefixWord ++ tailWord_5321972).sum := by decide
  have hdescent : baseEnd_5321972 < baseStart_5321972 := by decide
  rcases family_descends (prefixWord ++ tailWord_5321972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5321977 : List Nat := [1, 2, 1, 3, 1, 1, 3, 3, 2, 1, 5]
def baseStart_5321977 : Nat := 118140960795 + 5321977 * 2 ^ 59
def prefixEnd_5321977 : Nat := 4983230072969 + 3 ^ 40 * 5321977 * 2
def baseEnd_5321977 : Nat := 2732732233173229474212179

theorem tailTrace_5321977 : CollatzResearch.WordTrace tailWord_5321977 prefixEnd_5321977 2732732233173229474212179 := by
  unfold tailWord_5321977
  simp only [CollatzResearch.WordTrace]
  refine ⟨194108447840393725153788185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129405631893595816769192123 194108447840393725153788185)
  ·
    refine ⟨145581335880295293865341139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194108447840393725153788185 145581335880295293865341139)
    ·
      refine ⟨218372003820442940798011709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145581335880295293865341139 218372003820442940798011709)
      ·
        refine ⟨81889501432666102799254391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 218372003820442940798011709 81889501432666102799254391)
        ·
          refine ⟨122834252148999154198881587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81889501432666102799254391 122834252148999154198881587)
          ·
            refine ⟨184251378223498731298322381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122834252148999154198881587 184251378223498731298322381)
            ·
              refine ⟨69094266833812024236870893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 184251378223498731298322381 69094266833812024236870893)
              ·
                refine ⟨25910350062679509088826585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69094266833812024236870893 25910350062679509088826585)
                ·
                  refine ⟨19432762547009631816619939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25910350062679509088826585 19432762547009631816619939)
                  ·
                    refine ⟨29149143820514447724929909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19432762547009631816619939 29149143820514447724929909)
                    ·
                      refine ⟨2732732233173229474212179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29149143820514447724929909 2732732233173229474212179)
                      ·
                        rfl

theorem cell23_5321977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 3, 2, 1, 5].length) (baseStart_5321977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5321977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5321977 prefixEnd_5321977 := by exact prefixLift 5321977
  have htrace : WordTrace (prefixWord ++ tailWord_5321977) baseStart_5321977 baseEnd_5321977 := by
    simpa [prefixWord, tailWord_5321977, baseEnd_5321977] using wordTrace_append hprefix tailTrace_5321977
  have hstable : (prefixWord ++ tailWord_5321977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5321977).length < 2 ^ (prefixWord ++ tailWord_5321977).sum := by decide
  have hdescent : baseEnd_5321977 < baseStart_5321977 := by decide
  rcases family_descends (prefixWord ++ tailWord_5321977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5321978 : List Nat := [3, 1, 1, 1, 1, 4, 5, 1, 1, 3, 2]
def baseStart_5321978 : Nat := 118140960795 + 5321978 * 2 ^ 59
def prefixEnd_5321978 : Nat := 4983230072969 + 3 ^ 40 * 5321978 * 2
def baseEnd_5321978 : Nat := 2732732746653883970299675

theorem tailTrace_5321978 : CollatzResearch.WordTrace tailWord_5321978 prefixEnd_5321978 2732732746653883970299675 := by
  unfold tailWord_5321978
  simp only [CollatzResearch.WordTrace]
  refine ⟨48527121078347525581143647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129405656208926734883049725 48527121078347525581143647)
  ·
    refine ⟨72790681617521288371715471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48527121078347525581143647 72790681617521288371715471)
    ·
      refine ⟨109186022426281932557573207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72790681617521288371715471 109186022426281932557573207)
      ·
        refine ⟨163779033639422898836359811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109186022426281932557573207 163779033639422898836359811)
        ·
          refine ⟨245668550459134348254539717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163779033639422898836359811 245668550459134348254539717)
          ·
            refine ⟨46062853211087690297726197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 245668550459134348254539717 46062853211087690297726197)
            ·
              refine ⟨4318392488539470965411831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46062853211087690297726197 4318392488539470965411831)
              ·
                refine ⟨6477588732809206448117747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4318392488539470965411831 6477588732809206448117747)
                ·
                  refine ⟨9716383099213809672176621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6477588732809206448117747 9716383099213809672176621)
                  ·
                    refine ⟨3643643662205178627066233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9716383099213809672176621 3643643662205178627066233)
                    ·
                      refine ⟨2732732746653883970299675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3643643662205178627066233 2732732746653883970299675)
                      ·
                        rfl

theorem cell23_5321978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 5, 1, 1, 3, 2].length) (baseStart_5321978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5321978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5321978 prefixEnd_5321978 := by exact prefixLift 5321978
  have htrace : WordTrace (prefixWord ++ tailWord_5321978) baseStart_5321978 baseEnd_5321978 := by
    simpa [prefixWord, tailWord_5321978, baseEnd_5321978] using wordTrace_append hprefix tailTrace_5321978
  have hstable : (prefixWord ++ tailWord_5321978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5321978).length < 2 ^ (prefixWord ++ tailWord_5321978).sum := by decide
  have hdescent : baseEnd_5321978 < baseStart_5321978 := by decide
  rcases family_descends (prefixWord ++ tailWord_5321978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5321986 : List Nat := [3, 4, 1, 1, 4, 1, 2, 2, 1, 2, 2]
def baseStart_5321986 : Nat := 118140960795 + 5321986 * 2 ^ 59
def prefixEnd_5321986 : Nat := 4983230072969 + 3 ^ 40 * 5321986 * 2
def baseEnd_5321986 : Nat := 2732736854499119938999639

theorem tailTrace_5321986 : CollatzResearch.WordTrace tailWord_5321986 prefixEnd_5321986 2732736854499119938999639 := by
  unfold tailWord_5321986
  simp only [CollatzResearch.WordTrace]
  refine ⟨48527194024340279922716453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129405850731574079793910541 48527194024340279922716453)
  ·
    refine ⟨9098848879563802485509335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48527194024340279922716453 9098848879563802485509335)
    ·
      refine ⟨13648273319345703728264003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9098848879563802485509335 13648273319345703728264003)
      ·
        refine ⟨20472409979018555592396005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13648273319345703728264003 20472409979018555592396005)
        ·
          refine ⟨3838576871065979173574251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20472409979018555592396005 3838576871065979173574251)
          ·
            refine ⟨5757865306598968760361377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3838576871065979173574251 5757865306598968760361377)
            ·
              refine ⟨4318398979949226570271033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5757865306598968760361377 4318398979949226570271033)
              ·
                refine ⟨3238799234961919927703275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4318398979949226570271033 3238799234961919927703275)
                ·
                  refine ⟨4858198852442879891554913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3238799234961919927703275 4858198852442879891554913)
                  ·
                    refine ⟨3643649139332159918666185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4858198852442879891554913 3643649139332159918666185)
                    ·
                      refine ⟨2732736854499119938999639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3643649139332159918666185 2732736854499119938999639)
                      ·
                        rfl

theorem cell23_5321986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 2, 2, 1, 2, 2].length) (baseStart_5321986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5321986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5321986 prefixEnd_5321986 := by exact prefixLift 5321986
  have htrace : WordTrace (prefixWord ++ tailWord_5321986) baseStart_5321986 baseEnd_5321986 := by
    simpa [prefixWord, tailWord_5321986, baseEnd_5321986] using wordTrace_append hprefix tailTrace_5321986
  have hstable : (prefixWord ++ tailWord_5321986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5321986).length < 2 ^ (prefixWord ++ tailWord_5321986).sum := by decide
  have hdescent : baseEnd_5321986 < baseStart_5321986 := by decide
  rcases family_descends (prefixWord ++ tailWord_5321986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5322008 : List Nat := [2, 1, 2, 3, 1, 3, 2, 3, 2, 2, 2]
def baseStart_5322008 : Nat := 118140960795 + 5322008 * 2 ^ 59
def prefixEnd_5322008 : Nat := 4983230072969 + 3 ^ 40 * 5322008 * 2
def baseEnd_5322008 : Nat := 2732748151073518852924537

theorem tailTrace_5322008 : CollatzResearch.WordTrace tailWord_5322008 prefixEnd_5322008 2732748151073518852924537 := by
  unfold tailWord_5322008
  simp only [CollatzResearch.WordTrace]
  refine ⟨97054789251640708724083339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129406385668854278298777785 97054789251640708724083339)
  ·
    refine ⟨145582183877461063086125009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97054789251640708724083339 145582183877461063086125009)
    ·
      refine ⟨109186637908095797314593757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145582183877461063086125009 109186637908095797314593757)
      ·
        refine ⟨40944989215535923992972659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109186637908095797314593757 40944989215535923992972659)
        ·
          refine ⟨61417483823303885989458989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40944989215535923992972659 61417483823303885989458989)
          ·
            refine ⟨23031556433738957246047121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61417483823303885989458989 23031556433738957246047121)
            ·
              refine ⟨17273667325304217934535341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23031556433738957246047121 17273667325304217934535341)
              ·
                refine ⟨6477625246989081725450753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17273667325304217934535341 6477625246989081725450753)
                ·
                  refine ⟨4858218935241811294088065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6477625246989081725450753 4858218935241811294088065)
                  ·
                    refine ⟨3643664201431358470566049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4858218935241811294088065 3643664201431358470566049)
                    ·
                      refine ⟨2732748151073518852924537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3643664201431358470566049 2732748151073518852924537)
                      ·
                        rfl

theorem cell23_5322008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 3, 2, 2, 2].length) (baseStart_5322008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5322008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5322008 prefixEnd_5322008 := by exact prefixLift 5322008
  have htrace : WordTrace (prefixWord ++ tailWord_5322008) baseStart_5322008 baseEnd_5322008 := by
    simpa [prefixWord, tailWord_5322008, baseEnd_5322008] using wordTrace_append hprefix tailTrace_5322008
  have hstable : (prefixWord ++ tailWord_5322008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5322008).length < 2 ^ (prefixWord ++ tailWord_5322008).sum := by decide
  have hdescent : baseEnd_5322008 < baseStart_5322008 := by decide
  rcases family_descends (prefixWord ++ tailWord_5322008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5322027 : List Nat := [1, 1, 1, 1, 2, 1, 2, 1, 8, 5]
def baseStart_5322027 : Nat := 118140960795 + 5322027 * 2 ^ 59
def prefixEnd_5322027 : Nat := 4983230072969 + 3 ^ 40 * 5322027 * 2
def baseEnd_5322027 : Nat := 910919302401984759528983

theorem tailTrace_5322027 : CollatzResearch.WordTrace tailWord_5322027 prefixEnd_5322027 910919302401984759528983 := by
  unfold tailWord_5322027
  simp only [CollatzResearch.WordTrace]
  refine ⟨194110271490212583693108335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129406847660141722462072223 194110271490212583693108335)
  ·
    refine ⟨291165407235318875539662503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194110271490212583693108335 291165407235318875539662503)
    ·
      refine ⟨436748110852978313309493755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 291165407235318875539662503 436748110852978313309493755)
      ·
        refine ⟨655122166279467469964240633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 436748110852978313309493755 655122166279467469964240633)
        ·
          refine ⟨491341624709600602473180475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 655122166279467469964240633 491341624709600602473180475)
          ·
            refine ⟨737012437064400903709770713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 491341624709600602473180475 737012437064400903709770713)
            ·
              refine ⟨552759327798300677782328035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 737012437064400903709770713 552759327798300677782328035)
              ·
                refine ⟨829138991697451016673492053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 552759327798300677782328035 829138991697451016673492053)
                ·
                  refine ⟨9716472558954504101642485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 829138991697451016673492053 9716472558954504101642485)
                  ·
                    refine ⟨910919302401984759528983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9716472558954504101642485 910919302401984759528983)
                    ·
                      rfl

theorem cell23_5322027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 8, 5].length) (baseStart_5322027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5322027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5322027 prefixEnd_5322027 := by exact prefixLift 5322027
  have htrace : WordTrace (prefixWord ++ tailWord_5322027) baseStart_5322027 baseEnd_5322027 := by
    simpa [prefixWord, tailWord_5322027, baseEnd_5322027] using wordTrace_append hprefix tailTrace_5322027
  have hstable : (prefixWord ++ tailWord_5322027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5322027).length < 2 ^ (prefixWord ++ tailWord_5322027).sum := by decide
  have hdescent : baseEnd_5322027 < baseStart_5322027 := by decide
  rcases family_descends (prefixWord ++ tailWord_5322027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5322121 : List Nat := [1, 2, 1, 1, 7, 1, 1, 3, 6]
def baseStart_5322121 : Nat := 118140960795 + 5322121 * 2 ^ 59
def prefixEnd_5322121 : Nat := 4983230072969 + 3 ^ 40 * 5322121 * 2
def baseEnd_5322121 : Nat := 303645130487497434534613

theorem tailTrace_5322121 : CollatzResearch.WordTrace tailWord_5322121 prefixEnd_5322121 303645130487497434534613 := by
  unfold tailWord_5322121
  simp only [CollatzResearch.WordTrace]
  refine ⟨194113699951872037747030217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129409133301248025164686811 194113699951872037747030217)
  ·
    refine ⟨145585274963904028310272663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194113699951872037747030217 145585274963904028310272663)
    ·
      refine ⟨218377912445856042465408995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145585274963904028310272663 218377912445856042465408995)
      ·
        refine ⟨327566868668784063698113493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218377912445856042465408995 327566868668784063698113493)
        ·
          refine ⟨7677348484424626492924535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 327566868668784063698113493 7677348484424626492924535)
          ·
            refine ⟨11516022726636939739386803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7677348484424626492924535 11516022726636939739386803)
            ·
              refine ⟨17274034089955409609080205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11516022726636939739386803 17274034089955409609080205)
              ·
                refine ⟨6477762783733278603405077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17274034089955409609080205 6477762783733278603405077)
                ·
                  refine ⟨303645130487497434534613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6477762783733278603405077 303645130487497434534613)
                  ·
                    rfl

theorem cell23_5322121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 3, 6].length) (baseStart_5322121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5322121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5322121 prefixEnd_5322121 := by exact prefixLift 5322121
  have htrace : WordTrace (prefixWord ++ tailWord_5322121) baseStart_5322121 baseEnd_5322121 := by
    simpa [prefixWord, tailWord_5322121, baseEnd_5322121] using wordTrace_append hprefix tailTrace_5322121
  have hstable : (prefixWord ++ tailWord_5322121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5322121).length < 2 ^ (prefixWord ++ tailWord_5322121).sum := by decide
  have hdescent : baseEnd_5322121 < baseStart_5322121 := by decide
  rcases family_descends (prefixWord ++ tailWord_5322121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5322191 : List Nat := [1, 1, 2, 1, 1, 4, 4, 1, 3, 2, 3]
def baseStart_5322191 : Nat := 118140960795 + 5322191 * 2 ^ 59
def prefixEnd_5322191 : Nat := 4983230072969 + 3 ^ 40 * 5322191 * 2
def baseEnd_5322191 : Nat := 2732842118033291636936195

theorem tailTrace_5322191 : CollatzResearch.WordTrace tailWord_5322191 prefixEnd_5322191 2732842118033291636936195 := by
  unfold tailWord_5322191
  simp only [CollatzResearch.WordTrace]
  refine ⟨194116253061618439702078427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129410835374412293134718951 194116253061618439702078427)
  ·
    refine ⟨291174379592427659553117641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194116253061618439702078427 291174379592427659553117641)
    ·
      refine ⟨218380784694320744664838231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 291174379592427659553117641 218380784694320744664838231)
      ·
        refine ⟨327571177041481116997257347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218380784694320744664838231 327571177041481116997257347)
        ·
          refine ⟨491356765562221675495886021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 327571177041481116997257347 491356765562221675495886021)
          ·
            refine ⟨92129393542916564155478629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 491356765562221675495886021 92129393542916564155478629)
            ·
              refine ⟨17274261289296855779152243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 92129393542916564155478629 17274261289296855779152243)
              ·
                refine ⟨25911391933945283668728365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17274261289296855779152243 25911391933945283668728365)
                ·
                  refine ⟨9716771975229481375773137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25911391933945283668728365 9716771975229481375773137)
                  ·
                    refine ⟨7287578981422111031829853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9716771975229481375773137 7287578981422111031829853)
                    ·
                      refine ⟨2732842118033291636936195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7287578981422111031829853 2732842118033291636936195)
                      ·
                        rfl

theorem cell23_5322191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 1, 3, 2, 3].length) (baseStart_5322191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5322191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5322191 prefixEnd_5322191 := by exact prefixLift 5322191
  have htrace : WordTrace (prefixWord ++ tailWord_5322191) baseStart_5322191 baseEnd_5322191 := by
    simpa [prefixWord, tailWord_5322191, baseEnd_5322191] using wordTrace_append hprefix tailTrace_5322191
  have hstable : (prefixWord ++ tailWord_5322191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5322191).length < 2 ^ (prefixWord ++ tailWord_5322191).sum := by decide
  have hdescent : baseEnd_5322191 < baseStart_5322191 := by decide
  rcases family_descends (prefixWord ++ tailWord_5322191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5322198 : List Nat := [5, 2, 1, 1, 1, 2, 2, 2, 1, 6]
def baseStart_5322198 : Nat := 118140960795 + 5322198 * 2 ^ 59
def prefixEnd_5322198 : Nat := 4983230072969 + 3 ^ 40 * 5322198 * 2
def baseEnd_5322198 : Nat := 910948570799291036516221

theorem tailTrace_5322198 : CollatzResearch.WordTrace tailWord_5322198 prefixEnd_5322198 910948570799291036516221 := by
  unfold tailWord_5322198
  simp only [CollatzResearch.WordTrace]
  refine ⟨12132281773287067493598953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 129411005581728719931722165 12132281773287067493598953)
  ·
    refine ⟨9099211329965300620199215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12132281773287067493598953 9099211329965300620199215)
    ·
      refine ⟨13648816994947950930298823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9099211329965300620199215 13648816994947950930298823)
      ·
        refine ⟨20473225492421926395448235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13648816994947950930298823 20473225492421926395448235)
        ·
          refine ⟨30709838238632889593172353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20473225492421926395448235 30709838238632889593172353)
          ·
            refine ⟨23032378678974667194879265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30709838238632889593172353 23032378678974667194879265)
            ·
              refine ⟨17274284009231000396159449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23032378678974667194879265 17274284009231000396159449)
              ·
                refine ⟨12955713006923250297119587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17274284009231000396159449 12955713006923250297119587)
                ·
                  refine ⟨19433569510384875445679381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12955713006923250297119587 19433569510384875445679381)
                  ·
                    refine ⟨910948570799291036516221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19433569510384875445679381 910948570799291036516221)
                    ·
                      rfl

theorem cell23_5322198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_5322198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5322198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5322198 prefixEnd_5322198 := by exact prefixLift 5322198
  have htrace : WordTrace (prefixWord ++ tailWord_5322198) baseStart_5322198 baseEnd_5322198 := by
    simpa [prefixWord, tailWord_5322198, baseEnd_5322198] using wordTrace_append hprefix tailTrace_5322198
  have hstable : (prefixWord ++ tailWord_5322198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5322198).length < 2 ^ (prefixWord ++ tailWord_5322198).sum := by decide
  have hdescent : baseEnd_5322198 < baseStart_5322198 := by decide
  rcases family_descends (prefixWord ++ tailWord_5322198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5322201 : List Nat := [1, 2, 1, 2, 4, 2, 2, 2, 1, 2, 4]
def baseStart_5322201 : Nat := 118140960795 + 5322201 * 2 ^ 59
def prefixEnd_5322201 : Nat := 4983230072969 + 3 ^ 40 * 5322201 * 2
def baseEnd_5322201 : Nat := 2732847252839836597811149

theorem tailTrace_5322201 : CollatzResearch.WordTrace tailWord_5322201 prefixEnd_5322201 2732847252839836597811149 := by
  unfold tailWord_5322201
  simp only [CollatzResearch.WordTrace]
  refine ⟨194116617791582211409942457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129411078527721474273294971 194116617791582211409942457)
  ·
    refine ⟨145587463343686658557456843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194116617791582211409942457 145587463343686658557456843)
    ·
      refine ⟨218381195015529987836185265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145587463343686658557456843 218381195015529987836185265)
      ·
        refine ⟨163785896261647490877138949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 218381195015529987836185265 163785896261647490877138949)
        ·
          refine ⟨30709855549058904539463553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 163785896261647490877138949 30709855549058904539463553)
          ·
            refine ⟨23032391661794178404597665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30709855549058904539463553 23032391661794178404597665)
            ·
              refine ⟨17274293746345633803448249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23032391661794178404597665 17274293746345633803448249)
              ·
                refine ⟨12955720309759225352586187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17274293746345633803448249 12955720309759225352586187)
                ·
                  refine ⟨19433580464638838028879281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12955720309759225352586187 19433580464638838028879281)
                  ·
                    refine ⟨14575185348479128521659461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19433580464638838028879281 14575185348479128521659461)
                    ·
                      refine ⟨2732847252839836597811149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14575185348479128521659461 2732847252839836597811149)
                      ·
                        rfl

theorem cell23_5322201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 2, 1, 2, 4].length) (baseStart_5322201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5322201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5322201 prefixEnd_5322201 := by exact prefixLift 5322201
  have htrace : WordTrace (prefixWord ++ tailWord_5322201) baseStart_5322201 baseEnd_5322201 := by
    simpa [prefixWord, tailWord_5322201, baseEnd_5322201] using wordTrace_append hprefix tailTrace_5322201
  have hstable : (prefixWord ++ tailWord_5322201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5322201).length < 2 ^ (prefixWord ++ tailWord_5322201).sum := by decide
  have hdescent : baseEnd_5322201 < baseStart_5322201 := by decide
  rcases family_descends (prefixWord ++ tailWord_5322201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5322205 : List Nat := [1, 4, 3, 1, 1, 2, 4, 1, 1, 1, 4]
def baseStart_5322205 : Nat := 118140960795 + 5322205 * 2 ^ 59
def prefixEnd_5322205 : Nat := 4983230072969 + 3 ^ 40 * 5322205 * 2
def baseEnd_5322205 : Nat := 2732849306762454582161131

theorem tailTrace_5322205 : CollatzResearch.WordTrace tailWord_5322205 prefixEnd_5322205 2732849306762454582161131 := by
  unfold tailWord_5322205
  simp only [CollatzResearch.WordTrace]
  refine ⟨194116763683567720093088069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129411175789045146728725379 194116763683567720093088069)
  ·
    refine ⟨36396893190668947517454013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 194116763683567720093088069 36396893190668947517454013)
    ·
      refine ⟨13648834946500855319045255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36396893190668947517454013 13648834946500855319045255)
      ·
        refine ⟨20473252419751282978567883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13648834946500855319045255 20473252419751282978567883)
        ·
          refine ⟨30709878629626924467851825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20473252419751282978567883 30709878629626924467851825)
          ·
            refine ⟨23032408972220193350888869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30709878629626924467851825 23032408972220193350888869)
            ·
              refine ⟨4318576682291286253291663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23032408972220193350888869 4318576682291286253291663)
              ·
                refine ⟨6477865023436929379937495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4318576682291286253291663 6477865023436929379937495)
                ·
                  refine ⟨9716797535155394069906243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6477865023436929379937495 9716797535155394069906243)
                  ·
                    refine ⟨14575196302733091104859365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9716797535155394069906243 14575196302733091104859365)
                    ·
                      refine ⟨2732849306762454582161131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14575196302733091104859365 2732849306762454582161131)
                      ·
                        rfl

theorem cell23_5322205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 4, 1, 1, 1, 4].length) (baseStart_5322205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5322205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5322205 prefixEnd_5322205 := by exact prefixLift 5322205
  have htrace : WordTrace (prefixWord ++ tailWord_5322205) baseStart_5322205 baseEnd_5322205 := by
    simpa [prefixWord, tailWord_5322205, baseEnd_5322205] using wordTrace_append hprefix tailTrace_5322205
  have hstable : (prefixWord ++ tailWord_5322205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5322205).length < 2 ^ (prefixWord ++ tailWord_5322205).sum := by decide
  have hdescent : baseEnd_5322205 < baseStart_5322205 := by decide
  rcases family_descends (prefixWord ++ tailWord_5322205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5322215 : List Nat := [1, 1, 5, 2, 1, 4, 1, 2, 2, 4]
def baseStart_5322215 : Nat := 118140960795 + 5322215 * 2 ^ 59
def prefixEnd_5322215 : Nat := 4983230072969 + 3 ^ 40 * 5322215 * 2
def baseEnd_5322215 : Nat := 910951480522999847678695

theorem tailTrace_5322215 : CollatzResearch.WordTrace tailWord_5322215 prefixEnd_5322215 910951480522999847678695 := by
  unfold tailWord_5322215
  simp only [CollatzResearch.WordTrace]
  refine ⟨194117128413531491800952099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129411418942354327867301399 194117128413531491800952099)
  ·
    refine ⟨291175692620297237701428149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194117128413531491800952099 291175692620297237701428149)
    ·
      refine ⟨27297721183152866034508889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 291175692620297237701428149 27297721183152866034508889)
      ·
        refine ⟨20473290887364649525881667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27297721183152866034508889 20473290887364649525881667)
        ·
          refine ⟨30709936331046974288822501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20473290887364649525881667 30709936331046974288822501)
          ·
            refine ⟨5758113062071307679154219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30709936331046974288822501 5758113062071307679154219)
            ·
              refine ⟨8637169593106961518731329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5758113062071307679154219 8637169593106961518731329)
              ·
                refine ⟨6477877194830221139048497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8637169593106961518731329 6477877194830221139048497)
                ·
                  refine ⟨4858407896122665854286373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6477877194830221139048497 4858407896122665854286373)
                  ·
                    refine ⟨910951480522999847678695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4858407896122665854286373 910951480522999847678695)
                    ·
                      rfl

theorem cell23_5322215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 2, 2, 4].length) (baseStart_5322215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5322215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5322215 prefixEnd_5322215 := by exact prefixLift 5322215
  have htrace : WordTrace (prefixWord ++ tailWord_5322215) baseStart_5322215 baseEnd_5322215 := by
    simpa [prefixWord, tailWord_5322215, baseEnd_5322215] using wordTrace_append hprefix tailTrace_5322215
  have hstable : (prefixWord ++ tailWord_5322215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5322215).length < 2 ^ (prefixWord ++ tailWord_5322215).sum := by decide
  have hdescent : baseEnd_5322215 < baseStart_5322215 := by decide
  rcases family_descends (prefixWord ++ tailWord_5322215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5322222 : List Nat := [4, 1, 2, 1, 2, 1, 1, 6, 1, 2, 2]
def baseStart_5322222 : Nat := 118140960795 + 5322222 * 2 ^ 59
def prefixEnd_5322222 : Nat := 4983230072969 + 3 ^ 40 * 5322222 * 2
def baseEnd_5322222 : Nat := 2732858035933581015648553

theorem tailTrace_5322222 : CollatzResearch.WordTrace tailWord_5322222 prefixEnd_5322222 2732858035933581015648553 := by
  unfold tailWord_5322222
  simp only [CollatzResearch.WordTrace]
  refine ⟨24264672965563266499557115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129411589149670754664304613 24264672965563266499557115)
  ·
    refine ⟨36397009448344899749335673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24264672965563266499557115 36397009448344899749335673)
    ·
      refine ⟨27297757086258674812001755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36397009448344899749335673 27297757086258674812001755)
      ·
        refine ⟨40946635629388012218002633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27297757086258674812001755 40946635629388012218002633)
        ·
          refine ⟨30709976722041009163501975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40946635629388012218002633 30709976722041009163501975)
          ·
            refine ⟨46064965083061513745252963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30709976722041009163501975 46064965083061513745252963)
            ·
              refine ⟨69097447624592270617879445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46064965083061513745252963 69097447624592270617879445)
              ·
                refine ⟨3238942857402762685213099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 69097447624592270617879445 3238942857402762685213099)
                ·
                  refine ⟨4858414286104144027819649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3238942857402762685213099 4858414286104144027819649)
                  ·
                    refine ⟨3643810714578108020864737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4858414286104144027819649 3643810714578108020864737)
                    ·
                      refine ⟨2732858035933581015648553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3643810714578108020864737 2732858035933581015648553)
                      ·
                        rfl

theorem cell23_5322222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 6, 1, 2, 2].length) (baseStart_5322222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5322222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5322222 prefixEnd_5322222 := by exact prefixLift 5322222
  have htrace : WordTrace (prefixWord ++ tailWord_5322222) baseStart_5322222 baseEnd_5322222 := by
    simpa [prefixWord, tailWord_5322222, baseEnd_5322222] using wordTrace_append hprefix tailTrace_5322222
  have hstable : (prefixWord ++ tailWord_5322222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5322222).length < 2 ^ (prefixWord ++ tailWord_5322222).sum := by decide
  have hdescent : baseEnd_5322222 < baseStart_5322222 := by decide
  rcases family_descends (prefixWord ++ tailWord_5322222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5322231 : List Nat := [1, 1, 3, 1, 1, 1, 1, 3, 2, 7, 2]
def baseStart_5322231 : Nat := 118140960795 + 5322231 * 2 ^ 59
def prefixEnd_5322231 : Nat := 4983230072969 + 3 ^ 40 * 5322231 * 2
def baseEnd_5322231 : Nat := 2732862657259471480436011

theorem tailTrace_5322231 : CollatzResearch.WordTrace tailWord_5322231 prefixEnd_5322231 2732862657259471480436011 := by
  unfold tailWord_5322231
  simp only [CollatzResearch.WordTrace]
  refine ⟨194117711981473526533534547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129411807987649017689023031 194117711981473526533534547)
  ·
    refine ⟨291176567972210289800301821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194117711981473526533534547 291176567972210289800301821)
    ·
      refine ⟨109191212989578858675113183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 291176567972210289800301821 109191212989578858675113183)
      ·
        refine ⟨163786819484368288012669775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109191212989578858675113183 163786819484368288012669775)
        ·
          refine ⟨245680229226552432019004663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163786819484368288012669775 245680229226552432019004663)
          ·
            refine ⟨368520343839828648028506995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 245680229226552432019004663 368520343839828648028506995)
            ·
              refine ⟨552780515759742972042760493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 368520343839828648028506995 552780515759742972042760493)
              ·
                refine ⟨207292693409903614516035185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 552780515759742972042760493 207292693409903614516035185)
                ·
                  refine ⟨155469520057427710887026389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 207292693409903614516035185 155469520057427710887026389)
                  ·
                    refine ⟨3643816876345961973914681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 155469520057427710887026389 3643816876345961973914681)
                    ·
                      refine ⟨2732862657259471480436011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3643816876345961973914681 2732862657259471480436011)
                      ·
                        rfl

theorem cell23_5322231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 7, 2].length) (baseStart_5322231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5322231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5322231 prefixEnd_5322231 := by exact prefixLift 5322231
  have htrace : WordTrace (prefixWord ++ tailWord_5322231) baseStart_5322231 baseEnd_5322231 := by
    simpa [prefixWord, tailWord_5322231, baseEnd_5322231] using wordTrace_append hprefix tailTrace_5322231
  have hstable : (prefixWord ++ tailWord_5322231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5322231).length < 2 ^ (prefixWord ++ tailWord_5322231).sum := by decide
  have hdescent : baseEnd_5322231 < baseStart_5322231 := by decide
  rcases family_descends (prefixWord ++ tailWord_5322231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5322242 : List Nat := [3, 4, 1, 2, 1, 2, 2, 2, 1, 2, 3]
def baseStart_5322242 : Nat := 118140960795 + 5322242 * 2 ^ 59
def prefixEnd_5322242 : Nat := 4983230072969 + 3 ^ 40 * 5322242 * 2
def baseEnd_5322242 : Nat := 2732868305546670937398461

theorem tailTrace_5322242 : CollatzResearch.WordTrace tailWord_5322242 prefixEnd_5322242 2732868305546670937398461 := by
  unfold tailWord_5322242
  simp only [CollatzResearch.WordTrace]
  refine ⟨48529528296108418853046245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129412075456289116941456653 48529528296108418853046245)
  ·
    refine ⟨9099286555520328534946171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48529528296108418853046245 9099286555520328534946171)
    ·
      refine ⟨13648929833280492802419257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9099286555520328534946171 13648929833280492802419257)
      ·
        refine ⟨10236697374960369601814443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13648929833280492802419257 10236697374960369601814443)
        ·
          refine ⟨15355046062440554402721665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10236697374960369601814443 15355046062440554402721665)
          ·
            refine ⟨11516284546830415802041249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15355046062440554402721665 11516284546830415802041249)
            ·
              refine ⟨8637213410122811851530937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11516284546830415802041249 8637213410122811851530937)
              ·
                refine ⟨6477910057592108888648203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8637213410122811851530937 6477910057592108888648203)
                ·
                  refine ⟨9716865086388163332972305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6477910057592108888648203 9716865086388163332972305)
                  ·
                    refine ⟨7287648814791122499729229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9716865086388163332972305 7287648814791122499729229)
                    ·
                      refine ⟨2732868305546670937398461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7287648814791122499729229 2732868305546670937398461)
                      ·
                        rfl

theorem cell23_5322242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_5322242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5322242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5322242 prefixEnd_5322242 := by exact prefixLift 5322242
  have htrace : WordTrace (prefixWord ++ tailWord_5322242) baseStart_5322242 baseEnd_5322242 := by
    simpa [prefixWord, tailWord_5322242, baseEnd_5322242] using wordTrace_append hprefix tailTrace_5322242
  have hstable : (prefixWord ++ tailWord_5322242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5322242).length < 2 ^ (prefixWord ++ tailWord_5322242).sum := by decide
  have hdescent : baseEnd_5322242 < baseStart_5322242 := by decide
  rcases family_descends (prefixWord ++ tailWord_5322242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5322248 : List Nat := [2, 1, 3, 2, 1, 1, 2, 3, 3, 3, 2]
def baseStart_5322248 : Nat := 118140960795 + 5322248 * 2 ^ 59
def prefixEnd_5322248 : Nat := 4983230072969 + 3 ^ 40 * 5322248 * 2
def baseEnd_5322248 : Nat := 2732871386430597913923433

theorem tailTrace_5322248 : CollatzResearch.WordTrace tailWord_5322248 prefixEnd_5322248 2732871386430597913923433 := by
  unfold tailWord_5322248
  simp only [CollatzResearch.WordTrace]
  refine ⟨97059166011205969218451699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129412221348274625624602265 97059166011205969218451699)
  ·
    refine ⟨145588749016808953827677549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97059166011205969218451699 145588749016808953827677549)
    ·
      refine ⟨54595780881303357685379081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145588749016808953827677549 54595780881303357685379081)
      ·
        refine ⟨40946835660977518264034311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54595780881303357685379081 40946835660977518264034311)
        ·
          refine ⟨61420253491466277396051467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40946835660977518264034311 61420253491466277396051467)
          ·
            refine ⟨92130380237199416094077201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61420253491466277396051467 92130380237199416094077201)
            ·
              refine ⟨69097785177899562070557901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92130380237199416094077201 69097785177899562070557901)
              ·
                refine ⟨25911669441712335776459213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69097785177899562070557901 25911669441712335776459213)
                ·
                  refine ⟨9716876040642125916172205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25911669441712335776459213 9716876040642125916172205)
                  ·
                    refine ⟨3643828515240797218564577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9716876040642125916172205 3643828515240797218564577)
                    ·
                      refine ⟨2732871386430597913923433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3643828515240797218564577 2732871386430597913923433)
                      ·
                        rfl

theorem cell23_5322248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 3, 3, 3, 2].length) (baseStart_5322248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5322248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5322248 prefixEnd_5322248 := by exact prefixLift 5322248
  have htrace : WordTrace (prefixWord ++ tailWord_5322248) baseStart_5322248 baseEnd_5322248 := by
    simpa [prefixWord, tailWord_5322248, baseEnd_5322248] using wordTrace_append hprefix tailTrace_5322248
  have hstable : (prefixWord ++ tailWord_5322248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5322248).length < 2 ^ (prefixWord ++ tailWord_5322248).sum := by decide
  have hdescent : baseEnd_5322248 < baseStart_5322248 := by decide
  rcases family_descends (prefixWord ++ tailWord_5322248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5322318 : List Nat := [4, 1, 1, 1, 1, 2, 1, 7, 5]
def baseStart_5322318 : Nat := 118140960795 + 5322318 * 2 ^ 59
def prefixEnd_5322318 : Nat := 4983230072969 + 3 ^ 40 * 5322318 * 2
def baseEnd_5322318 : Nat := 303656370008490293338679

theorem tailTrace_5322318 : CollatzResearch.WordTrace tailWord_5322318 prefixEnd_5322318 303656370008490293338679 := by
  unfold tailWord_5322318
  simp only [CollatzResearch.WordTrace]
  refine ⟨24265110641519792548993951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129413923421438893594634405 24265110641519792548993951)
  ·
    refine ⟨36397665962279688823490927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24265110641519792548993951 36397665962279688823490927)
    ·
      refine ⟨54596498943419533235236391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36397665962279688823490927 54596498943419533235236391)
      ·
        refine ⟨81894748415129299852854587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54596498943419533235236391 81894748415129299852854587)
        ·
          refine ⟨122842122622693949779281881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81894748415129299852854587 122842122622693949779281881)
          ·
            refine ⟨92131591967020462334461411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122842122622693949779281881 92131591967020462334461411)
            ·
              refine ⟨138197387950530693501692117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92131591967020462334461411 138197387950530693501692117)
              ·
                refine ⟨3239001280090563128945909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 138197387950530693501692117 3239001280090563128945909)
                ·
                  refine ⟨303656370008490293338679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3239001280090563128945909 303656370008490293338679)
                  ·
                    rfl

theorem cell23_5322318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 7, 5].length) (baseStart_5322318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5322318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5322318 prefixEnd_5322318 := by exact prefixLift 5322318
  have htrace : WordTrace (prefixWord ++ tailWord_5322318) baseStart_5322318 baseEnd_5322318 := by
    simpa [prefixWord, tailWord_5322318, baseEnd_5322318] using wordTrace_append hprefix tailTrace_5322318
  have hstable : (prefixWord ++ tailWord_5322318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5322318).length < 2 ^ (prefixWord ++ tailWord_5322318).sum := by decide
  have hdescent : baseEnd_5322318 < baseStart_5322318 := by decide
  rcases family_descends (prefixWord ++ tailWord_5322318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5322351 : List Nat := [1, 1, 2, 1, 3, 2, 1, 4, 1, 3, 4]
def baseStart_5322351 : Nat := 118140960795 + 5322351 * 2 ^ 59
def prefixEnd_5322351 : Nat := 4983230072969 + 3 ^ 40 * 5322351 * 2
def baseEnd_5322351 : Nat := 2732924274938011010935459

theorem tailTrace_5322351 : CollatzResearch.WordTrace tailWord_5322351 prefixEnd_5322351 2732924274938011010935459 := by
  unfold tailWord_5322351
  simp only [CollatzResearch.WordTrace]
  refine ⟨194122088741038787027902907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129414725827359191351935271 194122088741038787027902907)
  ·
    refine ⟨291183133111558180541854361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194122088741038787027902907 291183133111558180541854361)
    ·
      refine ⟨218387349833668635406390771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 291183133111558180541854361 218387349833668635406390771)
      ·
        refine ⟨327581024750502953109586157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218387349833668635406390771 327581024750502953109586157)
        ·
          refine ⟨122842884281438607416094809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 327581024750502953109586157 122842884281438607416094809)
          ·
            refine ⟨92132163211078955562071107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122842884281438607416094809 92132163211078955562071107)
            ·
              refine ⟨138198244816618433343106661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92132163211078955562071107 138198244816618433343106661)
              ·
                refine ⟨25912170903115956251832499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 138198244816618433343106661 25912170903115956251832499)
                ·
                  refine ⟨38868256354673934377748749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25912170903115956251832499 38868256354673934377748749)
                  ·
                    refine ⟨14575596133002725391655781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38868256354673934377748749 14575596133002725391655781)
                    ·
                      refine ⟨2732924274938011010935459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14575596133002725391655781 2732924274938011010935459)
                      ·
                        rfl

theorem cell23_5322351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 4, 1, 3, 4].length) (baseStart_5322351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5322351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5322351 prefixEnd_5322351 := by exact prefixLift 5322351
  have htrace : WordTrace (prefixWord ++ tailWord_5322351) baseStart_5322351 baseEnd_5322351 := by
    simpa [prefixWord, tailWord_5322351, baseEnd_5322351] using wordTrace_append hprefix tailTrace_5322351
  have hstable : (prefixWord ++ tailWord_5322351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5322351).length < 2 ^ (prefixWord ++ tailWord_5322351).sum := by decide
  have hdescent : baseEnd_5322351 < baseStart_5322351 := by decide
  rcases family_descends (prefixWord ++ tailWord_5322351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5322365 : List Nat := [1, 4, 1, 1, 4, 3, 1, 1, 2, 5]
def baseStart_5322365 : Nat := 118140960795 + 5322365 * 2 ^ 59
def prefixEnd_5322365 : Nat := 4983230072969 + 3 ^ 40 * 5322365 * 2
def baseEnd_5322365 : Nat := 910977154555724652053465

theorem tailTrace_5322365 : CollatzResearch.WordTrace tailWord_5322365 prefixEnd_5322365 910977154555724652053465 := by
  unfold tailWord_5322365
  simp only [CollatzResearch.WordTrace]
  refine ⟨194122599362988067418912549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129415066241992044945941699 194122599362988067418912549)
  ·
    refine ⟨36397987380560262641046103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 194122599362988067418912549 36397987380560262641046103)
    ·
      refine ⟨54596981070840393961569155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36397987380560262641046103 54596981070840393961569155)
      ·
        refine ⟨81895471606260590942353733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54596981070840393961569155 81895471606260590942353733)
        ·
          refine ⟨15355400926173860801691325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81895471606260590942353733 15355400926173860801691325)
          ·
            refine ⟨5758275347315197800634247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15355400926173860801691325 5758275347315197800634247)
            ·
              refine ⟨8637413020972796700951371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5758275347315197800634247 8637413020972796700951371)
              ·
                refine ⟨12956119531459195051427057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8637413020972796700951371 12956119531459195051427057)
                ·
                  refine ⟨9717089648594396288570293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12956119531459195051427057 9717089648594396288570293)
                  ·
                    refine ⟨910977154555724652053465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9717089648594396288570293 910977154555724652053465)
                    ·
                      rfl

theorem cell23_5322365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 1, 2, 5].length) (baseStart_5322365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5322365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5322365 prefixEnd_5322365 := by exact prefixLift 5322365
  have htrace : WordTrace (prefixWord ++ tailWord_5322365) baseStart_5322365 baseEnd_5322365 := by
    simpa [prefixWord, tailWord_5322365, baseEnd_5322365] using wordTrace_append hprefix tailTrace_5322365
  have hstable : (prefixWord ++ tailWord_5322365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5322365).length < 2 ^ (prefixWord ++ tailWord_5322365).sum := by decide
  have hdescent : baseEnd_5322365 < baseStart_5322365 := by decide
  rcases family_descends (prefixWord ++ tailWord_5322365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5322368 : List Nat := [2, 1, 1, 2, 1, 4, 1, 2, 1, 6, 2]
def baseStart_5322368 : Nat := 118140960795 + 5322368 * 2 ^ 59
def prefixEnd_5322368 : Nat := 4983230072969 + 3 ^ 40 * 5322368 * 2
def baseEnd_5322368 : Nat := 2732933004109137444422881

theorem tailTrace_5322368 : CollatzResearch.WordTrace tailWord_5322368 prefixEnd_5322368 2732933004109137444422881 := by
  unfold tailWord_5322368
  simp only [CollatzResearch.WordTrace]
  refine ⟨97061354390988599465635879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129415139187984799287514505 97061354390988599465635879)
  ·
    refine ⟨145592031586482899198453819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97061354390988599465635879 145592031586482899198453819)
    ·
      refine ⟨218388047379724348797680729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145592031586482899198453819 218388047379724348797680729)
      ·
        refine ⟨163791035534793261598260547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 218388047379724348797680729 163791035534793261598260547)
        ·
          refine ⟨245686553302189892397390821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163791035534793261598260547 245686553302189892397390821)
          ·
            refine ⟨46066228744160604824510779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 245686553302189892397390821 46066228744160604824510779)
            ·
              refine ⟨69099343116240907236766169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46066228744160604824510779 69099343116240907236766169)
              ·
                refine ⟨51824507337180680427574627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69099343116240907236766169 51824507337180680427574627)
                ·
                  refine ⟨77736761005771020641361941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51824507337180680427574627 77736761005771020641361941)
                  ·
                    refine ⟨3643910672145516592563841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 77736761005771020641361941 3643910672145516592563841)
                    ·
                      refine ⟨2732933004109137444422881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3643910672145516592563841 2732933004109137444422881)
                      ·
                        rfl

theorem cell23_5322368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 2, 1, 6, 2].length) (baseStart_5322368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5322368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5322368 prefixEnd_5322368 := by exact prefixLift 5322368
  have htrace : WordTrace (prefixWord ++ tailWord_5322368) baseStart_5322368 baseEnd_5322368 := by
    simpa [prefixWord, tailWord_5322368, baseEnd_5322368] using wordTrace_append hprefix tailTrace_5322368
  have hstable : (prefixWord ++ tailWord_5322368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5322368).length < 2 ^ (prefixWord ++ tailWord_5322368).sum := by decide
  have hdescent : baseEnd_5322368 < baseStart_5322368 := by decide
  rcases family_descends (prefixWord ++ tailWord_5322368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5322422 : List Nat := [5, 1, 3, 1, 1, 1, 2, 1, 1, 4, 3]
def baseStart_5322422 : Nat := 118140960795 + 5322422 * 2 ^ 59
def prefixEnd_5322422 : Nat := 4983230072969 + 3 ^ 40 * 5322422 * 2
def baseEnd_5322422 : Nat := 2732960732064480233147633

theorem tailTrace_5322422 : CollatzResearch.WordTrace tailWord_5322422 prefixEnd_5322422 2732960732064480233147633 := by
  unfold tailWord_5322422
  simp only [CollatzResearch.WordTrace]
  refine ⟨12132792395236347884608595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 129416452215854377435825013 12132792395236347884608595)
  ·
    refine ⟨18199188592854521826912893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12132792395236347884608595 18199188592854521826912893)
    ·
      refine ⟨6824695722320445685092335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18199188592854521826912893 6824695722320445685092335)
      ·
        refine ⟨10237043583480668527638503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6824695722320445685092335 10237043583480668527638503)
        ·
          refine ⟨15355565375221002791457755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10237043583480668527638503 15355565375221002791457755)
          ·
            refine ⟨23033348062831504187186633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15355565375221002791457755 23033348062831504187186633)
            ·
              refine ⟨17275011047123628140389975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23033348062831504187186633 17275011047123628140389975)
              ·
                refine ⟨25912516570685442210584963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17275011047123628140389975 25912516570685442210584963)
                ·
                  refine ⟨38868774856028163315877445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25912516570685442210584963 38868774856028163315877445)
                  ·
                    refine ⟨7287895285505280621727021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38868774856028163315877445 7287895285505280621727021)
                    ·
                      refine ⟨2732960732064480233147633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7287895285505280621727021 2732960732064480233147633)
                      ·
                        rfl

theorem cell23_5322422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_5322422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5322422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5322422 prefixEnd_5322422 := by exact prefixLift 5322422
  have htrace : WordTrace (prefixWord ++ tailWord_5322422) baseStart_5322422 baseEnd_5322422 := by
    simpa [prefixWord, tailWord_5322422, baseEnd_5322422] using wordTrace_append hprefix tailTrace_5322422
  have hstable : (prefixWord ++ tailWord_5322422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5322422).length < 2 ^ (prefixWord ++ tailWord_5322422).sum := by decide
  have hdescent : baseEnd_5322422 < baseStart_5322422 := by decide
  rcases family_descends (prefixWord ++ tailWord_5322422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5322468 : List Nat := [2, 3, 1, 1, 1, 3, 2, 3, 1, 6]
def baseStart_5322468 : Nat := 118140960795 + 5322468 * 2 ^ 59
def prefixEnd_5322468 : Nat := 4983230072969 + 3 ^ 40 * 5322468 * 2
def baseEnd_5322468 : Nat := 910994784058195684390807

theorem tailTrace_5322468 : CollatzResearch.WordTrace tailWord_5322468 prefixEnd_5322468 910994784058195684390807 := by
  unfold tailWord_5322468
  simp only [CollatzResearch.WordTrace]
  refine ⟨97063178040807458004956029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129417570721076610673274705 97063178040807458004956029)
  ·
    refine ⟨36398691765302796751858511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97063178040807458004956029 36398691765302796751858511)
    ·
      refine ⟨54598037647954195127787767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36398691765302796751858511 54598037647954195127787767)
      ·
        refine ⟨81897056471931292691681651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54598037647954195127787767 81897056471931292691681651)
        ·
          refine ⟨122845584707896939037522477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81897056471931292691681651 122845584707896939037522477)
          ·
            refine ⟨46067094265461352139070929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 122845584707896939037522477 46067094265461352139070929)
            ·
              refine ⟨34550320699096014104303197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46067094265461352139070929 34550320699096014104303197)
              ·
                refine ⟨12956370262161005289113699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34550320699096014104303197 12956370262161005289113699)
                ·
                  refine ⟨19434555393241507933670549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12956370262161005289113699 19434555393241507933670549)
                  ·
                    refine ⟨910994784058195684390807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19434555393241507933670549 910994784058195684390807)
                    ·
                      rfl

theorem cell23_5322468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 3, 1, 6].length) (baseStart_5322468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5322468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5322468 prefixEnd_5322468 := by exact prefixLift 5322468
  have htrace : WordTrace (prefixWord ++ tailWord_5322468) baseStart_5322468 baseEnd_5322468 := by
    simpa [prefixWord, tailWord_5322468, baseEnd_5322468] using wordTrace_append hprefix tailTrace_5322468
  have hstable : (prefixWord ++ tailWord_5322468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5322468).length < 2 ^ (prefixWord ++ tailWord_5322468).sum := by decide
  have hdescent : baseEnd_5322468 < baseStart_5322468 := by decide
  rcases family_descends (prefixWord ++ tailWord_5322468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5322472 : List Nat := [2, 1, 4, 1, 3, 3, 1, 2, 1, 5]
def baseStart_5322472 : Nat := 118140960795 + 5322472 * 2 ^ 59
def prefixEnd_5322472 : Nat := 4983230072969 + 3 ^ 40 * 5322472 * 2
def baseEnd_5322472 : Nat := 910995468699068345840801

theorem tailTrace_5322472 : CollatzResearch.WordTrace tailWord_5322472 prefixEnd_5322472 910995468699068345840801 := by
  unfold tailWord_5322472
  simp only [CollatzResearch.WordTrace]
  refine ⟨97063250986800212346528835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129417667982400283128705113 97063250986800212346528835)
  ·
    refine ⟨145594876480200318519793253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97063250986800212346528835 145594876480200318519793253)
    ·
      refine ⟨27299039340037559722461235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 145594876480200318519793253 27299039340037559722461235)
      ·
        refine ⟨40948559010056339583691853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27299039340037559722461235 40948559010056339583691853)
        ·
          refine ⟨15355709628771127343884445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40948559010056339583691853 15355709628771127343884445)
          ·
            refine ⟨5758391110789172753956667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15355709628771127343884445 5758391110789172753956667)
            ·
              refine ⟨8637586666183759130935001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5758391110789172753956667 8637586666183759130935001)
              ·
                refine ⟨6478189999637819348201251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8637586666183759130935001 6478189999637819348201251)
                ·
                  refine ⟨9717284999456729022301877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6478189999637819348201251 9717284999456729022301877)
                  ·
                    refine ⟨910995468699068345840801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9717284999456729022301877 910995468699068345840801)
                    ·
                      rfl

theorem cell23_5322472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 2, 1, 5].length) (baseStart_5322472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5322472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5322472 prefixEnd_5322472 := by exact prefixLift 5322472
  have htrace : WordTrace (prefixWord ++ tailWord_5322472) baseStart_5322472 baseEnd_5322472 := by
    simpa [prefixWord, tailWord_5322472, baseEnd_5322472] using wordTrace_append hprefix tailTrace_5322472
  have hstable : (prefixWord ++ tailWord_5322472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5322472).length < 2 ^ (prefixWord ++ tailWord_5322472).sum := by decide
  have hdescent : baseEnd_5322472 < baseStart_5322472 := by decide
  rcases family_descends (prefixWord ++ tailWord_5322472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5322475 : List Nat := [1, 1, 1, 1, 2, 4, 5, 2, 1, 1, 4]
def baseStart_5322475 : Nat := 118140960795 + 5322475 * 2 ^ 59
def prefixEnd_5322475 : Nat := 4983230072969 + 3 ^ 40 * 5322475 * 2
def baseEnd_5322475 : Nat := 2732987946539168525784889

theorem tailTrace_5322475 : CollatzResearch.WordTrace tailWord_5322475 prefixEnd_5322475 2732987946539168525784889 := by
  unfold tailWord_5322475
  simp only [CollatzResearch.WordTrace]
  refine ⟨194126611392589556205416879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129417740928393037470277919 194126611392589556205416879)
  ·
    refine ⟨291189917088884334308125319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194126611392589556205416879 291189917088884334308125319)
    ·
      refine ⟨436784875633326501462187979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 291189917088884334308125319 436784875633326501462187979)
      ·
        refine ⟨655177313449989752193281969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 436784875633326501462187979 655177313449989752193281969)
        ·
          refine ⟨491382985087492314144961477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 655177313449989752193281969 491382985087492314144961477)
          ·
            refine ⟨92134309703904808902180277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 491382985087492314144961477 92134309703904808902180277)
            ·
              refine ⟨8637591534741075834579401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 92134309703904808902180277 8637591534741075834579401)
              ·
                refine ⟨6478193651055806875934551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8637591534741075834579401 6478193651055806875934551)
                ·
                  refine ⟨9717290476583710313901827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6478193651055806875934551 9717290476583710313901827)
                  ·
                    refine ⟨14575935714875565470852741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9717290476583710313901827 14575935714875565470852741)
                    ·
                      refine ⟨2732987946539168525784889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14575935714875565470852741 2732987946539168525784889)
                      ·
                        rfl

theorem cell23_5322475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 2, 1, 1, 4].length) (baseStart_5322475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5322475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5322475 prefixEnd_5322475 := by exact prefixLift 5322475
  have htrace : WordTrace (prefixWord ++ tailWord_5322475) baseStart_5322475 baseEnd_5322475 := by
    simpa [prefixWord, tailWord_5322475, baseEnd_5322475] using wordTrace_append hprefix tailTrace_5322475
  have hstable : (prefixWord ++ tailWord_5322475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5322475).length < 2 ^ (prefixWord ++ tailWord_5322475).sum := by decide
  have hdescent : baseEnd_5322475 < baseStart_5322475 := by decide
  rcases family_descends (prefixWord ++ tailWord_5322475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5322492 : List Nat := [2, 2, 2, 1, 3, 1, 5, 1, 1, 1, 4]
def baseStart_5322492 : Nat := 118140960795 + 5322492 * 2 ^ 59
def prefixEnd_5322492 : Nat := 4983230072969 + 3 ^ 40 * 5322492 * 2
def baseEnd_5322492 : Nat := 2732996675710294959272311

theorem tailTrace_5322492 : CollatzResearch.WordTrace tailWord_5322492 prefixEnd_5322492 2732996675710294959272311 := by
  unfold tailWord_5322492
  simp only [CollatzResearch.WordTrace]
  refine ⟨97063615716763984054392865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129418154289018645405857153 97063615716763984054392865)
  ·
    refine ⟨72797711787572988040794649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97063615716763984054392865 72797711787572988040794649)
    ·
      refine ⟨54598283840679741030595987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72797711787572988040794649 54598283840679741030595987)
      ·
        refine ⟨81897425761019611545893981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54598283840679741030595987 81897425761019611545893981)
        ·
          refine ⟨30711534660382354329710243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81897425761019611545893981 30711534660382354329710243)
          ·
            refine ⟨46067301990573531494565365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30711534660382354329710243 46067301990573531494565365)
            ·
              refine ⟨4318809561616268577615503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46067301990573531494565365 4318809561616268577615503)
              ·
                refine ⟨6478214342424402866423255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4318809561616268577615503 6478214342424402866423255)
                ·
                  refine ⟨9717321513636604299634883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6478214342424402866423255 9717321513636604299634883)
                  ·
                    refine ⟨14575982270454906449452325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9717321513636604299634883 14575982270454906449452325)
                    ·
                      refine ⟨2732996675710294959272311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14575982270454906449452325 2732996675710294959272311)
                      ·
                        rfl

theorem cell23_5322492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 5, 1, 1, 1, 4].length) (baseStart_5322492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5322492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5322492 prefixEnd_5322492 := by exact prefixLift 5322492
  have htrace : WordTrace (prefixWord ++ tailWord_5322492) baseStart_5322492 baseEnd_5322492 := by
    simpa [prefixWord, tailWord_5322492, baseEnd_5322492] using wordTrace_append hprefix tailTrace_5322492
  have hstable : (prefixWord ++ tailWord_5322492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5322492).length < 2 ^ (prefixWord ++ tailWord_5322492).sum := by decide
  have hdescent : baseEnd_5322492 < baseStart_5322492 := by decide
  rcases family_descends (prefixWord ++ tailWord_5322492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5322495 : List Nat := [1, 1, 2, 2, 1, 3, 2, 5, 1, 2, 3]
def baseStart_5322495 : Nat := 118140960795 + 5322495 * 2 ^ 59
def prefixEnd_5322495 : Nat := 4983230072969 + 3 ^ 40 * 5322495 * 2
def baseEnd_5322495 : Nat := 2732998216152258447534797

theorem tailTrace_5322495 : CollatzResearch.WordTrace tailWord_5322495 prefixEnd_5322495 2732998216152258447534797 := by
  unfold tailWord_5322495
  simp only [CollatzResearch.WordTrace]
  refine ⟨194127340852517099621144939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129418227235011399747429959 194127340852517099621144939)
  ·
    refine ⟨291191011278775649431717409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194127340852517099621144939 291191011278775649431717409)
    ·
      refine ⟨218393258459081737073788057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 291191011278775649431717409 218393258459081737073788057)
      ·
        refine ⟨163794943844311302805341043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 218393258459081737073788057 163794943844311302805341043)
        ·
          refine ⟨245692415766466954208011565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163794943844311302805341043 245692415766466954208011565)
          ·
            refine ⟨92134655912425107828004337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 245692415766466954208011565 92134655912425107828004337)
            ·
              refine ⟨69100991934318830871003253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92134655912425107828004337 69100991934318830871003253)
              ·
                refine ⟨6478217993842390394156555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 69100991934318830871003253 6478217993842390394156555)
                ·
                  refine ⟨9717326990763585591234833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6478217993842390394156555 9717326990763585591234833)
                  ·
                    refine ⟨7287995243072689193426125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9717326990763585591234833 7287995243072689193426125)
                    ·
                      refine ⟨2732998216152258447534797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7287995243072689193426125 2732998216152258447534797)
                      ·
                        rfl

theorem cell23_5322495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 5, 1, 2, 3].length) (baseStart_5322495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5322495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5322495 prefixEnd_5322495 := by exact prefixLift 5322495
  have htrace : WordTrace (prefixWord ++ tailWord_5322495) baseStart_5322495 baseEnd_5322495 := by
    simpa [prefixWord, tailWord_5322495, baseEnd_5322495] using wordTrace_append hprefix tailTrace_5322495
  have hstable : (prefixWord ++ tailWord_5322495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5322495).length < 2 ^ (prefixWord ++ tailWord_5322495).sum := by decide
  have hdescent : baseEnd_5322495 < baseStart_5322495 := by decide
  rcases family_descends (prefixWord ++ tailWord_5322495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5322503 : List Nat := [1, 1, 4, 4, 2, 2, 2, 2, 1, 1, 3]
def baseStart_5322503 : Nat := 118140960795 + 5322503 * 2 ^ 59
def prefixEnd_5322503 : Nat := 4983230072969 + 3 ^ 40 * 5322503 * 2
def baseEnd_5322503 : Nat := 2733002323997494416234761

theorem tailTrace_5322503 : CollatzResearch.WordTrace tailWord_5322503 prefixEnd_5322503 2733002323997494416234761 := by
  unfold tailWord_5322503
  simp only [CollatzResearch.WordTrace]
  refine ⟨194127632636488116987436163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129418421757658744658290775 194127632636488116987436163)
  ·
    refine ⟨291191448954732175481154245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194127632636488116987436163 291191448954732175481154245)
    ·
      refine ⟨54598396679012282902716421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 291191448954732175481154245 54598396679012282902716421)
      ·
        refine ⟨10237199377314803044259329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54598396679012282902716421 10237199377314803044259329)
        ·
          refine ⟨7677899532986102283194497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10237199377314803044259329 7677899532986102283194497)
          ·
            refine ⟨5758424649739576712395873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7677899532986102283194497 5758424649739576712395873)
            ·
              refine ⟨4318818487304682534296905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5758424649739576712395873 4318818487304682534296905)
              ·
                refine ⟨3239113865478511900722679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4318818487304682534296905 3239113865478511900722679)
                ·
                  refine ⟨4858670798217767851084019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3239113865478511900722679 4858670798217767851084019)
                  ·
                    refine ⟨7288006197326651776626029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4858670798217767851084019 7288006197326651776626029)
                    ·
                      refine ⟨2733002323997494416234761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7288006197326651776626029 2733002323997494416234761)
                      ·
                        rfl

theorem cell23_5322503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 2, 2, 1, 1, 3].length) (baseStart_5322503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5322503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5322503 prefixEnd_5322503 := by exact prefixLift 5322503
  have htrace : WordTrace (prefixWord ++ tailWord_5322503) baseStart_5322503 baseEnd_5322503 := by
    simpa [prefixWord, tailWord_5322503, baseEnd_5322503] using wordTrace_append hprefix tailTrace_5322503
  have hstable : (prefixWord ++ tailWord_5322503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5322503).length < 2 ^ (prefixWord ++ tailWord_5322503).sum := by decide
  have hdescent : baseEnd_5322503 < baseStart_5322503 := by decide
  rcases family_descends (prefixWord ++ tailWord_5322503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5322528 : List Nat := [2, 1, 1, 5, 1, 1, 1, 2, 2, 7]
def baseStart_5322528 : Nat := 118140960795 + 5322528 * 2 ^ 59
def prefixEnd_5322528 : Nat := 4983230072969 + 3 ^ 40 * 5322528 * 2
def baseEnd_5322528 : Nat := 911005053671285606140715

theorem tailTrace_5322528 : CollatzResearch.WordTrace tailWord_5322528 prefixEnd_5322528 911005053671285606140715 := by
  unfold tailWord_5322528
  simp only [CollatzResearch.WordTrace]
  refine ⟨97064272230698773128548119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129419029640931697504730825 97064272230698773128548119)
  ·
    refine ⟨145596408346048159692822179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97064272230698773128548119 145596408346048159692822179)
    ·
      refine ⟨218394612519072239539233269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145596408346048159692822179 218394612519072239539233269)
      ·
        refine ⟨20474494923663022456803119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 218394612519072239539233269 20474494923663022456803119)
        ·
          refine ⟨30711742385494533685204679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20474494923663022456803119 30711742385494533685204679)
          ·
            refine ⟨46067613578241800527807019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30711742385494533685204679 46067613578241800527807019)
            ·
              refine ⟨69101420367362700791710529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46067613578241800527807019 69101420367362700791710529)
              ·
                refine ⟨51826065275522025593782897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69101420367362700791710529 51826065275522025593782897)
                ·
                  refine ⟨38869548956641519195337173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51826065275522025593782897 38869548956641519195337173)
                  ·
                    refine ⟨911005053671285606140715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38869548956641519195337173 911005053671285606140715)
                    ·
                      rfl

theorem cell23_5322528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 2, 2, 7].length) (baseStart_5322528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5322528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5322528 prefixEnd_5322528 := by exact prefixLift 5322528
  have htrace : WordTrace (prefixWord ++ tailWord_5322528) baseStart_5322528 baseEnd_5322528 := by
    simpa [prefixWord, tailWord_5322528, baseEnd_5322528] using wordTrace_append hprefix tailTrace_5322528
  have hstable : (prefixWord ++ tailWord_5322528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5322528).length < 2 ^ (prefixWord ++ tailWord_5322528).sum := by decide
  have hdescent : baseEnd_5322528 < baseStart_5322528 := by decide
  rcases family_descends (prefixWord ++ tailWord_5322528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5322652 : List Nat := [2, 2, 3, 3, 1, 1, 1, 3, 2, 5]
def baseStart_5322652 : Nat := 118140960795 + 5322652 * 2 ^ 59
def prefixEnd_5322652 : Nat := 4983230072969 + 3 ^ 40 * 5322652 * 2
def baseEnd_5322652 : Nat := 911026277538338111090525

theorem tailTrace_5322652 : CollatzResearch.WordTrace tailWord_5322652 prefixEnd_5322652 911026277538338111090525 := by
  unfold tailWord_5322652
  simp only [CollatzResearch.WordTrace]
  refine ⟨97066533556474157717305105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129422044741965543623073473 97066533556474157717305105)
  ·
    refine ⟨72799900167355618287978829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97066533556474157717305105 72799900167355618287978829)
    ·
      refine ⟨27299962562758356857992061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72799900167355618287978829 27299962562758356857992061)
      ·
        refine ⟨10237485961034383821747023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27299962562758356857992061 10237485961034383821747023)
        ·
          refine ⟨15356228941551575732620535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10237485961034383821747023 15356228941551575732620535)
          ·
            refine ⟨23034343412327363598930803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15356228941551575732620535 23034343412327363598930803)
            ·
              refine ⟨34551515118491045398396205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23034343412327363598930803 34551515118491045398396205)
              ·
                refine ⟨12956818169434142024398577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34551515118491045398396205 12956818169434142024398577)
                ·
                  refine ⟨9717613627075606518298933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12956818169434142024398577 9717613627075606518298933)
                  ·
                    refine ⟨911026277538338111090525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9717613627075606518298933 911026277538338111090525)
                    ·
                      rfl

theorem cell23_5322652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 3, 2, 5].length) (baseStart_5322652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5322652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5322652 prefixEnd_5322652 := by exact prefixLift 5322652
  have htrace : WordTrace (prefixWord ++ tailWord_5322652) baseStart_5322652 baseEnd_5322652 := by
    simpa [prefixWord, tailWord_5322652, baseEnd_5322652] using wordTrace_append hprefix tailTrace_5322652
  have hstable : (prefixWord ++ tailWord_5322652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5322652).length < 2 ^ (prefixWord ++ tailWord_5322652).sum := by decide
  have hdescent : baseEnd_5322652 < baseStart_5322652 := by decide
  rcases family_descends (prefixWord ++ tailWord_5322652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5322665 : List Nat := [1, 2, 1, 1, 1, 1, 4, 1, 7, 4]
def baseStart_5322665 : Nat := 118140960795 + 5322665 * 2 ^ 59
def prefixEnd_5322665 : Nat := 4983230072969 + 3 ^ 40 * 5322665 * 2
def baseEnd_5322665 : Nat := 911028502621174260803005

theorem tailTrace_5322665 : CollatzResearch.WordTrace tailWord_5322665 prefixEnd_5322665 911028502621174260803005 := by
  unfold tailWord_5322665
  simp only [CollatzResearch.WordTrace]
  refine ⟨194133541261901218654833449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129422360841267479103222299 194133541261901218654833449)
  ·
    refine ⟨145600155946425913991125087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194133541261901218654833449 145600155946425913991125087)
    ·
      refine ⟨218400233919638870986687631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145600155946425913991125087 218400233919638870986687631)
      ·
        refine ⟨327600350879458306480031447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218400233919638870986687631 327600350879458306480031447)
        ·
          refine ⟨491400526319187459720047171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 327600350879458306480031447 491400526319187459720047171)
          ·
            refine ⟨737100789478781189580070757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 491400526319187459720047171 737100789478781189580070757)
            ·
              refine ⟨138206398027271473046263267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 737100789478781189580070757 138206398027271473046263267)
              ·
                refine ⟨207309597040907209569394901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 138206398027271473046263267 207309597040907209569394901)
                ·
                  refine ⟨4858818680646262724282693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 207309597040907209569394901 4858818680646262724282693)
                  ·
                    refine ⟨911028502621174260803005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4858818680646262724282693 911028502621174260803005)
                    ·
                      rfl

theorem cell23_5322665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 7, 4].length) (baseStart_5322665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5322665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5322665 prefixEnd_5322665 := by exact prefixLift 5322665
  have htrace : WordTrace (prefixWord ++ tailWord_5322665) baseStart_5322665 baseEnd_5322665 := by
    simpa [prefixWord, tailWord_5322665, baseEnd_5322665] using wordTrace_append hprefix tailTrace_5322665
  have hstable : (prefixWord ++ tailWord_5322665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5322665).length < 2 ^ (prefixWord ++ tailWord_5322665).sum := by decide
  have hdescent : baseEnd_5322665 < baseStart_5322665 := by decide
  rcases family_descends (prefixWord ++ tailWord_5322665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5322705 : List Nat := [1, 2, 2, 1, 2, 1, 2, 1, 1, 7, 3]
def baseStart_5322705 : Nat := 118140960795 + 5322705 * 2 ^ 59
def prefixEnd_5322705 : Nat := 4983230072969 + 3 ^ 40 * 5322705 * 2
def baseEnd_5322705 : Nat := 2733106047089702625908831

theorem tailTrace_5322705 : CollatzResearch.WordTrace tailWord_5322705 prefixEnd_5322705 2733106047089702625908831 := by
  unfold tailWord_5322705
  simp only [CollatzResearch.WordTrace]
  refine ⟨194135000181756305486289569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129423333454504203657526379 194135000181756305486289569)
  ·
    refine ⟨145601250136317229114717177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194135000181756305486289569 145601250136317229114717177)
    ·
      refine ⟨109200937602237921836037883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145601250136317229114717177 109200937602237921836037883)
      ·
        refine ⟨163801406403356882754056825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109200937602237921836037883 163801406403356882754056825)
        ·
          refine ⟨122851054802517662065542619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163801406403356882754056825 122851054802517662065542619)
          ·
            refine ⟨184276582203776493098313929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122851054802517662065542619 184276582203776493098313929)
            ·
              refine ⟨138207436652832369823735447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 184276582203776493098313929 138207436652832369823735447)
              ·
                refine ⟨207311154979248554735603171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 138207436652832369823735447 207311154979248554735603171)
                ·
                  refine ⟨310966732468872832103404757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 207311154979248554735603171 310966732468872832103404757)
                  ·
                    refine ⟨7288282792239207002423549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 310966732468872832103404757 7288282792239207002423549)
                    ·
                      refine ⟨2733106047089702625908831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7288282792239207002423549 2733106047089702625908831)
                      ·
                        rfl

theorem cell23_5322705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 7, 3].length) (baseStart_5322705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5322705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5322705 prefixEnd_5322705 := by exact prefixLift 5322705
  have htrace : WordTrace (prefixWord ++ tailWord_5322705) baseStart_5322705 baseEnd_5322705 := by
    simpa [prefixWord, tailWord_5322705, baseEnd_5322705] using wordTrace_append hprefix tailTrace_5322705
  have hstable : (prefixWord ++ tailWord_5322705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5322705).length < 2 ^ (prefixWord ++ tailWord_5322705).sum := by decide
  have hdescent : baseEnd_5322705 < baseStart_5322705 := by decide
  rcases family_descends (prefixWord ++ tailWord_5322705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5322706 : List Nat := [3, 2, 2, 3, 2, 2, 1, 1, 2, 1, 4]
def baseStart_5322706 : Nat := 118140960795 + 5322706 * 2 ^ 59
def prefixEnd_5322706 : Nat := 4983230072969 + 3 ^ 40 * 5322706 * 2
def baseEnd_5322706 : Nat := 2733106560570357121996327

theorem tailTrace_5322706 : CollatzResearch.WordTrace tailWord_5322706 prefixEnd_5322706 2733106560570357121996327 := by
  unfold tailWord_5322706
  simp only [CollatzResearch.WordTrace]
  refine ⟨48533759163688170664268993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129423357769835121771383981 48533759163688170664268993)
  ·
    refine ⟨36400319372766127998201745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48533759163688170664268993 36400319372766127998201745)
    ·
      refine ⟨27300239529574595998651309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36400319372766127998201745 27300239529574595998651309)
      ·
        refine ⟨10237589823590473499494241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27300239529574595998651309 10237589823590473499494241)
        ·
          refine ⟨7678192367692855124620681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10237589823590473499494241 7678192367692855124620681)
          ·
            refine ⟨5758644275769641343465511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7678192367692855124620681 5758644275769641343465511)
            ·
              refine ⟨8637966413654462015198267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5758644275769641343465511 8637966413654462015198267)
              ·
                refine ⟨12956949620481693022797401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8637966413654462015198267 12956949620481693022797401)
                ·
                  refine ⟨9717712215361269767098051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12956949620481693022797401 9717712215361269767098051)
                  ·
                    refine ⟨14576568323041904650647077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9717712215361269767098051 14576568323041904650647077)
                    ·
                      refine ⟨2733106560570357121996327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14576568323041904650647077 2733106560570357121996327)
                      ·
                        rfl

theorem cell23_5322706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_5322706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5322706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5322706 prefixEnd_5322706 := by exact prefixLift 5322706
  have htrace : WordTrace (prefixWord ++ tailWord_5322706) baseStart_5322706 baseEnd_5322706 := by
    simpa [prefixWord, tailWord_5322706, baseEnd_5322706] using wordTrace_append hprefix tailTrace_5322706
  have hstable : (prefixWord ++ tailWord_5322706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5322706).length < 2 ^ (prefixWord ++ tailWord_5322706).sum := by decide
  have hdescent : baseEnd_5322706 < baseStart_5322706 := by decide
  rcases family_descends (prefixWord ++ tailWord_5322706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5322709 : List Nat := [1, 3, 2, 3, 2, 1, 3, 1, 2, 2, 3]
def baseStart_5322709 : Nat := 118140960795 + 5322709 * 2 ^ 59
def prefixEnd_5322709 : Nat := 4983230072969 + 3 ^ 40 * 5322709 * 2
def baseEnd_5322709 : Nat := 2733108101012320610258813

theorem tailTrace_5322709 : CollatzResearch.WordTrace tailWord_5322709 prefixEnd_5322709 2733108101012320610258813 := by
  unfold tailWord_5322709
  simp only [CollatzResearch.WordTrace]
  refine ⟨194135146073741814169435181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129423430715827876112956787 194135146073741814169435181)
  ·
    refine ⟨72800679777653180313538193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 194135146073741814169435181 72800679777653180313538193)
    ·
      refine ⟨54600509833239885235153645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72800679777653180313538193 54600509833239885235153645)
      ·
        refine ⟨20475191187464956963182617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54600509833239885235153645 20475191187464956963182617)
        ·
          refine ⟨15356393390598717722386963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20475191187464956963182617 15356393390598717722386963)
          ·
            refine ⟨23034590085898076583580445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15356393390598717722386963 23034590085898076583580445)
            ·
              refine ⟨8637971282211778718842667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23034590085898076583580445 8637971282211778718842667)
              ·
                refine ⟨12956956923317668078264001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8637971282211778718842667 12956956923317668078264001)
                ·
                  refine ⟨9717717692488251058698001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12956956923317668078264001 9717717692488251058698001)
                  ·
                    refine ⟨7288288269366188294023501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9717717692488251058698001 7288288269366188294023501)
                    ·
                      refine ⟨2733108101012320610258813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7288288269366188294023501 2733108101012320610258813)
                      ·
                        rfl

theorem cell23_5322709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 1, 2, 2, 3].length) (baseStart_5322709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5322709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5322709 prefixEnd_5322709 := by exact prefixLift 5322709
  have htrace : WordTrace (prefixWord ++ tailWord_5322709) baseStart_5322709 baseEnd_5322709 := by
    simpa [prefixWord, tailWord_5322709, baseEnd_5322709] using wordTrace_append hprefix tailTrace_5322709
  have hstable : (prefixWord ++ tailWord_5322709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5322709).length < 2 ^ (prefixWord ++ tailWord_5322709).sum := by decide
  have hdescent : baseEnd_5322709 < baseStart_5322709 := by decide
  rcases family_descends (prefixWord ++ tailWord_5322709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5322759 : List Nat := [1, 1, 4, 3, 1, 3, 2, 2, 1, 5]
def baseStart_5322759 : Nat := 118140960795 + 5322759 * 2 ^ 59
def prefixEnd_5322759 : Nat := 4983230072969 + 3 ^ 40 * 5322759 * 2
def baseEnd_5322759 : Nat := 911044591681681804877861

theorem tailTrace_5322759 : CollatzResearch.WordTrace tailWord_5322759 prefixEnd_5322759 911044591681681804877861 := by
  unfold tailWord_5322759
  simp only [CollatzResearch.WordTrace]
  refine ⟨194136969723560672708755331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129424646482373781805836887 194136969723560672708755331)
  ·
    refine ⟨291205454585341009063132997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194136969723560672708755331 291205454585341009063132997)
    ·
      refine ⟨54601022734751439199337437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 291205454585341009063132997 54601022734751439199337437)
      ·
        refine ⟨20475383525531789699751539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54601022734751439199337437 20475383525531789699751539)
        ·
          refine ⟨30713075288297684549627309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20475383525531789699751539 30713075288297684549627309)
          ·
            refine ⟨11517403233111631706110241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30713075288297684549627309 11517403233111631706110241)
            ·
              refine ⟨8638052424833723779582681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11517403233111631706110241 8638052424833723779582681)
              ·
                refine ⟨6478539318625292834687011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8638052424833723779582681 6478539318625292834687011)
                ·
                  refine ⟨9717808977937939252030517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6478539318625292834687011 9717808977937939252030517)
                  ·
                    refine ⟨911044591681681804877861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9717808977937939252030517 911044591681681804877861)
                    ·
                      rfl

theorem cell23_5322759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 2, 1, 5].length) (baseStart_5322759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5322759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5322759 prefixEnd_5322759 := by exact prefixLift 5322759
  have htrace : WordTrace (prefixWord ++ tailWord_5322759) baseStart_5322759 baseEnd_5322759 := by
    simpa [prefixWord, tailWord_5322759, baseEnd_5322759] using wordTrace_append hprefix tailTrace_5322759
  have hstable : (prefixWord ++ tailWord_5322759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5322759).length < 2 ^ (prefixWord ++ tailWord_5322759).sum := by decide
  have hdescent : baseEnd_5322759 < baseStart_5322759 := by decide
  rcases family_descends (prefixWord ++ tailWord_5322759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5322802 : List Nat := [3, 2, 1, 1, 2, 4, 2, 8]
def baseStart_5322802 : Nat := 118140960795 + 5322802 * 2 ^ 59
def prefixEnd_5322802 : Nat := 4983230072969 + 3 ^ 40 * 5322802 * 2
def baseEnd_5322802 : Nat := 101227994619006990607255

theorem tailTrace_5322802 : CollatzResearch.WordTrace tailWord_5322802 prefixEnd_5322802 101227994619006990607255 := by
  unfold tailWord_5322802
  simp only [CollatzResearch.WordTrace]
  refine ⟨48534634515601222763142665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129425692041603260701713773 48534634515601222763142665)
  ·
    refine ⟨36400975886700917072356999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48534634515601222763142665 36400975886700917072356999)
    ·
      refine ⟨54601463830051375608535499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36400975886700917072356999 54601463830051375608535499)
      ·
        refine ⟨81902195745077063412803249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54601463830051375608535499 81902195745077063412803249)
        ·
          refine ⟨61426646808807797559602437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81902195745077063412803249 61426646808807797559602437)
          ·
            refine ⟨11517496276651462042425457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61426646808807797559602437 11517496276651462042425457)
            ·
              refine ⟨8638122207488596531819093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11517496276651462042425457 8638122207488596531819093)
              ·
                refine ⟨101227994619006990607255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8638122207488596531819093 101227994619006990607255)
                ·
                  rfl

theorem cell23_5322802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 8].length) (baseStart_5322802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5322802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5322802 prefixEnd_5322802 := by exact prefixLift 5322802
  have htrace : WordTrace (prefixWord ++ tailWord_5322802) baseStart_5322802 baseEnd_5322802 := by
    simpa [prefixWord, tailWord_5322802, baseEnd_5322802] using wordTrace_append hprefix tailTrace_5322802
  have hstable : (prefixWord ++ tailWord_5322802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5322802).length < 2 ^ (prefixWord ++ tailWord_5322802).sum := by decide
  have hdescent : baseEnd_5322802 < baseStart_5322802 := by decide
  rcases family_descends (prefixWord ++ tailWord_5322802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5322806 : List Nat := [5, 1, 2, 1, 1, 1, 3, 3, 2, 4]
def baseStart_5322806 : Nat := 118140960795 + 5322806 * 2 ^ 59
def prefixEnd_5322806 : Nat := 4983230072969 + 3 ^ 40 * 5322806 * 2
def baseEnd_5322806 : Nat := 911052636211935576915289

theorem tailTrace_5322806 : CollatzResearch.WordTrace tailWord_5322806 prefixEnd_5322806 911052636211935576915289 := by
  unfold tailWord_5322806
  simp only [CollatzResearch.WordTrace]
  refine ⟨12133667747149399983482267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 129425789302926933157144181 12133667747149399983482267)
  ·
    refine ⟨18200501620724099975223401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12133667747149399983482267 18200501620724099975223401)
    ·
      refine ⟨13650376215543074981417551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18200501620724099975223401 13650376215543074981417551)
      ·
        refine ⟨20475564323314612472126327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13650376215543074981417551 20475564323314612472126327)
        ·
          refine ⟨30713346484971918708189491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20475564323314612472126327 30713346484971918708189491)
          ·
            refine ⟨46070019727457878062284237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30713346484971918708189491 46070019727457878062284237)
            ·
              refine ⟨17276257397796704273356589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46070019727457878062284237 17276257397796704273356589)
              ·
                refine ⟨6478596524173764102508721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17276257397796704273356589 6478596524173764102508721)
                ·
                  refine ⟨4858947393130323076881541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6478596524173764102508721 4858947393130323076881541)
                  ·
                    refine ⟨911052636211935576915289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4858947393130323076881541 911052636211935576915289)
                    ·
                      rfl

theorem cell23_5322806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 3, 2, 4].length) (baseStart_5322806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5322806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5322806 prefixEnd_5322806 := by exact prefixLift 5322806
  have htrace : WordTrace (prefixWord ++ tailWord_5322806) baseStart_5322806 baseEnd_5322806 := by
    simpa [prefixWord, tailWord_5322806, baseEnd_5322806] using wordTrace_append hprefix tailTrace_5322806
  have hstable : (prefixWord ++ tailWord_5322806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5322806).length < 2 ^ (prefixWord ++ tailWord_5322806).sum := by decide
  have hdescent : baseEnd_5322806 < baseStart_5322806 := by decide
  rcases family_descends (prefixWord ++ tailWord_5322806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5322816 : List Nat := [2, 1, 1, 2, 2, 6, 1, 2, 1, 2, 3]
def baseStart_5322816 : Nat := 118140960795 + 5322816 * 2 ^ 59
def prefixEnd_5322816 : Nat := 4983230072969 + 3 ^ 40 * 5322816 * 2
def baseEnd_5322816 : Nat := 2733163043442351691620821

theorem tailTrace_5322816 : CollatzResearch.WordTrace tailWord_5322816 prefixEnd_5322816 2733163043442351691620821 := by
  unfold tailWord_5322816
  simp only [CollatzResearch.WordTrace]
  refine ⟨97069524342177085721790151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129426032456236114295720201 97069524342177085721790151)
  ·
    refine ⟨145604286513265628582685227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97069524342177085721790151 145604286513265628582685227)
    ·
      refine ⟨218406429769898442874027841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145604286513265628582685227 218406429769898442874027841)
      ·
        refine ⟨163804822327423832155520881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 218406429769898442874027841 163804822327423832155520881)
        ·
          refine ⟨122853616745567874116640661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163804822327423832155520881 122853616745567874116640661)
          ·
            refine ⟨5758763284948494099217531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 122853616745567874116640661 5758763284948494099217531)
            ·
              refine ⟨8638144927422741148826297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5758763284948494099217531 8638144927422741148826297)
              ·
                refine ⟨6478608695567055861619723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8638144927422741148826297 6478608695567055861619723)
                ·
                  refine ⟨9717913043350583792429585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6478608695567055861619723 9717913043350583792429585)
                  ·
                    refine ⟨7288434782512937844322189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9717913043350583792429585 7288434782512937844322189)
                    ·
                      refine ⟨2733163043442351691620821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7288434782512937844322189 2733163043442351691620821)
                      ·
                        rfl

theorem cell23_5322816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 2, 1, 2, 3].length) (baseStart_5322816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5322816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5322816 prefixEnd_5322816 := by exact prefixLift 5322816
  have htrace : WordTrace (prefixWord ++ tailWord_5322816) baseStart_5322816 baseEnd_5322816 := by
    simpa [prefixWord, tailWord_5322816, baseEnd_5322816] using wordTrace_append hprefix tailTrace_5322816
  have hstable : (prefixWord ++ tailWord_5322816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5322816).length < 2 ^ (prefixWord ++ tailWord_5322816).sum := by decide
  have hdescent : baseEnd_5322816 < baseStart_5322816 := by decide
  rcases family_descends (prefixWord ++ tailWord_5322816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5322852 : List Nat := [2, 3, 1, 1, 2, 1, 3, 1, 2, 3, 4]
def baseStart_5322852 : Nat := 118140960795 + 5322852 * 2 ^ 59
def prefixEnd_5322852 : Nat := 4983230072969 + 3 ^ 40 * 5322852 * 2
def baseEnd_5322852 : Nat := 2733181528745913550770655

theorem tailTrace_5322852 : CollatzResearch.WordTrace tailWord_5322852 prefixEnd_5322852 2733181528745913550770655 := by
  unfold tailWord_5322852
  simp only [CollatzResearch.WordTrace]
  refine ⟨97070180856111874795945405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129426907808149166394593873 97070180856111874795945405)
  ·
    refine ⟨36401317821041953048479527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97070180856111874795945405 36401317821041953048479527)
    ·
      refine ⟨54601976731562929572719291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36401317821041953048479527 54601976731562929572719291)
      ·
        refine ⟨81902965097344394359078937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54601976731562929572719291 81902965097344394359078937)
        ·
          refine ⟨61427223823008295769309203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81902965097344394359078937 61427223823008295769309203)
          ·
            refine ⟨92140835734512443653963805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61427223823008295769309203 92140835734512443653963805)
            ·
              refine ⟨34552813400442166370236427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92140835734512443653963805 34552813400442166370236427)
              ·
                refine ⟨51829220100663249555354641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34552813400442166370236427 51829220100663249555354641)
                ·
                  refine ⟨38871915075497437166515981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51829220100663249555354641 38871915075497437166515981)
                  ·
                    refine ⟨14576968153311538937443493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38871915075497437166515981 14576968153311538937443493)
                    ·
                      refine ⟨2733181528745913550770655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14576968153311538937443493 2733181528745913550770655)
                      ·
                        rfl

theorem cell23_5322852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 1, 2, 3, 4].length) (baseStart_5322852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5322852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5322852 prefixEnd_5322852 := by exact prefixLift 5322852
  have htrace : WordTrace (prefixWord ++ tailWord_5322852) baseStart_5322852 baseEnd_5322852 := by
    simpa [prefixWord, tailWord_5322852, baseEnd_5322852] using wordTrace_append hprefix tailTrace_5322852
  have hstable : (prefixWord ++ tailWord_5322852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5322852).length < 2 ^ (prefixWord ++ tailWord_5322852).sum := by decide
  have hdescent : baseEnd_5322852 < baseStart_5322852 := by decide
  rcases family_descends (prefixWord ++ tailWord_5322852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5322872 : List Nat := [2, 1, 2, 1, 1, 1, 3, 1, 4, 4, 3]
def baseStart_5322872 : Nat := 118140960795 + 5322872 * 2 ^ 59
def prefixEnd_5322872 : Nat := 4983230072969 + 3 ^ 40 * 5322872 * 2
def baseEnd_5322872 : Nat := 2733191798359003472520563

theorem tailTrace_5322872 : CollatzResearch.WordTrace tailWord_5322872 prefixEnd_5322872 2733191798359003472520563 := by
  unfold tailWord_5322872
  simp only [CollatzResearch.WordTrace]
  refine ⟨97070545586075646503809435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129427394114767528671745913 97070545586075646503809435)
  ·
    refine ⟨145605818379113469755714153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97070545586075646503809435 145605818379113469755714153)
    ·
      refine ⟨109204363784335102316785615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145605818379113469755714153 109204363784335102316785615)
      ·
        refine ⟨163806545676502653475178423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109204363784335102316785615 163806545676502653475178423)
        ·
          refine ⟨245709818514753980212767635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163806545676502653475178423 245709818514753980212767635)
          ·
            refine ⟨368564727772130970319151453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 245709818514753980212767635 368564727772130970319151453)
            ·
              refine ⟨138211772914549113869681795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 368564727772130970319151453 138211772914549113869681795)
              ·
                refine ⟨207317659371823670804522693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 138211772914549113869681795 207317659371823670804522693)
                ·
                  refine ⟨38872061132216938275848005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 207317659371823670804522693 38872061132216938275848005)
                  ·
                    refine ⟨7288511462290675926721501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38872061132216938275848005 7288511462290675926721501)
                    ·
                      refine ⟨2733191798359003472520563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7288511462290675926721501 2733191798359003472520563)
                      ·
                        rfl

theorem cell23_5322872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 4, 4, 3].length) (baseStart_5322872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5322872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5322872 prefixEnd_5322872 := by exact prefixLift 5322872
  have htrace : WordTrace (prefixWord ++ tailWord_5322872) baseStart_5322872 baseEnd_5322872 := by
    simpa [prefixWord, tailWord_5322872, baseEnd_5322872] using wordTrace_append hprefix tailTrace_5322872
  have hstable : (prefixWord ++ tailWord_5322872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5322872).length < 2 ^ (prefixWord ++ tailWord_5322872).sum := by decide
  have hdescent : baseEnd_5322872 < baseStart_5322872 := by decide
  rcases family_descends (prefixWord ++ tailWord_5322872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5322890 : List Nat := [3, 1, 2, 3, 1, 4, 2, 1, 1, 3, 2]
def baseStart_5322890 : Nat := 118140960795 + 5322890 * 2 ^ 59
def prefixEnd_5322890 : Nat := 4983230072969 + 3 ^ 40 * 5322890 * 2
def baseEnd_5322890 : Nat := 2733201041010784402095481

theorem tailTrace_5322890 : CollatzResearch.WordTrace tailWord_5322890 prefixEnd_5322890 2733201041010784402095481 := by
  unfold tailWord_5322890
  simp only [CollatzResearch.WordTrace]
  refine ⟨48535436921521520520443531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129427831790724054721182749 48535436921521520520443531)
  ·
    refine ⟨72803155382282280780665297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48535436921521520520443531 72803155382282280780665297)
    ·
      refine ⟨54602366536711710585498973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72803155382282280780665297 54602366536711710585498973)
      ·
        refine ⟨20475887451266891469562115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54602366536711710585498973 20475887451266891469562115)
        ·
          refine ⟨30713831176900337204343173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20475887451266891469562115 30713831176900337204343173)
          ·
            refine ⟨5758843345668813225814345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30713831176900337204343173 5758843345668813225814345)
            ·
              refine ⟨4319132509251609919360759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5758843345668813225814345 4319132509251609919360759)
              ·
                refine ⟨6478698763877414879041139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4319132509251609919360759 6478698763877414879041139)
                ·
                  refine ⟨9718048145816122318561709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6478698763877414879041139 9718048145816122318561709)
                  ·
                    refine ⟨3644268054681045869460641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9718048145816122318561709 3644268054681045869460641)
                    ·
                      refine ⟨2733201041010784402095481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3644268054681045869460641 2733201041010784402095481)
                      ·
                        rfl

theorem cell23_5322890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 2, 1, 1, 3, 2].length) (baseStart_5322890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5322890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5322890 prefixEnd_5322890 := by exact prefixLift 5322890
  have htrace : WordTrace (prefixWord ++ tailWord_5322890) baseStart_5322890 baseEnd_5322890 := by
    simpa [prefixWord, tailWord_5322890, baseEnd_5322890] using wordTrace_append hprefix tailTrace_5322890
  have hstable : (prefixWord ++ tailWord_5322890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5322890).length < 2 ^ (prefixWord ++ tailWord_5322890).sum := by decide
  have hdescent : baseEnd_5322890 < baseStart_5322890 := by decide
  rcases family_descends (prefixWord ++ tailWord_5322890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5322903 : List Nat := [1, 1, 3, 3, 4, 1, 1, 1, 4, 2, 2]
def baseStart_5322903 : Nat := 118140960795 + 5322903 * 2 ^ 59
def prefixEnd_5322903 : Nat := 4983230072969 + 3 ^ 40 * 5322903 * 2
def baseEnd_5322903 : Nat := 2733207716259292851232921

theorem tailTrace_5322903 : CollatzResearch.WordTrace tailWord_5322903 prefixEnd_5322903 2733207716259292851232921 := by
  unfold tailWord_5322903
  simp only [CollatzResearch.WordTrace]
  refine ⟨194142221835038985301997363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129428147890025990201331575 194142221835038985301997363)
  ·
    refine ⟨291213332752558477952996045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194142221835038985301997363 291213332752558477952996045)
    ·
      refine ⟨109204999782209429232373517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 291213332752558477952996045 109204999782209429232373517)
      ·
        refine ⟨40951874918328535962140069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109204999782209429232373517 40951874918328535962140069)
        ·
          refine ⟨7678476547186600492901263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40951874918328535962140069 7678476547186600492901263)
          ·
            refine ⟨11517714820779900739351895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7678476547186600492901263 11517714820779900739351895)
            ·
              refine ⟨17276572231169851109027843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11517714820779900739351895 17276572231169851109027843)
              ·
                refine ⟨25914858346754776663541765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17276572231169851109027843 25914858346754776663541765)
                ·
                  refine ⟨4859035940016520624414081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25914858346754776663541765 4859035940016520624414081)
                  ·
                    refine ⟨3644276955012390468310561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4859035940016520624414081 3644276955012390468310561)
                    ·
                      refine ⟨2733207716259292851232921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3644276955012390468310561 2733207716259292851232921)
                      ·
                        rfl

theorem cell23_5322903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 1, 4, 2, 2].length) (baseStart_5322903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5322903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5322903 prefixEnd_5322903 := by exact prefixLift 5322903
  have htrace : WordTrace (prefixWord ++ tailWord_5322903) baseStart_5322903 baseEnd_5322903 := by
    simpa [prefixWord, tailWord_5322903, baseEnd_5322903] using wordTrace_append hprefix tailTrace_5322903
  have hstable : (prefixWord ++ tailWord_5322903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5322903).length < 2 ^ (prefixWord ++ tailWord_5322903).sum := by decide
  have hdescent : baseEnd_5322903 < baseStart_5322903 := by decide
  rcases family_descends (prefixWord ++ tailWord_5322903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5322909 : List Nat := [1, 4, 2, 1, 1, 4, 2, 1, 7]
def baseStart_5322909 : Nat := 118140960795 + 5322909 * 2 ^ 59
def prefixEnd_5322909 : Nat := 4983230072969 + 3 ^ 40 * 5322909 * 2
def baseEnd_5322909 : Nat := 303690088571468869750877

theorem tailTrace_5322909 : CollatzResearch.WordTrace tailWord_5322909 prefixEnd_5322909 303690088571468869750877 := by
  unfold tailWord_5322909
  simp only [CollatzResearch.WordTrace]
  refine ⟨194142440673017248326715781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129428293782011498884477187 194142440673017248326715781)
  ·
    refine ⟨36401707626190734061259209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 194142440673017248326715781 36401707626190734061259209)
    ·
      refine ⟨27301280719643050545944407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36401707626190734061259209 27301280719643050545944407)
      ·
        refine ⟨40951921079464575818916611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27301280719643050545944407 40951921079464575818916611)
        ·
          refine ⟨61427881619196863728374917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40951921079464575818916611 61427881619196863728374917)
          ·
            refine ⟨11517727803599411949070297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61427881619196863728374917 11517727803599411949070297)
            ·
              refine ⟨8638295852699558961802723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11517727803599411949070297 8638295852699558961802723)
              ·
                refine ⟨12957443779049338442704085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8638295852699558961802723 12957443779049338442704085)
                ·
                  refine ⟨303690088571468869750877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12957443779049338442704085 303690088571468869750877)
                  ·
                    rfl

theorem cell23_5322909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 1, 7].length) (baseStart_5322909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5322909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5322909 prefixEnd_5322909 := by exact prefixLift 5322909
  have htrace : WordTrace (prefixWord ++ tailWord_5322909) baseStart_5322909 baseEnd_5322909 := by
    simpa [prefixWord, tailWord_5322909, baseEnd_5322909] using wordTrace_append hprefix tailTrace_5322909
  have hstable : (prefixWord ++ tailWord_5322909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5322909).length < 2 ^ (prefixWord ++ tailWord_5322909).sum := by decide
  have hdescent : baseEnd_5322909 < baseStart_5322909 := by decide
  rcases family_descends (prefixWord ++ tailWord_5322909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5322959 : List Nat := [1, 1, 2, 1, 1, 3, 5, 2, 2, 1, 4]
def baseStart_5322959 : Nat := 118140960795 + 5322959 * 2 ^ 59
def prefixEnd_5322959 : Nat := 4983230072969 + 3 ^ 40 * 5322959 * 2
def baseEnd_5322959 : Nat := 2733236471175944632132663

theorem tailTrace_5322959 : CollatzResearch.WordTrace tailWord_5322959 prefixEnd_5322959 2733236471175944632132663 := by
  unfold tailWord_5322959
  simp only [CollatzResearch.WordTrace]
  refine ⟨194144264322836106866035931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129429509548557404577357287 194144264322836106866035931)
  ·
    refine ⟨291216396484254160299053897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194144264322836106866035931 291216396484254160299053897)
    ·
      refine ⟨218412297363190620224290423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 291216396484254160299053897 218412297363190620224290423)
      ·
        refine ⟨327618446044785930336435635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218412297363190620224290423 327618446044785930336435635)
        ·
          refine ⟨491427669067178895504653453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 327618446044785930336435635 491427669067178895504653453)
          ·
            refine ⟨184285375900192085814245045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 491427669067178895504653453 184285375900192085814245045)
            ·
              refine ⟨17276753990643008045085473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 184285375900192085814245045 17276753990643008045085473)
              ·
                refine ⟨12957565492982256033814105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17276753990643008045085473 12957565492982256033814105)
                ·
                  refine ⟨9718174119736692025360579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12957565492982256033814105 9718174119736692025360579)
                  ·
                    refine ⟨14577261179605038038040869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9718174119736692025360579 14577261179605038038040869)
                    ·
                      refine ⟨2733236471175944632132663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14577261179605038038040869 2733236471175944632132663)
                      ·
                        rfl

theorem cell23_5322959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 2, 2, 1, 4].length) (baseStart_5322959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5322959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5322959 prefixEnd_5322959 := by exact prefixLift 5322959
  have htrace : WordTrace (prefixWord ++ tailWord_5322959) baseStart_5322959 baseEnd_5322959 := by
    simpa [prefixWord, tailWord_5322959, baseEnd_5322959] using wordTrace_append hprefix tailTrace_5322959
  have hstable : (prefixWord ++ tailWord_5322959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5322959).length < 2 ^ (prefixWord ++ tailWord_5322959).sum := by decide
  have hdescent : baseEnd_5322959 < baseStart_5322959 := by decide
  rcases family_descends (prefixWord ++ tailWord_5322959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5322966 : List Nat := [5, 2, 1, 2, 1, 1, 1, 1, 1, 1, 7]
def baseStart_5322966 : Nat := 118140960795 + 5322966 * 2 ^ 59
def prefixEnd_5322966 : Nat := 4983230072969 + 3 ^ 40 * 5322966 * 2
def baseEnd_5322966 : Nat := 2733240065540526104745131

theorem tailTrace_5322966 : CollatzResearch.WordTrace tailWord_5322966 prefixEnd_5322966 2733240065540526104745131 := by
  unfold tailWord_5322966
  simp only [CollatzResearch.WordTrace]
  refine ⟨12134032477113171691346297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 129429679755873831374360501 12134032477113171691346297)
  ·
    refine ⟨9100524357834878768509723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12134032477113171691346297 9100524357834878768509723)
    ·
      refine ⟨13650786536752318152764585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9100524357834878768509723 13650786536752318152764585)
      ·
        refine ⟨10238089902564238614573439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13650786536752318152764585 10238089902564238614573439)
        ·
          refine ⟨15357134853846357921860159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10238089902564238614573439 15357134853846357921860159)
          ·
            refine ⟨23035702280769536882790239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15357134853846357921860159 23035702280769536882790239)
            ·
              refine ⟨34553553421154305324185359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23035702280769536882790239 34553553421154305324185359)
              ·
                refine ⟨51830330131731457986278039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34553553421154305324185359 51830330131731457986278039)
                ·
                  refine ⟨77745495197597186979417059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51830330131731457986278039 77745495197597186979417059)
                  ·
                    refine ⟨116618242796395780469125589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 77745495197597186979417059 116618242796395780469125589)
                    ·
                      refine ⟨2733240065540526104745131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 116618242796395780469125589 2733240065540526104745131)
                      ·
                        rfl

theorem cell23_5322966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_5322966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5322966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5322966 prefixEnd_5322966 := by exact prefixLift 5322966
  have htrace : WordTrace (prefixWord ++ tailWord_5322966) baseStart_5322966 baseEnd_5322966 := by
    simpa [prefixWord, tailWord_5322966, baseEnd_5322966] using wordTrace_append hprefix tailTrace_5322966
  have hstable : (prefixWord ++ tailWord_5322966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5322966).length < 2 ^ (prefixWord ++ tailWord_5322966).sum := by decide
  have hdescent : baseEnd_5322966 < baseStart_5322966 := by decide
  rcases family_descends (prefixWord ++ tailWord_5322966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5323016 : List Nat := [2, 1, 3, 2, 3, 2, 2, 2, 6]
def baseStart_5323016 : Nat := 118140960795 + 5323016 * 2 ^ 59
def prefixEnd_5323016 : Nat := 4983230072969 + 3 ^ 40 * 5323016 * 2
def baseEnd_5323016 : Nat := 303696193285916767679989

theorem tailTrace_5323016 : CollatzResearch.WordTrace tailWord_5323016 prefixEnd_5323016 303696193285916767679989 := by
  unfold tailWord_5323016
  simp only [CollatzResearch.WordTrace]
  refine ⟨97073171641814802800430451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129430895522419737067240601 97073171641814802800430451)
  ·
    refine ⟨145609757462722204200645677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97073171641814802800430451 145609757462722204200645677)
    ·
      refine ⟨54603659048520826575242129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145609757462722204200645677 54603659048520826575242129)
      ·
        refine ⟨40952744286390619931431597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54603659048520826575242129 40952744286390619931431597)
        ·
          refine ⟨15357279107396482474286849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40952744286390619931431597 15357279107396482474286849)
          ·
            refine ⟨11517959330547361855715137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15357279107396482474286849 11517959330547361855715137)
            ·
              refine ⟨8638469497910521391786353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11517959330547361855715137 8638469497910521391786353)
              ·
                refine ⟨6478852123432891043839765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8638469497910521391786353 6478852123432891043839765)
                ·
                  refine ⟨303696193285916767679989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6478852123432891043839765 303696193285916767679989)
                  ·
                    rfl

theorem cell23_5323016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 2, 6].length) (baseStart_5323016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5323016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5323016 prefixEnd_5323016 := by exact prefixLift 5323016
  have htrace : WordTrace (prefixWord ++ tailWord_5323016) baseStart_5323016 baseEnd_5323016 := by
    simpa [prefixWord, tailWord_5323016, baseEnd_5323016] using wordTrace_append hprefix tailTrace_5323016
  have hstable : (prefixWord ++ tailWord_5323016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5323016).length < 2 ^ (prefixWord ++ tailWord_5323016).sum := by decide
  have hdescent : baseEnd_5323016 < baseStart_5323016 := by decide
  rcases family_descends (prefixWord ++ tailWord_5323016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5323029 : List Nat := [1, 3, 2, 1, 2, 1, 3, 2, 3, 5]
def baseStart_5323029 : Nat := 118140960795 + 5323029 * 2 ^ 59
def prefixEnd_5323029 : Nat := 4983230072969 + 3 ^ 40 * 5323029 * 2
def baseEnd_5323029 : Nat := 911090804940586452752447

theorem tailTrace_5323029 : CollatzResearch.WordTrace tailWord_5323029 prefixEnd_5323029 911090804940586452752447 := by
  unfold tailWord_5323029
  simp only [CollatzResearch.WordTrace]
  refine ⟨194146817432582508821084141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129431211621721672547389427 194146817432582508821084141)
  ·
    refine ⟨72805056537218440807906553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 194146817432582508821084141 72805056537218440807906553)
    ·
      refine ⟨54603792402913830605929915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72805056537218440807906553 54603792402913830605929915)
      ·
        refine ⟨81905688604370745908894873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54603792402913830605929915 81905688604370745908894873)
        ·
          refine ⟨61429266453278059431671155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81905688604370745908894873 61429266453278059431671155)
          ·
            refine ⟨92143899679917089147506733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61429266453278059431671155 92143899679917089147506733)
            ·
              refine ⟨34553962379968908430315025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92143899679917089147506733 34553962379968908430315025)
              ·
                refine ⟨25915471784976681322736269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34553962379968908430315025 25915471784976681322736269)
                ·
                  refine ⟨9718301919366255496026101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25915471784976681322736269 9718301919366255496026101)
                  ·
                    refine ⟨911090804940586452752447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9718301919366255496026101 911090804940586452752447)
                    ·
                      rfl

theorem cell23_5323029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 2, 3, 5].length) (baseStart_5323029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5323029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5323029 prefixEnd_5323029 := by exact prefixLift 5323029
  have htrace : WordTrace (prefixWord ++ tailWord_5323029) baseStart_5323029 baseEnd_5323029 := by
    simpa [prefixWord, tailWord_5323029, baseEnd_5323029] using wordTrace_append hprefix tailTrace_5323029
  have hstable : (prefixWord ++ tailWord_5323029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5323029).length < 2 ^ (prefixWord ++ tailWord_5323029).sum := by decide
  have hdescent : baseEnd_5323029 < baseStart_5323029 := by decide
  rcases family_descends (prefixWord ++ tailWord_5323029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5323036 : List Nat := [2, 2, 3, 1, 1, 1, 1, 4, 1, 5, 2]
def baseStart_5323036 : Nat := 118140960795 + 5323036 * 2 ^ 59
def prefixEnd_5323036 : Nat := 4983230072969 + 3 ^ 40 * 5323036 * 2
def baseEnd_5323036 : Nat := 2733276009186340830869809

theorem tailTrace_5323036 : CollatzResearch.WordTrace tailWord_5323036 prefixEnd_5323036 2733276009186340830869809 := by
  unfold tailWord_5323036
  simp only [CollatzResearch.WordTrace]
  refine ⟨97073536371778574508294481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129431381829038099344392641 97073536371778574508294481)
  ·
    refine ⟨72805152278833930881220861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97073536371778574508294481 72805152278833930881220861)
    ·
      refine ⟨27301932104562724080457823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72805152278833930881220861 27301932104562724080457823)
      ·
        refine ⟨40952898156844086120686735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27301932104562724080457823 40952898156844086120686735)
        ·
          refine ⟨61429347235266129181030103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40952898156844086120686735 61429347235266129181030103)
          ·
            refine ⟨92144020852899193771545155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61429347235266129181030103 92144020852899193771545155)
            ·
              refine ⟨138216031279348790657317733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92144020852899193771545155 138216031279348790657317733)
              ·
                refine ⟨25915505864877898248247075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 138216031279348790657317733 25915505864877898248247075)
                ·
                  refine ⟨38873258797316847372370613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25915505864877898248247075 38873258797316847372370613)
                  ·
                    refine ⟨3644368012248454441159745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38873258797316847372370613 3644368012248454441159745)
                    ·
                      refine ⟨2733276009186340830869809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3644368012248454441159745 2733276009186340830869809)
                      ·
                        rfl

theorem cell23_5323036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 4, 1, 5, 2].length) (baseStart_5323036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5323036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5323036 prefixEnd_5323036 := by exact prefixLift 5323036
  have htrace : WordTrace (prefixWord ++ tailWord_5323036) baseStart_5323036 baseEnd_5323036 := by
    simpa [prefixWord, tailWord_5323036, baseEnd_5323036] using wordTrace_append hprefix tailTrace_5323036
  have hstable : (prefixWord ++ tailWord_5323036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5323036).length < 2 ^ (prefixWord ++ tailWord_5323036).sum := by decide
  have hdescent : baseEnd_5323036 < baseStart_5323036 := by decide
  rcases family_descends (prefixWord ++ tailWord_5323036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5323059 : List Nat := [1, 1, 1, 2, 5, 1, 1, 4, 1, 6]
def baseStart_5323059 : Nat := 118140960795 + 5323059 * 2 ^ 59
def prefixEnd_5323059 : Nat := 4983230072969 + 3 ^ 40 * 5323059 * 2
def baseEnd_5323059 : Nat := 911095939747131413627401

theorem tailTrace_5323059 : CollatzResearch.WordTrace tailWord_5323059 prefixEnd_5323059 911095939747131413627401 := by
  unfold tailWord_5323059
  simp only [CollatzResearch.WordTrace]
  refine ⟨194147911622473823944676231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129431941081649215963117487 194147911622473823944676231)
  ·
    refine ⟨291221867433710735917014347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194147911622473823944676231 291221867433710735917014347)
    ·
      refine ⟨436832801150566103875521521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 291221867433710735917014347 436832801150566103875521521)
      ·
        refine ⟨327624600862924577906641141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 436832801150566103875521521 327624600862924577906641141)
        ·
          refine ⟨30714806330899179178747607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 327624600862924577906641141 30714806330899179178747607)
          ·
            refine ⟨46072209496348768768121411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30714806330899179178747607 46072209496348768768121411)
            ·
              refine ⟨69108314244523153152182117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46072209496348768768121411 69108314244523153152182117)
              ·
                refine ⟨12957808920848091216034147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69108314244523153152182117 12957808920848091216034147)
                ·
                  refine ⟨19436713381272136824051221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12957808920848091216034147 19436713381272136824051221)
                  ·
                    refine ⟨911095939747131413627401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19436713381272136824051221 911095939747131413627401)
                    ·
                      rfl

theorem cell23_5323059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 4, 1, 6].length) (baseStart_5323059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5323059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5323059 prefixEnd_5323059 := by exact prefixLift 5323059
  have htrace : WordTrace (prefixWord ++ tailWord_5323059) baseStart_5323059 baseEnd_5323059 := by
    simpa [prefixWord, tailWord_5323059, baseEnd_5323059] using wordTrace_append hprefix tailTrace_5323059
  have hstable : (prefixWord ++ tailWord_5323059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5323059).length < 2 ^ (prefixWord ++ tailWord_5323059).sum := by decide
  have hdescent : baseEnd_5323059 < baseStart_5323059 := by decide
  rcases family_descends (prefixWord ++ tailWord_5323059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5323079 : List Nat := [1, 1, 4, 1, 2, 2, 2, 2, 1, 1, 6]
def baseStart_5323079 : Nat := 118140960795 + 5323079 * 2 ^ 59
def prefixEnd_5323079 : Nat := 4983230072969 + 3 ^ 40 * 5323079 * 2
def baseEnd_5323079 : Nat := 2733298088854484162632111

theorem tailTrace_5323079 : CollatzResearch.WordTrace tailWord_5323079 prefixEnd_5323079 2733298088854484162632111 := by
  unfold tailWord_5323079
  simp only [CollatzResearch.WordTrace]
  refine ⟨194148641082401367360404291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129432427388267578240269527 194148641082401367360404291)
  ·
    refine ⟨291222961623602051040606437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194148641082401367360404291 291222961623602051040606437)
    ·
      refine ⟨54604305304425384570113707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 291222961623602051040606437 54604305304425384570113707)
      ·
        refine ⟨81906457956638076855170561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54604305304425384570113707 81906457956638076855170561)
        ·
          refine ⟨61429843467478557641377921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81906457956638076855170561 61429843467478557641377921)
          ·
            refine ⟨46072382600608918231033441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61429843467478557641377921 46072382600608918231033441)
            ·
              refine ⟨34554286950456688673275081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46072382600608918231033441 34554286950456688673275081)
              ·
                refine ⟨25915715212842516504956311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34554286950456688673275081 25915715212842516504956311)
                ·
                  refine ⟨38873572819263774757434467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25915715212842516504956311 38873572819263774757434467)
                  ·
                    refine ⟨58310359228895662136151701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38873572819263774757434467 58310359228895662136151701)
                    ·
                      refine ⟨2733298088854484162632111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58310359228895662136151701 2733298088854484162632111)
                      ·
                        rfl

theorem cell23_5323079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 2, 1, 1, 6].length) (baseStart_5323079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5323079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5323079 prefixEnd_5323079 := by exact prefixLift 5323079
  have htrace : WordTrace (prefixWord ++ tailWord_5323079) baseStart_5323079 baseEnd_5323079 := by
    simpa [prefixWord, tailWord_5323079, baseEnd_5323079] using wordTrace_append hprefix tailTrace_5323079
  have hstable : (prefixWord ++ tailWord_5323079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5323079).length < 2 ^ (prefixWord ++ tailWord_5323079).sum := by decide
  have hdescent : baseEnd_5323079 < baseStart_5323079 := by decide
  rcases family_descends (prefixWord ++ tailWord_5323079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5323086 : List Nat := [4, 1, 1, 1, 1, 1, 2, 4, 3, 2, 3]
def baseStart_5323086 : Nat := 118140960795 + 5323086 * 2 ^ 59
def prefixEnd_5323086 : Nat := 4983230072969 + 3 ^ 40 * 5323086 * 2
def baseEnd_5323086 : Nat := 2733301683219065635244579

theorem tailTrace_5323086 : CollatzResearch.WordTrace tailWord_5323086 prefixEnd_5323086 2733301683219065635244579 := by
  unfold tailWord_5323086
  simp only [CollatzResearch.WordTrace]
  refine ⟨24268612049172000944488639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129432597595584005037272741 24268612049172000944488639)
  ·
    refine ⟨36402918073758001416732959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24268612049172000944488639 36402918073758001416732959)
    ·
      refine ⟨54604377110637002125099439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36402918073758001416732959 54604377110637002125099439)
      ·
        refine ⟨81906565665955503187649159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54604377110637002125099439 81906565665955503187649159)
        ·
          refine ⟨122859848498933254781473739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81906565665955503187649159 122859848498933254781473739)
          ·
            refine ⟨184289772748399882172210609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122859848498933254781473739 184289772748399882172210609)
            ·
              refine ⟨138217329561299911629157957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 184289772748399882172210609 138217329561299911629157957)
              ·
                refine ⟨25915749292743733430467117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 138217329561299911629157957 25915749292743733430467117)
                ·
                  refine ⟨9718405984778900036425169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25915749292743733430467117 9718405984778900036425169)
                  ·
                    refine ⟨7288804488584175027318877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9718405984778900036425169 7288804488584175027318877)
                    ·
                      refine ⟨2733301683219065635244579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7288804488584175027318877 2733301683219065635244579)
                      ·
                        rfl

theorem cell23_5323086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 4, 3, 2, 3].length) (baseStart_5323086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5323086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5323086 prefixEnd_5323086 := by exact prefixLift 5323086
  have htrace : WordTrace (prefixWord ++ tailWord_5323086) baseStart_5323086 baseEnd_5323086 := by
    simpa [prefixWord, tailWord_5323086, baseEnd_5323086] using wordTrace_append hprefix tailTrace_5323086
  have hstable : (prefixWord ++ tailWord_5323086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5323086).length < 2 ^ (prefixWord ++ tailWord_5323086).sum := by decide
  have hdescent : baseEnd_5323086 < baseStart_5323086 := by decide
  rcases family_descends (prefixWord ++ tailWord_5323086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5323093 : List Nat := [1, 3, 2, 2, 4, 2, 1, 1, 1, 6]
def baseStart_5323093 : Nat := 118140960795 + 5323093 * 2 ^ 59
def prefixEnd_5323093 : Nat := 4983230072969 + 3 ^ 40 * 5323093 * 2
def baseEnd_5323093 : Nat := 911101759194549035952349

theorem tailTrace_5323093 : CollatzResearch.WordTrace tailWord_5323093 prefixEnd_5323093 911101759194549035952349 := by
  unfold tailWord_5323093
  simp only [CollatzResearch.WordTrace]
  refine ⟨194149151704350647751413933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129432767802900431834275955 194149151704350647751413933)
  ·
    refine ⟨72805931889131492906780225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 194149151704350647751413933 72805931889131492906780225)
    ·
      refine ⟨54604448916848619680085169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72805931889131492906780225 54604448916848619680085169)
      ·
        refine ⟨40953336687636464760063877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54604448916848619680085169 40953336687636464760063877)
        ·
          refine ⟨7678750628931837142511977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40953336687636464760063877 7678750628931837142511977)
          ·
            refine ⟨5759062971698877856883983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7678750628931837142511977 5759062971698877856883983)
            ·
              refine ⟨8638594457548316785325975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5759062971698877856883983 8638594457548316785325975)
              ·
                refine ⟨12957891686322475177988963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8638594457548316785325975 12957891686322475177988963)
                ·
                  refine ⟨19436837529483712766983445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12957891686322475177988963 19436837529483712766983445)
                  ·
                    refine ⟨911101759194549035952349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19436837529483712766983445 911101759194549035952349)
                    ·
                      rfl

theorem cell23_5323093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 1, 1, 6].length) (baseStart_5323093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5323093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5323093 prefixEnd_5323093 := by exact prefixLift 5323093
  have htrace : WordTrace (prefixWord ++ tailWord_5323093) baseStart_5323093 baseEnd_5323093 := by
    simpa [prefixWord, tailWord_5323093, baseEnd_5323093] using wordTrace_append hprefix tailTrace_5323093
  have hstable : (prefixWord ++ tailWord_5323093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5323093).length < 2 ^ (prefixWord ++ tailWord_5323093).sum := by decide
  have hdescent : baseEnd_5323093 < baseStart_5323093 := by decide
  rcases family_descends (prefixWord ++ tailWord_5323093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5323106 : List Nat := [3, 3, 2, 1, 1, 3, 1, 9]
def baseStart_5323106 : Nat := 118140960795 + 5323106 * 2 ^ 59
def prefixEnd_5323106 : Nat := 4983230072969 + 3 ^ 40 * 5323106 * 2
def baseEnd_5323106 : Nat := 101233776030820576184981

theorem tailTrace_5323106 : CollatzResearch.WordTrace tailWord_5323106 prefixEnd_5323106 101233776030820576184981 := by
  unfold tailWord_5323106
  simp only [CollatzResearch.WordTrace]
  refine ⟨48537406463325887742909293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129433083902202367314424781 48537406463325887742909293)
  ·
    refine ⟨18201527423747207903590985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48537406463325887742909293 18201527423747207903590985)
    ·
      refine ⟨13651145567810405927693239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18201527423747207903590985 13651145567810405927693239)
      ·
        refine ⟨20476718351715608891539859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13651145567810405927693239 20476718351715608891539859)
        ·
          refine ⟨30715077527573413337309789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20476718351715608891539859 30715077527573413337309789)
          ·
            refine ⟨11518154072840030001491171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30715077527573413337309789 11518154072840030001491171)
            ·
              refine ⟨17277231109260045002236757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11518154072840030001491171 17277231109260045002236757)
              ·
                refine ⟨101233776030820576184981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17277231109260045002236757 101233776030820576184981)
                ·
                  rfl

theorem cell23_5323106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 9].length) (baseStart_5323106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5323106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5323106 prefixEnd_5323106 := by exact prefixLift 5323106
  have htrace : WordTrace (prefixWord ++ tailWord_5323106) baseStart_5323106 baseEnd_5323106 := by
    simpa [prefixWord, tailWord_5323106, baseEnd_5323106] using wordTrace_append hprefix tailTrace_5323106
  have hstable : (prefixWord ++ tailWord_5323106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5323106).length < 2 ^ (prefixWord ++ tailWord_5323106).sum := by decide
  have hdescent : baseEnd_5323106 < baseStart_5323106 := by decide
  rcases family_descends (prefixWord ++ tailWord_5323106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5323129 : List Nat := [1, 2, 1, 3, 2, 1, 1, 1, 4, 2, 5]
def baseStart_5323129 : Nat := 118140960795 + 5323129 * 2 ^ 59
def prefixEnd_5323129 : Nat := 4983230072969 + 3 ^ 40 * 5323129 * 2
def baseEnd_5323129 : Nat := 2733323762887208967006881

theorem tailTrace_5323129 : CollatzResearch.WordTrace tailWord_5323129 prefixEnd_5323129 2733323762887208967006881 := by
  unfold tailWord_5323129
  simp only [CollatzResearch.WordTrace]
  refine ⟨194150464732220225899724441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129433643154813483933149627 194150464732220225899724441)
  ·
    refine ⟨145612848549165169424793331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194150464732220225899724441 145612848549165169424793331)
    ·
      refine ⟨218419272823747754137189997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145612848549165169424793331 218419272823747754137189997)
      ·
        refine ⟨81907227308905407801446249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 218419272823747754137189997 81907227308905407801446249)
        ·
          refine ⟨61430420481679055851084687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81907227308905407801446249 61430420481679055851084687)
          ·
            refine ⟨92145630722518583776627031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61430420481679055851084687 92145630722518583776627031)
            ·
              refine ⟨138218446083777875664940547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92145630722518583776627031 138218446083777875664940547)
              ·
                refine ⟨207327669125666813497410821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 138218446083777875664940547 207327669125666813497410821)
                ·
                  refine ⟨38873937961062527530764529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 207327669125666813497410821 38873937961062527530764529)
                  ·
                    refine ⟨29155453470796895648073397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38873937961062527530764529 29155453470796895648073397)
                    ·
                      refine ⟨2733323762887208967006881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29155453470796895648073397 2733323762887208967006881)
                      ·
                        rfl

theorem cell23_5323129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 4, 2, 5].length) (baseStart_5323129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5323129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5323129 prefixEnd_5323129 := by exact prefixLift 5323129
  have htrace : WordTrace (prefixWord ++ tailWord_5323129) baseStart_5323129 baseEnd_5323129 := by
    simpa [prefixWord, tailWord_5323129, baseEnd_5323129] using wordTrace_append hprefix tailTrace_5323129
  have hstable : (prefixWord ++ tailWord_5323129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5323129).length < 2 ^ (prefixWord ++ tailWord_5323129).sum := by decide
  have hdescent : baseEnd_5323129 < baseStart_5323129 := by decide
  rcases family_descends (prefixWord ++ tailWord_5323129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5323133 : List Nat := [1, 4, 1, 1, 2, 3, 2, 1, 4, 1, 3]
def baseStart_5323133 : Nat := 118140960795 + 5323133 * 2 ^ 59
def prefixEnd_5323133 : Nat := 4983230072969 + 3 ^ 40 * 5323133 * 2
def baseEnd_5323133 : Nat := 2733325816809826951356863

theorem tailTrace_5323133 : CollatzResearch.WordTrace tailWord_5323133 prefixEnd_5323133 2733325816809826951356863 := by
  unfold tailWord_5323133
  simp only [CollatzResearch.WordTrace]
  refine ⟨194150610624205734582870053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129433740416137156388580035 194150610624205734582870053)
  ·
    refine ⟨36403239492038575234288135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 194150610624205734582870053 36403239492038575234288135)
    ·
      refine ⟨54604859238057862851432203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36403239492038575234288135 54604859238057862851432203)
      ·
        refine ⟨81907288857086794277148305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54604859238057862851432203 81907288857086794277148305)
        ·
          refine ⟨61430466642815095707861229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81907288857086794277148305 61430466642815095707861229)
          ·
            refine ⟨23036424991055660890447961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61430466642815095707861229 23036424991055660890447961)
            ·
              refine ⟨17277318743291745667835971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23036424991055660890447961 17277318743291745667835971)
              ·
                refine ⟨25915978114937618501753957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17277318743291745667835971 25915978114937618501753957)
                ·
                  refine ⟨4859245896550803469078867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25915978114937618501753957 4859245896550803469078867)
                  ·
                    refine ⟨7288868844826205203618301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4859245896550803469078867 7288868844826205203618301)
                    ·
                      refine ⟨2733325816809826951356863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7288868844826205203618301 2733325816809826951356863)
                      ·
                        rfl

theorem cell23_5323133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 1, 4, 1, 3].length) (baseStart_5323133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5323133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5323133 prefixEnd_5323133 := by exact prefixLift 5323133
  have htrace : WordTrace (prefixWord ++ tailWord_5323133) baseStart_5323133 baseEnd_5323133 := by
    simpa [prefixWord, tailWord_5323133, baseEnd_5323133] using wordTrace_append hprefix tailTrace_5323133
  have hstable : (prefixWord ++ tailWord_5323133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5323133).length < 2 ^ (prefixWord ++ tailWord_5323133).sum := by decide
  have hdescent : baseEnd_5323133 < baseStart_5323133 := by decide
  rcases family_descends (prefixWord ++ tailWord_5323133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5323143 : List Nat := [1, 1, 4, 2, 2, 1, 2, 2, 3, 3, 2]
def baseStart_5323143 : Nat := 118140960795 + 5323143 * 2 ^ 59
def prefixEnd_5323143 : Nat := 4983230072969 + 3 ^ 40 * 5323143 * 2
def baseEnd_5323143 : Nat := 2733330951616371912231817

theorem tailTrace_5323143 : CollatzResearch.WordTrace tailWord_5323143 prefixEnd_5323143 2733330951616371912231817 := by
  unfold tailWord_5323143
  simp only [CollatzResearch.WordTrace]
  refine ⟨194150975354169506290734083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129433983569446337527156055 194150975354169506290734083)
  ·
    refine ⟨291226463031254259436101125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194150975354169506290734083 291226463031254259436101125)
    ·
      refine ⟨54604961818360173644268961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 291226463031254259436101125 54604961818360173644268961)
      ·
        refine ⟨40953721363770130233201721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54604961818360173644268961 40953721363770130233201721)
        ·
          refine ⟨30715291022827597674901291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40953721363770130233201721 30715291022827597674901291)
          ·
            refine ⟨46072936534241396512351937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30715291022827597674901291 46072936534241396512351937)
            ·
              refine ⟨34554702400681047384263953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46072936534241396512351937 34554702400681047384263953)
              ·
                refine ⟨25916026800510785538197965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34554702400681047384263953 25916026800510785538197965)
                ·
                  refine ⟨9718510050191544576824237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25916026800510785538197965 9718510050191544576824237)
                  ·
                    refine ⟨3644441268821829216309089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9718510050191544576824237 3644441268821829216309089)
                    ·
                      refine ⟨2733330951616371912231817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3644441268821829216309089 2733330951616371912231817)
                      ·
                        rfl

theorem cell23_5323143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 2, 3, 3, 2].length) (baseStart_5323143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5323143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5323143 prefixEnd_5323143 := by exact prefixLift 5323143
  have htrace : WordTrace (prefixWord ++ tailWord_5323143) baseStart_5323143 baseEnd_5323143 := by
    simpa [prefixWord, tailWord_5323143, baseEnd_5323143] using wordTrace_append hprefix tailTrace_5323143
  have hstable : (prefixWord ++ tailWord_5323143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5323143).length < 2 ^ (prefixWord ++ tailWord_5323143).sum := by decide
  have hdescent : baseEnd_5323143 < baseStart_5323143 := by decide
  rcases family_descends (prefixWord ++ tailWord_5323143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5323160 : List Nat := [2, 1, 2, 5, 1, 2, 1, 1, 3, 3, 2]
def baseStart_5323160 : Nat := 118140960795 + 5323160 * 2 ^ 59
def prefixEnd_5323160 : Nat := 4983230072969 + 3 ^ 40 * 5323160 * 2
def baseEnd_5323160 : Nat := 2733339680787498345719239

theorem tailTrace_5323160 : CollatzResearch.WordTrace tailWord_5323160 prefixEnd_5323160 2733339680787498345719239 := by
  unfold tailWord_5323160
  simp only [CollatzResearch.WordTrace]
  refine ⟨97075797697553959097051467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129434396930071945462735289 97075797697553959097051467)
  ·
    refine ⟨145613696546330938645577201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97075797697553959097051467 145613696546330938645577201)
    ·
      refine ⟨109210272409748203984182901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145613696546330938645577201 109210272409748203984182901)
      ·
        refine ⟨10238463038413894123517147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 109210272409748203984182901 10238463038413894123517147)
        ·
          refine ⟨15357694557620841185275721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10238463038413894123517147 15357694557620841185275721)
          ·
            refine ⟨11518270918215630888956791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15357694557620841185275721 11518270918215630888956791)
            ·
              refine ⟨17277406377323446333435187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11518270918215630888956791 17277406377323446333435187)
              ·
                refine ⟨25916109565985169500152781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17277406377323446333435187 25916109565985169500152781)
                ·
                  refine ⟨9718541087244438562557293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25916109565985169500152781 9718541087244438562557293)
                  ·
                    refine ⟨3644452907716664460958985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9718541087244438562557293 3644452907716664460958985)
                    ·
                      refine ⟨2733339680787498345719239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3644452907716664460958985 2733339680787498345719239)
                      ·
                        rfl

theorem cell23_5323160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 1, 3, 3, 2].length) (baseStart_5323160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5323160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5323160 prefixEnd_5323160 := by exact prefixLift 5323160
  have htrace : WordTrace (prefixWord ++ tailWord_5323160) baseStart_5323160 baseEnd_5323160 := by
    simpa [prefixWord, tailWord_5323160, baseEnd_5323160] using wordTrace_append hprefix tailTrace_5323160
  have hstable : (prefixWord ++ tailWord_5323160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5323160).length < 2 ^ (prefixWord ++ tailWord_5323160).sum := by decide
  have hdescent : baseEnd_5323160 < baseStart_5323160 := by decide
  rcases family_descends (prefixWord ++ tailWord_5323160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5323173 : List Nat := [1, 3, 1, 2, 1, 1, 5, 2, 1, 4, 2]
def baseStart_5323173 : Nat := 118140960795 + 5323173 * 2 ^ 59
def prefixEnd_5323173 : Nat := 4983230072969 + 3 ^ 40 * 5323173 * 2
def baseEnd_5323173 : Nat := 2733346356036006794856679

theorem tailTrace_5323173 : CollatzResearch.WordTrace tailWord_5323173 prefixEnd_5323173 2733346356036006794856679 := by
  unfold tailWord_5323173
  simp only [CollatzResearch.WordTrace]
  refine ⟨194152069544060821414326173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129434713029373880942884115 194152069544060821414326173)
  ·
    refine ⟨72807026079022808030372315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 194152069544060821414326173 72807026079022808030372315)
    ·
      refine ⟨109210539118534212045558473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72807026079022808030372315 109210539118534212045558473)
      ·
        refine ⟨81907904338900659034168855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109210539118534212045558473 81907904338900659034168855)
        ·
          refine ⟨122861856508350988551253283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81907904338900659034168855 122861856508350988551253283)
          ·
            refine ⟨184292784762526482826879925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122861856508350988551253283 184292784762526482826879925)
            ·
              refine ⟨17277448571486857765019993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 184292784762526482826879925 17277448571486857765019993)
              ·
                refine ⟨12958086428615143323764995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17277448571486857765019993 12958086428615143323764995)
                ·
                  refine ⟨19437129642922714985647493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12958086428615143323764995 19437129642922714985647493)
                  ·
                    refine ⟨3644461808048009059808905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19437129642922714985647493 3644461808048009059808905)
                    ·
                      refine ⟨2733346356036006794856679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3644461808048009059808905 2733346356036006794856679)
                      ·
                        rfl

theorem cell23_5323173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 2, 1, 4, 2].length) (baseStart_5323173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5323173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5323173 prefixEnd_5323173 := by exact prefixLift 5323173
  have htrace : WordTrace (prefixWord ++ tailWord_5323173) baseStart_5323173 baseEnd_5323173 := by
    simpa [prefixWord, tailWord_5323173, baseEnd_5323173] using wordTrace_append hprefix tailTrace_5323173
  have hstable : (prefixWord ++ tailWord_5323173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5323173).length < 2 ^ (prefixWord ++ tailWord_5323173).sum := by decide
  have hdescent : baseEnd_5323173 < baseStart_5323173 := by decide
  rcases family_descends (prefixWord ++ tailWord_5323173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5323186 : List Nat := [3, 2, 1, 1, 1, 1, 4, 2, 2, 2, 4]
def baseStart_5323186 : Nat := 118140960795 + 5323186 * 2 ^ 59
def prefixEnd_5323186 : Nat := 4983230072969 + 3 ^ 40 * 5323186 * 2
def baseEnd_5323186 : Nat := 2733353031284515243994119

theorem tailTrace_5323186 : CollatzResearch.WordTrace tailWord_5323186 prefixEnd_5323186 2733353031284515243994119 := by
  unfold tailWord_5323186
  simp only [CollatzResearch.WordTrace]
  refine ⟨48538135923253431158637353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129435029128675816423032941 48538135923253431158637353)
  ·
    refine ⟨36403601942440073368978015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48538135923253431158637353 36403601942440073368978015)
    ·
      refine ⟨54605402913660110053467023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36403601942440073368978015 54605402913660110053467023)
      ·
        refine ⟨81908104370490165080200535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54605402913660110053467023 81908104370490165080200535)
        ·
          refine ⟨122862156555735247620300803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81908104370490165080200535 122862156555735247620300803)
          ·
            refine ⟨184293234833602871430451205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122862156555735247620300803 184293234833602871430451205)
            ·
              refine ⟨34554981531300538393209601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 184293234833602871430451205 34554981531300538393209601)
              ·
                refine ⟨25916236148475403794907201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34554981531300538393209601 25916236148475403794907201)
                ·
                  refine ⟨19437177111356552846180401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25916236148475403794907201 19437177111356552846180401)
                  ·
                    refine ⟨14577882833517414634635301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19437177111356552846180401 14577882833517414634635301)
                    ·
                      refine ⟨2733353031284515243994119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14577882833517414634635301 2733353031284515243994119)
                      ·
                        rfl

theorem cell23_5323186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 2, 2, 2, 4].length) (baseStart_5323186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5323186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5323186 prefixEnd_5323186 := by exact prefixLift 5323186
  have htrace : WordTrace (prefixWord ++ tailWord_5323186) baseStart_5323186 baseEnd_5323186 := by
    simpa [prefixWord, tailWord_5323186, baseEnd_5323186] using wordTrace_append hprefix tailTrace_5323186
  have hstable : (prefixWord ++ tailWord_5323186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5323186).length < 2 ^ (prefixWord ++ tailWord_5323186).sum := by decide
  have hdescent : baseEnd_5323186 < baseStart_5323186 := by decide
  rcases family_descends (prefixWord ++ tailWord_5323186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5323199 : List Nat := [1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 8]
def baseStart_5323199 : Nat := 118140960795 + 5323199 * 2 ^ 59
def prefixEnd_5323199 : Nat := 4983230072969 + 3 ^ 40 * 5323199 * 2
def baseEnd_5323199 : Nat := 2733359706533023693131559

theorem tailTrace_5323199 : CollatzResearch.WordTrace tailWord_5323199 prefixEnd_5323199 2733359706533023693131559 := by
  unfold tailWord_5323199
  simp only [CollatzResearch.WordTrace]
  refine ⟨194153017841966627854772651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129435345227977751903181767 194153017841966627854772651)
  ·
    refine ⟨291229526762949941782158977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194153017841966627854772651 291229526762949941782158977)
    ·
      refine ⟨218422145072212456336619233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 291229526762949941782158977 218422145072212456336619233)
      ·
        refine ⟨163816608804159342252464425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 218422145072212456336619233 163816608804159342252464425)
        ·
          refine ⟨122862456603119506689348319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163816608804159342252464425 122862456603119506689348319)
          ·
            refine ⟨184293684904679260034022479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122862456603119506689348319 184293684904679260034022479)
            ·
              refine ⟨276440527357018890051033719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 184293684904679260034022479 276440527357018890051033719)
              ·
                refine ⟨414660791035528335076550579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 276440527357018890051033719 414660791035528335076550579)
                ·
                  refine ⟨621991186553292502614825869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 414660791035528335076550579 621991186553292502614825869)
                  ·
                    refine ⟨233246694957484688480559701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 621991186553292502614825869 233246694957484688480559701)
                    ·
                      refine ⟨2733359706533023693131559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 233246694957484688480559701 2733359706533023693131559)
                      ·
                        rfl

theorem cell23_5323199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 8].length) (baseStart_5323199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5323199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5323199 prefixEnd_5323199 := by exact prefixLift 5323199
  have htrace : WordTrace (prefixWord ++ tailWord_5323199) baseStart_5323199 baseEnd_5323199 := by
    simpa [prefixWord, tailWord_5323199, baseEnd_5323199] using wordTrace_append hprefix tailTrace_5323199
  have hstable : (prefixWord ++ tailWord_5323199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5323199).length < 2 ^ (prefixWord ++ tailWord_5323199).sum := by decide
  have hdescent : baseEnd_5323199 < baseStart_5323199 := by decide
  rcases family_descends (prefixWord ++ tailWord_5323199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5323226 : List Nat := [3, 1, 1, 2, 3, 1, 3, 1, 1, 7]
def baseStart_5323226 : Nat := 118140960795 + 5323226 * 2 ^ 59
def prefixEnd_5323226 : Nat := 4983230072969 + 3 ^ 40 * 5323226 * 2
def baseEnd_5323226 : Nat := 911124523503565029164645

theorem tailTrace_5323226 : CollatzResearch.WordTrace tailWord_5323226 prefixEnd_5323226 911124523503565029164645 := by
  unfold tailWord_5323226
  simp only [CollatzResearch.WordTrace]
  refine ⟨48538500653217202866501383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129436001741912540977337021 48538500653217202866501383)
  ·
    refine ⟨72807750979825804299752075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48538500653217202866501383 72807750979825804299752075)
    ·
      refine ⟨109211626469738706449628113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72807750979825804299752075 109211626469738706449628113)
      ·
        refine ⟨81908719852304029837221085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109211626469738706449628113 81908719852304029837221085)
        ·
          refine ⟨30715769944614011188957907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81908719852304029837221085 30715769944614011188957907)
          ·
            refine ⟨46073654916921016783436861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30715769944614011188957907 46073654916921016783436861)
            ·
              refine ⟨17277620593845381293788823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46073654916921016783436861 17277620593845381293788823)
              ·
                refine ⟨25916430890768071940683235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17277620593845381293788823 25916430890768071940683235)
                ·
                  refine ⟨38874646336152107911024853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25916430890768071940683235 38874646336152107911024853)
                  ·
                    refine ⟨911124523503565029164645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38874646336152107911024853 911124523503565029164645)
                    ·
                      rfl

theorem cell23_5323226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 1, 1, 7].length) (baseStart_5323226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5323226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5323226 prefixEnd_5323226 := by exact prefixLift 5323226
  have htrace : WordTrace (prefixWord ++ tailWord_5323226) baseStart_5323226 baseEnd_5323226 := by
    simpa [prefixWord, tailWord_5323226, baseEnd_5323226] using wordTrace_append hprefix tailTrace_5323226
  have hstable : (prefixWord ++ tailWord_5323226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5323226).length < 2 ^ (prefixWord ++ tailWord_5323226).sum := by decide
  have hdescent : baseEnd_5323226 < baseStart_5323226 := by decide
  rcases family_descends (prefixWord ++ tailWord_5323226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5323263 : List Nat := [1, 1, 2, 2, 1, 2, 3, 3, 2, 4, 2]
def baseStart_5323263 : Nat := 118140960795 + 5323263 * 2 ^ 59
def prefixEnd_5323263 : Nat := 4983230072969 + 3 ^ 40 * 5323263 * 2
def baseEnd_5323263 : Nat := 2733392569294911442731265

theorem tailTrace_5323263 : CollatzResearch.WordTrace tailWord_5323263 prefixEnd_5323263 2733392569294911442731265 := by
  unfold tailWord_5323263
  simp only [CollatzResearch.WordTrace]
  refine ⟨194155352113734766785102443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129436901409156511190068295 194155352113734766785102443)
  ·
    refine ⟨291233028170602150177653665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194155352113734766785102443 291233028170602150177653665)
    ·
      refine ⟨218424771127951612633240249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 291233028170602150177653665 218424771127951612633240249)
      ·
        refine ⟨163818578345963709474930187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 218424771127951612633240249 163818578345963709474930187)
        ·
          refine ⟨245727867518945564212395281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163818578345963709474930187 245727867518945564212395281)
          ·
            refine ⟨184295900639209173159296461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 245727867518945564212395281 184295900639209173159296461)
            ·
              refine ⟨69110962739703439934736173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 184295900639209173159296461 69110962739703439934736173)
              ·
                refine ⟨25916611027388789975526065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69110962739703439934736173 25916611027388789975526065)
                ·
                  refine ⟨19437458270541592481644549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25916611027388789975526065 19437458270541592481644549)
                  ·
                    refine ⟨3644523425726548590308353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19437458270541592481644549 3644523425726548590308353)
                    ·
                      refine ⟨2733392569294911442731265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3644523425726548590308353 2733392569294911442731265)
                      ·
                        rfl

theorem cell23_5323263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 3, 2, 4, 2].length) (baseStart_5323263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5323263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5323263 prefixEnd_5323263 := by exact prefixLift 5323263
  have htrace : WordTrace (prefixWord ++ tailWord_5323263) baseStart_5323263 baseEnd_5323263 := by
    simpa [prefixWord, tailWord_5323263, baseEnd_5323263] using wordTrace_append hprefix tailTrace_5323263
  have hstable : (prefixWord ++ tailWord_5323263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5323263).length < 2 ^ (prefixWord ++ tailWord_5323263).sum := by decide
  have hdescent : baseEnd_5323263 < baseStart_5323263 := by decide
  rcases family_descends (prefixWord ++ tailWord_5323263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5323283 : List Nat := [1, 1, 1, 2, 1, 5, 2, 3, 2, 2, 3]
def baseStart_5323283 : Nat := 118140960795 + 5323283 * 2 ^ 59
def prefixEnd_5323283 : Nat := 4983230072969 + 3 ^ 40 * 5323283 * 2
def baseEnd_5323283 : Nat := 2733402838908001364481173

theorem tailTrace_5323283 : CollatzResearch.WordTrace tailWord_5323283 prefixEnd_5323283 2733402838908001364481173 := by
  unfold tailWord_5323283
  simp only [CollatzResearch.WordTrace]
  refine ⟨194156081573662310200830503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129437387715774873467220335 194156081573662310200830503)
  ·
    refine ⟨291234122360493465301245755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194156081573662310200830503 291234122360493465301245755)
    ·
      refine ⟨436851183540740197951868633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 291234122360493465301245755 436851183540740197951868633)
      ·
        refine ⟨327638387655555148463901475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 436851183540740197951868633 327638387655555148463901475)
        ·
          refine ⟨491457581483332722695852213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 327638387655555148463901475 491457581483332722695852213)
          ·
            refine ⟨46074148264062442752736145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 491457581483332722695852213 46074148264062442752736145)
            ·
              refine ⟨34555611198046832064552109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46074148264062442752736145 34555611198046832064552109)
              ·
                refine ⟨12958354199267562024207041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34555611198046832064552109 12958354199267562024207041)
                ·
                  refine ⟨9718765649450671518155281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12958354199267562024207041 9718765649450671518155281)
                  ·
                    refine ⟨7289074237088003638616461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9718765649450671518155281 7289074237088003638616461)
                    ·
                      refine ⟨2733402838908001364481173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7289074237088003638616461 2733402838908001364481173)
                      ·
                        rfl

theorem cell23_5323283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 3, 2, 2, 3].length) (baseStart_5323283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5323283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5323283 prefixEnd_5323283 := by exact prefixLift 5323283
  have htrace : WordTrace (prefixWord ++ tailWord_5323283) baseStart_5323283 baseEnd_5323283 := by
    simpa [prefixWord, tailWord_5323283, baseEnd_5323283] using wordTrace_append hprefix tailTrace_5323283
  have hstable : (prefixWord ++ tailWord_5323283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5323283).length < 2 ^ (prefixWord ++ tailWord_5323283).sum := by decide
  have hdescent : baseEnd_5323283 < baseStart_5323283 := by decide
  rcases family_descends (prefixWord ++ tailWord_5323283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5323333 : List Nat := [1, 3, 1, 1, 1, 6, 1, 1, 3, 5]
def baseStart_5323333 : Nat := 118140960795 + 5323333 * 2 ^ 59
def prefixEnd_5323333 : Nat := 4983230072969 + 3 ^ 40 * 5323333 * 2
def baseEnd_5323333 : Nat := 911142837646908722951981

theorem tailTrace_5323333 : CollatzResearch.WordTrace tailWord_5323333 prefixEnd_5323333 911142837646908722951981 := by
  unfold tailWord_5323333
  simp only [CollatzResearch.WordTrace]
  refine ⟨194157905223481168740150653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129438603482320779160100435 194157905223481168740150653)
  ·
    refine ⟨72809214458805438277556495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 194157905223481168740150653 72809214458805438277556495)
    ·
      refine ⟨109213821688208157416334743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72809214458805438277556495 109213821688208157416334743)
      ·
        refine ⟨163820732532312236124502115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109213821688208157416334743 163820732532312236124502115)
        ·
          refine ⟨245731098798468354186753173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163820732532312236124502115 245731098798468354186753173)
          ·
            refine ⟨11518645256178204102504055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 245731098798468354186753173 11518645256178204102504055)
            ·
              refine ⟨17277967884267306153756083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11518645256178204102504055 17277967884267306153756083)
              ·
                refine ⟨25916951826400959230634125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17277967884267306153756083 25916951826400959230634125)
                ·
                  refine ⟨9718856934900359711487797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25916951826400959230634125 9718856934900359711487797)
                  ·
                    refine ⟨911142837646908722951981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9718856934900359711487797 911142837646908722951981)
                    ·
                      rfl

theorem cell23_5323333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 1, 3, 5].length) (baseStart_5323333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5323333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5323333 prefixEnd_5323333 := by exact prefixLift 5323333
  have htrace : WordTrace (prefixWord ++ tailWord_5323333) baseStart_5323333 baseEnd_5323333 := by
    simpa [prefixWord, tailWord_5323333, baseEnd_5323333] using wordTrace_append hprefix tailTrace_5323333
  have hstable : (prefixWord ++ tailWord_5323333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5323333).length < 2 ^ (prefixWord ++ tailWord_5323333).sum := by decide
  have hdescent : baseEnd_5323333 < baseStart_5323333 := by decide
  rcases family_descends (prefixWord ++ tailWord_5323333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5323334 : List Nat := [6, 1, 1, 1, 2, 2, 2, 1, 2, 2, 3]
def baseStart_5323334 : Nat := 118140960795 + 5323334 * 2 ^ 59
def prefixEnd_5323334 : Nat := 4983230072969 + 3 ^ 40 * 5323334 * 2
def baseEnd_5323334 : Nat := 2733429026421380664943439

theorem tailTrace_5323334 : CollatzResearch.WordTrace tailWord_5323334 prefixEnd_5323334 2733429026421380664943439 := by
  unfold tailWord_5323334
  simp only [CollatzResearch.WordTrace]
  refine ⟨6067435678014923309716783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 129438627797651697273958037 6067435678014923309716783)
  ·
    refine ⟨9101153517022384964575175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6067435678014923309716783 9101153517022384964575175)
    ·
      refine ⟨13651730275533577446862763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9101153517022384964575175 13651730275533577446862763)
      ·
        refine ⟨20477595413300366170294145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13651730275533577446862763 20477595413300366170294145)
        ·
          refine ⟨15358196559975274627720609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20477595413300366170294145 15358196559975274627720609)
          ·
            refine ⟨11518647419981455970790457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15358196559975274627720609 11518647419981455970790457)
            ·
              refine ⟨8638985564986091978092843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11518647419981455970790457 8638985564986091978092843)
              ·
                refine ⟨12958478347479137967139265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8638985564986091978092843 12958478347479137967139265)
                ·
                  refine ⟨9718858760609353475354449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12958478347479137967139265 9718858760609353475354449)
                  ·
                    refine ⟨7289144070457015106515837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9718858760609353475354449 7289144070457015106515837)
                    ·
                      refine ⟨2733429026421380664943439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7289144070457015106515837 2733429026421380664943439)
                      ·
                        rfl

theorem cell23_5323334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 1, 2, 2, 3].length) (baseStart_5323334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5323334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5323334 prefixEnd_5323334 := by exact prefixLift 5323334
  have htrace : WordTrace (prefixWord ++ tailWord_5323334) baseStart_5323334 baseEnd_5323334 := by
    simpa [prefixWord, tailWord_5323334, baseEnd_5323334] using wordTrace_append hprefix tailTrace_5323334
  have hstable : (prefixWord ++ tailWord_5323334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5323334).length < 2 ^ (prefixWord ++ tailWord_5323334).sum := by decide
  have hdescent : baseEnd_5323334 < baseStart_5323334 := by decide
  rcases family_descends (prefixWord ++ tailWord_5323334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5323358 : List Nat := [4, 4, 1, 2, 1, 1, 1, 4, 1, 4]
def baseStart_5323358 : Nat := 118140960795 + 5323358 * 2 ^ 59
def prefixEnd_5323358 : Nat := 4983230072969 + 3 ^ 40 * 5323358 * 2
def baseEnd_5323358 : Nat := 911147116652362857014443

theorem tailTrace_5323358 : CollatzResearch.WordTrace tailWord_5323358 prefixEnd_5323358 911147116652362857014443 := by
  unfold tailWord_5323358
  simp only [CollatzResearch.WordTrace]
  refine ⟨24269852131048824751226341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129439211365593732006540485 24269852131048824751226341)
  ·
    refine ⟨4550597274571654640854939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24269852131048824751226341 4550597274571654640854939)
    ·
      refine ⟨6825895911857481961282409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4550597274571654640854939 6825895911857481961282409)
      ·
        refine ⟨5119421933893111470961807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6825895911857481961282409 5119421933893111470961807)
        ·
          refine ⟨7679132900839667206442711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5119421933893111470961807 7679132900839667206442711)
          ·
            refine ⟨11518699351259500809664067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7679132900839667206442711 11518699351259500809664067)
            ·
              refine ⟨17278049026889251214496101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11518699351259500809664067 17278049026889251214496101)
              ·
                refine ⟨3239634192541734602718019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17278049026889251214496101 3239634192541734602718019)
                ·
                  refine ⟨4859451288812601904077029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3239634192541734602718019 4859451288812601904077029)
                  ·
                    refine ⟨911147116652362857014443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4859451288812601904077029 911147116652362857014443)
                    ·
                      rfl

theorem cell23_5323358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_5323358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5323358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5323358 prefixEnd_5323358 := by exact prefixLift 5323358
  have htrace : WordTrace (prefixWord ++ tailWord_5323358) baseStart_5323358 baseEnd_5323358 := by
    simpa [prefixWord, tailWord_5323358, baseEnd_5323358] using wordTrace_append hprefix tailTrace_5323358
  have hstable : (prefixWord ++ tailWord_5323358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5323358).length < 2 ^ (prefixWord ++ tailWord_5323358).sum := by decide
  have hdescent : baseEnd_5323358 < baseStart_5323358 := by decide
  rcases family_descends (prefixWord ++ tailWord_5323358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5323383 : List Nat := [1, 1, 3, 1, 1, 3, 3, 3, 1, 2, 4]
def baseStart_5323383 : Nat := 118140960795 + 5323383 * 2 ^ 59
def prefixEnd_5323383 : Nat := 4983230072969 + 3 ^ 40 * 5323383 * 2
def baseEnd_5323383 : Nat := 2733454186973450973230713

theorem tailTrace_5323383 : CollatzResearch.WordTrace tailWord_5323383 prefixEnd_5323383 2733454186973450973230713 := by
  unfold tailWord_5323383
  simp only [CollatzResearch.WordTrace]
  refine ⟨194159728873300027279470803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129439819248866684852980535 194159728873300027279470803)
  ·
    refine ⟨291239593309950040919206205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194159728873300027279470803 291239593309950040919206205)
    ·
      refine ⟨109214847491231265344702327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 291239593309950040919206205 109214847491231265344702327)
      ·
        refine ⟨163822271236846898017053491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109214847491231265344702327 163822271236846898017053491)
        ·
          refine ⟨245733406855270347025580237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163822271236846898017053491 245733406855270347025580237)
          ·
            refine ⟨92150027570726380134592589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 245733406855270347025580237 92150027570726380134592589)
            ·
              refine ⟨34556260339022392550472221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92150027570726380134592589 34556260339022392550472221)
              ·
                refine ⟨12958597627133397206427083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34556260339022392550472221 12958597627133397206427083)
                ·
                  refine ⟨19437896440700095809640625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12958597627133397206427083 19437896440700095809640625)
                  ·
                    refine ⟨14578422330525071857230469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19437896440700095809640625 14578422330525071857230469)
                    ·
                      refine ⟨2733454186973450973230713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14578422330525071857230469 2733454186973450973230713)
                      ·
                        rfl

theorem cell23_5323383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 3, 1, 2, 4].length) (baseStart_5323383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5323383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5323383 prefixEnd_5323383 := by exact prefixLift 5323383
  have htrace : WordTrace (prefixWord ++ tailWord_5323383) baseStart_5323383 baseEnd_5323383 := by
    simpa [prefixWord, tailWord_5323383, baseEnd_5323383] using wordTrace_append hprefix tailTrace_5323383
  have hstable : (prefixWord ++ tailWord_5323383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5323383).length < 2 ^ (prefixWord ++ tailWord_5323383).sum := by decide
  have hdescent : baseEnd_5323383 < baseStart_5323383 := by decide
  rcases family_descends (prefixWord ++ tailWord_5323383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5323403 : List Nat := [1, 1, 1, 1, 4, 1, 2, 3, 3, 3, 3]
def baseStart_5323403 : Nat := 118140960795 + 5323403 * 2 ^ 59
def prefixEnd_5323403 : Nat := 4983230072969 + 3 ^ 40 * 5323403 * 2
def baseEnd_5323403 : Nat := 2733464456586540894980621

theorem tailTrace_5323403 : CollatzResearch.WordTrace tailWord_5323403 prefixEnd_5323403 2733464456586540894980621 := by
  unfold tailWord_5323403
  simp only [CollatzResearch.WordTrace]
  refine ⟨194160458333227570695198863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129440305555485047130132575 194160458333227570695198863)
  ·
    refine ⟨291240687499841356042798295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194160458333227570695198863 291240687499841356042798295)
    ·
      refine ⟨436861031249762034064197443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 291240687499841356042798295 436861031249762034064197443)
      ·
        refine ⟨655291546874643051096296165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 436861031249762034064197443 655291546874643051096296165)
        ·
          refine ⟨122867165038995572080555531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 655291546874643051096296165 122867165038995572080555531)
          ·
            refine ⟨184300747558493358120833297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122867165038995572080555531 184300747558493358120833297)
            ·
              refine ⟨138225560668870018590624973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 184300747558493358120833297 138225560668870018590624973)
              ·
                refine ⟨51834585250826256971484365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 138225560668870018590624973 51834585250826256971484365)
                ·
                  refine ⟨19437969469059846364306637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51834585250826256971484365 19437969469059846364306637)
                  ·
                    refine ⟨7289238550897442386614989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19437969469059846364306637 7289238550897442386614989)
                    ·
                      refine ⟨2733464456586540894980621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7289238550897442386614989 2733464456586540894980621)
                      ·
                        rfl

theorem cell23_5323403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 3, 3, 3, 3].length) (baseStart_5323403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5323403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5323403 prefixEnd_5323403 := by exact prefixLift 5323403
  have htrace : WordTrace (prefixWord ++ tailWord_5323403) baseStart_5323403 baseEnd_5323403 := by
    simpa [prefixWord, tailWord_5323403, baseEnd_5323403] using wordTrace_append hprefix tailTrace_5323403
  have hstable : (prefixWord ++ tailWord_5323403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5323403).length < 2 ^ (prefixWord ++ tailWord_5323403).sum := by decide
  have hdescent : baseEnd_5323403 < baseStart_5323403 := by decide
  rcases family_descends (prefixWord ++ tailWord_5323403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5323431 : List Nat := [1, 1, 6, 3, 1, 1, 3, 1, 2, 4]
def baseStart_5323431 : Nat := 118140960795 + 5323431 * 2 ^ 59
def prefixEnd_5323431 : Nat := 4983230072969 + 3 ^ 40 * 5323431 * 2
def baseEnd_5323431 : Nat := 911159611348288928476831

theorem tailTrace_5323431 : CollatzResearch.WordTrace tailWord_5323431 prefixEnd_5323431 911159611348288928476831 := by
  unfold tailWord_5323431
  simp only [CollatzResearch.WordTrace]
  refine ⟨194161479577126131477218147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129440986384750754318145431 194161479577126131477218147)
  ·
    refine ⟨291242219365689197215827221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194161479577126131477218147 291242219365689197215827221)
    ·
      refine ⟨13651979032766681119491901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 291242219365689197215827221 13651979032766681119491901)
      ·
        refine ⟨5119492137287505419809463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13651979032766681119491901 5119492137287505419809463)
        ·
          refine ⟨7679238205931258129714195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5119492137287505419809463 7679238205931258129714195)
          ·
            refine ⟨11518857308896887194571293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7679238205931258129714195 11518857308896887194571293)
            ·
              refine ⟨4319571490836332697964235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11518857308896887194571293 4319571490836332697964235)
              ·
                refine ⟨6479357236254499046946353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4319571490836332697964235 6479357236254499046946353)
                ·
                  refine ⟨4859517927190874285209765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6479357236254499046946353 4859517927190874285209765)
                  ·
                    refine ⟨911159611348288928476831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4859517927190874285209765 911159611348288928476831)
                    ·
                      rfl

theorem cell23_5323431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 3, 1, 2, 4].length) (baseStart_5323431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5323431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5323431 prefixEnd_5323431 := by exact prefixLift 5323431
  have htrace : WordTrace (prefixWord ++ tailWord_5323431) baseStart_5323431 baseEnd_5323431 := by
    simpa [prefixWord, tailWord_5323431, baseEnd_5323431] using wordTrace_append hprefix tailTrace_5323431
  have hstable : (prefixWord ++ tailWord_5323431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5323431).length < 2 ^ (prefixWord ++ tailWord_5323431).sum := by decide
  have hdescent : baseEnd_5323431 < baseStart_5323431 := by decide
  rcases family_descends (prefixWord ++ tailWord_5323431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5323437 : List Nat := [1, 5, 2, 1, 1, 2, 3, 1, 1, 3, 3]
def baseStart_5323437 : Nat := 118140960795 + 5323437 * 2 ^ 59
def prefixEnd_5323437 : Nat := 4983230072969 + 3 ^ 40 * 5323437 * 2
def baseEnd_5323437 : Nat := 2733481914928793761955465

theorem tailTrace_5323437 : CollatzResearch.WordTrace tailWord_5323437 prefixEnd_5323437 2733481914928793761955465 := by
  unfold tailWord_5323437
  simp only [CollatzResearch.WordTrace]
  refine ⟨194161698415104394501936565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129441132276736263001291043 194161698415104394501936565)
  ·
    refine ⟨18202659226416036984556553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 194161698415104394501936565 18202659226416036984556553)
    ·
      refine ⟨13651994419812027738417415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18202659226416036984556553 13651994419812027738417415)
      ·
        refine ⟨20477991629718041607626123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13651994419812027738417415 20477991629718041607626123)
        ·
          refine ⟨30716987444577062411439185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20477991629718041607626123 30716987444577062411439185)
          ·
            refine ⟨23037740583432796808579389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30716987444577062411439185 23037740583432796808579389)
            ·
              refine ⟨8639152718787298803217271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23037740583432796808579389 8639152718787298803217271)
              ·
                refine ⟨12958729078180948204825907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8639152718787298803217271 12958729078180948204825907)
                ·
                  refine ⟨19438093617271422307238861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12958729078180948204825907 19438093617271422307238861)
                  ·
                    refine ⟨7289285106476783365214573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19438093617271422307238861 7289285106476783365214573)
                    ·
                      refine ⟨2733481914928793761955465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7289285106476783365214573 2733481914928793761955465)
                      ·
                        rfl

theorem cell23_5323437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 1, 1, 3, 3].length) (baseStart_5323437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5323437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5323437 prefixEnd_5323437 := by exact prefixLift 5323437
  have htrace : WordTrace (prefixWord ++ tailWord_5323437) baseStart_5323437 baseEnd_5323437 := by
    simpa [prefixWord, tailWord_5323437, baseEnd_5323437] using wordTrace_append hprefix tailTrace_5323437
  have hstable : (prefixWord ++ tailWord_5323437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5323437).length < 2 ^ (prefixWord ++ tailWord_5323437).sum := by decide
  have hdescent : baseEnd_5323437 < baseStart_5323437 := by decide
  rcases family_descends (prefixWord ++ tailWord_5323437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5323513 : List Nat := [1, 2, 1, 3, 1, 1, 1, 5, 1, 7]
def baseStart_5323513 : Nat := 118140960795 + 5323513 * 2 ^ 59
def prefixEnd_5323513 : Nat := 4983230072969 + 3 ^ 40 * 5323513 * 2
def baseEnd_5323513 : Nat := 911173646486178488201705

theorem tailTrace_5323513 : CollatzResearch.WordTrace tailWord_5323513 prefixEnd_5323513 911173646486178488201705 := by
  unfold tailWord_5323513
  simp only [CollatzResearch.WordTrace]
  refine ⟨194164470362829059481703193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129442980241886039654468795 194164470362829059481703193)
  ·
    refine ⟨145623352772121794611277395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194164470362829059481703193 145623352772121794611277395)
    ·
      refine ⟨218435029158182691916916093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145623352772121794611277395 218435029158182691916916093)
      ·
        refine ⟨81913135934318509468843535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 218435029158182691916916093 81913135934318509468843535)
        ·
          refine ⟨122869703901477764203265303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81913135934318509468843535 122869703901477764203265303)
          ·
            refine ⟨184304555852216646304897955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122869703901477764203265303 184304555852216646304897955)
            ·
              refine ⟨276456833778324969457346933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 184304555852216646304897955 276456833778324969457346933)
              ·
                refine ⟨25917828166717965886626275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 276456833778324969457346933 25917828166717965886626275)
                ·
                  refine ⟨38876742250076948829939413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25917828166717965886626275 38876742250076948829939413)
                  ·
                    refine ⟨911173646486178488201705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38876742250076948829939413 911173646486178488201705)
                    ·
                      rfl

theorem cell23_5323513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 5, 1, 7].length) (baseStart_5323513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5323513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5323513 prefixEnd_5323513 := by exact prefixLift 5323513
  have htrace : WordTrace (prefixWord ++ tailWord_5323513) baseStart_5323513 baseEnd_5323513 := by
    simpa [prefixWord, tailWord_5323513, baseEnd_5323513] using wordTrace_append hprefix tailTrace_5323513
  have hstable : (prefixWord ++ tailWord_5323513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5323513).length < 2 ^ (prefixWord ++ tailWord_5323513).sum := by decide
  have hdescent : baseEnd_5323513 < baseStart_5323513 := by decide
  rcases family_descends (prefixWord ++ tailWord_5323513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5323520 : List Nat := [2, 1, 1, 2, 1, 1, 2, 1, 3, 7, 2]
def baseStart_5323520 : Nat := 118140960795 + 5323520 * 2 ^ 59
def prefixEnd_5323520 : Nat := 4983230072969 + 3 ^ 40 * 5323520 * 2
def baseEnd_5323520 : Nat := 2733524533823116937217583

theorem tailTrace_5323520 : CollatzResearch.WordTrace tailWord_5323520 prefixEnd_5323520 2733524533823116937217583 := by
  unfold tailWord_5323520
  simp only [CollatzResearch.WordTrace]
  refine ⟨97082362836901849838604007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129443150449202466451472009 97082362836901849838604007)
  ·
    refine ⟨145623544255352774757906011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97082362836901849838604007 145623544255352774757906011)
    ·
      refine ⟨218435316383029162136859017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145623544255352774757906011 218435316383029162136859017)
      ·
        refine ⟨163826487287271871602644263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 218435316383029162136859017 163826487287271871602644263)
        ·
          refine ⟨245739730930907807403966395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163826487287271871602644263 245739730930907807403966395)
          ·
            refine ⟨368609596396361711105949593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 245739730930907807403966395 368609596396361711105949593)
            ·
              refine ⟨276457197297271283329462195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 368609596396361711105949593 276457197297271283329462195)
              ·
                refine ⟨414685795945906924994193293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 276457197297271283329462195 414685795945906924994193293)
                ·
                  refine ⟨155507173479715096872822485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 414685795945906924994193293 155507173479715096872822485)
                  ·
                    refine ⟨3644699378430822582956777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 155507173479715096872822485 3644699378430822582956777)
                    ·
                      refine ⟨2733524533823116937217583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3644699378430822582956777 2733524533823116937217583)
                      ·
                        rfl

theorem cell23_5323520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 3, 7, 2].length) (baseStart_5323520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5323520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5323520 prefixEnd_5323520 := by exact prefixLift 5323520
  have htrace : WordTrace (prefixWord ++ tailWord_5323520) baseStart_5323520 baseEnd_5323520 := by
    simpa [prefixWord, tailWord_5323520, baseEnd_5323520] using wordTrace_append hprefix tailTrace_5323520
  have hstable : (prefixWord ++ tailWord_5323520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5323520).length < 2 ^ (prefixWord ++ tailWord_5323520).sum := by decide
  have hdescent : baseEnd_5323520 < baseStart_5323520 := by decide
  rcases family_descends (prefixWord ++ tailWord_5323520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5323530 : List Nat := [3, 1, 2, 2, 1, 2, 1, 4, 2, 5]
def baseStart_5323530 : Nat := 118140960795 + 5323530 * 2 ^ 59
def prefixEnd_5323530 : Nat := 4983230072969 + 3 ^ 40 * 5323530 * 2
def baseEnd_5323530 : Nat := 911176556209887299364179

theorem tailTrace_5323530 : CollatzResearch.WordTrace tailWord_5323530 prefixEnd_5323530 911176556209887299364179 := by
  unfold tailWord_5323530
  simp only [CollatzResearch.WordTrace]
  refine ⟨48541272600941867846268011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129443393602511647590048029 48541272600941867846268011)
  ·
    refine ⟨72811908901412801769402017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48541272600941867846268011 72811908901412801769402017)
    ·
      refine ⟨54608931676059601327051513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72811908901412801769402017 54608931676059601327051513)
      ·
        refine ⟨40956698757044700995288635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54608931676059601327051513 40956698757044700995288635)
        ·
          refine ⟨61435048135567051492932953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40956698757044700995288635 61435048135567051492932953)
          ·
            refine ⟨46076286101675288619699715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61435048135567051492932953 46076286101675288619699715)
            ·
              refine ⟨69114429152512932929549573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46076286101675288619699715 69114429152512932929549573)
              ·
                refine ⟨12958955466096174924290545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69114429152512932929549573 12958955466096174924290545)
                ·
                  refine ⟨9719216599572131193217909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12958955466096174924290545 9719216599572131193217909)
                  ·
                    refine ⟨911176556209887299364179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9719216599572131193217909 911176556209887299364179)
                    ·
                      rfl

theorem cell23_5323530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 4, 2, 5].length) (baseStart_5323530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5323530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5323530 prefixEnd_5323530 := by exact prefixLift 5323530
  have htrace : WordTrace (prefixWord ++ tailWord_5323530) baseStart_5323530 baseEnd_5323530 := by
    simpa [prefixWord, tailWord_5323530, baseEnd_5323530] using wordTrace_append hprefix tailTrace_5323530
  have hstable : (prefixWord ++ tailWord_5323530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5323530).length < 2 ^ (prefixWord ++ tailWord_5323530).sum := by decide
  have hdescent : baseEnd_5323530 < baseStart_5323530 := by decide
  rcases family_descends (prefixWord ++ tailWord_5323530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5323563 : List Nat := [1, 1, 1, 1, 2, 1, 2, 4, 1, 3, 6]
def baseStart_5323563 : Nat := 118140960795 + 5323563 * 2 ^ 59
def prefixEnd_5323563 : Nat := 4983230072969 + 3 ^ 40 * 5323563 * 2
def baseEnd_5323563 : Nat := 2733546613491260268979885

theorem tailTrace_5323563 : CollatzResearch.WordTrace tailWord_5323563 prefixEnd_5323563 2733546613491260268979885 := by
  unfold tailWord_5323563
  simp only [CollatzResearch.WordTrace]
  refine ⟨194166294012647918021023343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129444196008431945347348895 194166294012647918021023343)
  ·
    refine ⟨291249441018971877031535015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194166294012647918021023343 291249441018971877031535015)
    ·
      refine ⟨436874161528457815547302523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 291249441018971877031535015 436874161528457815547302523)
      ·
        refine ⟨655311242292686723320953785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 436874161528457815547302523 655311242292686723320953785)
        ·
          refine ⟨491483431719515042490715339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 655311242292686723320953785 491483431719515042490715339)
          ·
            refine ⟨737225147579272563736073009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 491483431719515042490715339 737225147579272563736073009)
            ·
              refine ⟨552918860684454422802054757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 737225147579272563736073009 552918860684454422802054757)
              ·
                refine ⟨103672286378335204275385267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 552918860684454422802054757 103672286378335204275385267)
                ·
                  refine ⟨155508429567502806413077901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 103672286378335204275385267 155508429567502806413077901)
                  ·
                    refine ⟨58315661087813552404904213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 155508429567502806413077901 58315661087813552404904213)
                    ·
                      refine ⟨2733546613491260268979885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58315661087813552404904213 2733546613491260268979885)
                      ·
                        rfl

theorem cell23_5323563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 3, 6].length) (baseStart_5323563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5323563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5323563 prefixEnd_5323563 := by exact prefixLift 5323563
  have htrace : WordTrace (prefixWord ++ tailWord_5323563) baseStart_5323563 baseEnd_5323563 := by
    simpa [prefixWord, tailWord_5323563, baseEnd_5323563] using wordTrace_append hprefix tailTrace_5323563
  have hstable : (prefixWord ++ tailWord_5323563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5323563).length < 2 ^ (prefixWord ++ tailWord_5323563).sum := by decide
  have hdescent : baseEnd_5323563 < baseStart_5323563 := by decide
  rcases family_descends (prefixWord ++ tailWord_5323563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5323617 : List Nat := [1, 2, 3, 1, 1, 1, 2, 3, 5, 1, 3]
def baseStart_5323617 : Nat := 118140960795 + 5323617 * 2 ^ 59
def prefixEnd_5323617 : Nat := 4983230072969 + 3 ^ 40 * 5323617 * 2
def baseEnd_5323617 : Nat := 2733574341446603057704637

theorem tailTrace_5323617 : CollatzResearch.WordTrace tailWord_5323617 prefixEnd_5323617 2733574341446603057704637 := by
  unfold tailWord_5323617
  simp only [CollatzResearch.WordTrace]
  refine ⟨194168263554452285243489105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129445509036301523495659403 194168263554452285243489105)
  ·
    refine ⟨145626197665839213932616829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194168263554452285243489105 145626197665839213932616829)
    ·
      refine ⟨54609824124689705224731311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145626197665839213932616829 54609824124689705224731311)
      ·
        refine ⟨81914736187034557837096967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54609824124689705224731311 81914736187034557837096967)
        ·
          refine ⟨122872104280551836755645451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81914736187034557837096967 122872104280551836755645451)
          ·
            refine ⟨184308156420827755133468177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122872104280551836755645451 184308156420827755133468177)
            ·
              refine ⟨138231117315620816350101133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 184308156420827755133468177 138231117315620816350101133)
              ·
                refine ⟨51836668993357806131287925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 138231117315620816350101133 51836668993357806131287925)
                ·
                  refine ⟨4859687718127294324808243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51836668993357806131287925 4859687718127294324808243)
                  ·
                    refine ⟨7289531577190941487212365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4859687718127294324808243 7289531577190941487212365)
                    ·
                      refine ⟨2733574341446603057704637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7289531577190941487212365 2733574341446603057704637)
                      ·
                        rfl

theorem cell23_5323617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 3, 5, 1, 3].length) (baseStart_5323617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5323617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5323617 prefixEnd_5323617 := by exact prefixLift 5323617
  have htrace : WordTrace (prefixWord ++ tailWord_5323617) baseStart_5323617 baseEnd_5323617 := by
    simpa [prefixWord, tailWord_5323617, baseEnd_5323617] using wordTrace_append hprefix tailTrace_5323617
  have hstable : (prefixWord ++ tailWord_5323617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5323617).length < 2 ^ (prefixWord ++ tailWord_5323617).sum := by decide
  have hdescent : baseEnd_5323617 < baseStart_5323617 := by decide
  rcases family_descends (prefixWord ++ tailWord_5323617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5323627 : List Nat := [1, 1, 1, 1, 2, 2, 6, 1, 1, 5, 2]
def baseStart_5323627 : Nat := 118140960795 + 5323627 * 2 ^ 59
def prefixEnd_5323627 : Nat := 4983230072969 + 3 ^ 40 * 5323627 * 2
def baseEnd_5323627 : Nat := 2733579476253148018579591

theorem tailTrace_5323627 : CollatzResearch.WordTrace tailWord_5323627 prefixEnd_5323627 2733579476253148018579591 := by
  unfold tailWord_5323627
  simp only [CollatzResearch.WordTrace]
  refine ⟨194168628284416056951353135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129445752189610704634235423 194168628284416056951353135)
  ·
    refine ⟨291252942426624085427029703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194168628284416056951353135 291252942426624085427029703)
    ·
      refine ⟨436879413639936128140544555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 291252942426624085427029703 436879413639936128140544555)
      ·
        refine ⟨655319120459904192210816833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 436879413639936128140544555 655319120459904192210816833)
        ·
          refine ⟨491489340344928144158112625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 655319120459904192210816833 491489340344928144158112625)
          ·
            refine ⟨368617005258696108118584469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 491489340344928144158112625 368617005258696108118584469)
            ·
              refine ⟨17278922121501380068058647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 368617005258696108118584469 17278922121501380068058647)
              ·
                refine ⟨25918383182252070102087971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17278922121501380068058647 25918383182252070102087971)
                ·
                  refine ⟨38877574773378105153131957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25918383182252070102087971 38877574773378105153131957)
                  ·
                    refine ⟨3644772635004197358106121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38877574773378105153131957 3644772635004197358106121)
                    ·
                      refine ⟨2733579476253148018579591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3644772635004197358106121 2733579476253148018579591)
                      ·
                        rfl

theorem cell23_5323627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 1, 1, 5, 2].length) (baseStart_5323627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5323627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5323627 prefixEnd_5323627 := by exact prefixLift 5323627
  have htrace : WordTrace (prefixWord ++ tailWord_5323627) baseStart_5323627 baseEnd_5323627 := by
    simpa [prefixWord, tailWord_5323627, baseEnd_5323627] using wordTrace_append hprefix tailTrace_5323627
  have hstable : (prefixWord ++ tailWord_5323627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5323627).length < 2 ^ (prefixWord ++ tailWord_5323627).sum := by decide
  have hdescent : baseEnd_5323627 < baseStart_5323627 := by decide
  rcases family_descends (prefixWord ++ tailWord_5323627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5323674 : List Nat := [3, 1, 1, 4, 3, 1, 1, 1, 3, 1, 4]
def baseStart_5323674 : Nat := 118140960795 + 5323674 * 2 ^ 59
def prefixEnd_5323674 : Nat := 4983230072969 + 3 ^ 40 * 5323674 * 2
def baseEnd_5323674 : Nat := 2733603609843909334691875

theorem tailTrace_5323674 : CollatzResearch.WordTrace tailWord_5323674 prefixEnd_5323674 2733603609843909334691875 := by
  unfold tailWord_5323674
  simp only [CollatzResearch.WordTrace]
  refine ⟨48542585628811445994578519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129446895010163855985542717 48542585628811445994578519)
  ·
    refine ⟨72813878443217168991867779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48542585628811445994578519 72813878443217168991867779)
    ·
      refine ⟨109220817664825753487801669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72813878443217168991867779 109220817664825753487801669)
      ·
        refine ⟨20478903312154828778962813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 109220817664825753487801669 20478903312154828778962813)
        ·
          refine ⟨7679588742058060792111055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20478903312154828778962813 7679588742058060792111055)
          ·
            refine ⟨11519383113087091188166583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7679588742058060792111055 11519383113087091188166583)
            ·
              refine ⟨17279074669630636782249875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11519383113087091188166583 17279074669630636782249875)
              ·
                refine ⟨25918612004445955173374813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17279074669630636782249875 25918612004445955173374813)
                ·
                  refine ⟨9719479501667233190015555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25918612004445955173374813 9719479501667233190015555)
                  ·
                    refine ⟨14579219252500849785023333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9719479501667233190015555 14579219252500849785023333)
                    ·
                      refine ⟨2733603609843909334691875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14579219252500849785023333 2733603609843909334691875)
                      ·
                        rfl

theorem cell23_5323674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 1, 3, 1, 4].length) (baseStart_5323674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5323674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5323674 prefixEnd_5323674 := by exact prefixLift 5323674
  have htrace : WordTrace (prefixWord ++ tailWord_5323674) baseStart_5323674 baseEnd_5323674 := by
    simpa [prefixWord, tailWord_5323674, baseEnd_5323674] using wordTrace_append hprefix tailTrace_5323674
  have hstable : (prefixWord ++ tailWord_5323674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5323674).length < 2 ^ (prefixWord ++ tailWord_5323674).sum := by decide
  have hdescent : baseEnd_5323674 < baseStart_5323674 := by decide
  rcases family_descends (prefixWord ++ tailWord_5323674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5323680 : List Nat := [2, 1, 1, 4, 1, 1, 4, 9]
def baseStart_5323680 : Nat := 118140960795 + 5323680 * 2 ^ 59
def prefixEnd_5323680 : Nat := 4983230072969 + 3 ^ 40 * 5323680 * 2
def baseEnd_5323680 : Nat := 101244692249179122637661

theorem tailTrace_5323680 : CollatzResearch.WordTrace tailWord_5323680 prefixEnd_5323680 101244692249179122637661 := by
  unfold tailWord_5323680
  simp only [CollatzResearch.WordTrace]
  refine ⟨97085280676612023501516247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129447040902149364668688329 97085280676612023501516247)
  ·
    refine ⟨145627921014918035252274371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97085280676612023501516247 145627921014918035252274371)
    ·
      refine ⟨218441881522377052878411557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145627921014918035252274371 218441881522377052878411557)
      ·
        refine ⟨40957852785445697414702167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 218441881522377052878411557 40957852785445697414702167)
        ·
          refine ⟨61436779178168546122053251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40957852785445697414702167 61436779178168546122053251)
          ·
            refine ⟨92155168767252819183079877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61436779178168546122053251 92155168767252819183079877)
            ·
              refine ⟨17279094143859903596827477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 92155168767252819183079877 17279094143859903596827477)
              ·
                refine ⟨101244692249179122637661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17279094143859903596827477 101244692249179122637661)
                ·
                  rfl

theorem cell23_5323680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 9].length) (baseStart_5323680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5323680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5323680 prefixEnd_5323680 := by exact prefixLift 5323680
  have htrace : WordTrace (prefixWord ++ tailWord_5323680) baseStart_5323680 baseEnd_5323680 := by
    simpa [prefixWord, tailWord_5323680, baseEnd_5323680] using wordTrace_append hprefix tailTrace_5323680
  have hstable : (prefixWord ++ tailWord_5323680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5323680).length < 2 ^ (prefixWord ++ tailWord_5323680).sum := by decide
  have hdescent : baseEnd_5323680 < baseStart_5323680 := by decide
  rcases family_descends (prefixWord ++ tailWord_5323680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5323697 : List Nat := [1, 2, 2, 4, 4, 10]
def baseStart_5323697 : Nat := 118140960795 + 5323697 * 2 ^ 59
def prefixEnd_5323697 : Nat := 4983230072969 + 3 ^ 40 * 5323697 * 2
def baseEnd_5323697 : Nat := 11249446172423714998783

theorem tailTrace_5323697 : CollatzResearch.WordTrace tailWord_5323697 prefixEnd_5323697 11249446172423714998783 := by
  unfold tailWord_5323697
  simp only [CollatzResearch.WordTrace]
  refine ⟨194171181394162458906401345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129447454262774972604267563 194171181394162458906401345)
  ·
    refine ⟨145628386045621844179801009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194171181394162458906401345 145628386045621844179801009)
    ·
      refine ⟨109221289534216383134850757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145628386045621844179801009 109221289534216383134850757)
      ·
        refine ⟨20478991787665571837784517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 109221289534216383134850757 20478991787665571837784517)
        ·
          refine ⟨3839810960187294719584597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20478991787665571837784517 3839810960187294719584597)
          ·
            refine ⟨11249446172423714998783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3839810960187294719584597 11249446172423714998783)
            ·
              rfl

theorem cell23_5323697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 10].length) (baseStart_5323697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5323697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5323697 prefixEnd_5323697 := by exact prefixLift 5323697
  have htrace : WordTrace (prefixWord ++ tailWord_5323697) baseStart_5323697 baseEnd_5323697 := by
    simpa [prefixWord, tailWord_5323697, baseEnd_5323697] using wordTrace_append hprefix tailTrace_5323697
  have hstable : (prefixWord ++ tailWord_5323697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5323697).length < 2 ^ (prefixWord ++ tailWord_5323697).sum := by decide
  have hdescent : baseEnd_5323697 < baseStart_5323697 := by decide
  rcases family_descends (prefixWord ++ tailWord_5323697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5323724 : List Nat := [2, 2, 1, 4, 1, 1, 4, 1, 1, 3, 3]
def baseStart_5323724 : Nat := 118140960795 + 5323724 * 2 ^ 59
def prefixEnd_5323724 : Nat := 4983230072969 + 3 ^ 40 * 5323724 * 2
def baseEnd_5323724 : Nat := 2733629283876634139066645

theorem tailTrace_5323724 : CollatzResearch.WordTrace tailWord_5323724 prefixEnd_5323724 2733629283876634139066645 := by
  unfold tailWord_5323724
  simp only [CollatzResearch.WordTrace]
  refine ⟨97086083082532321258817113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129448110776709761678422817 97086083082532321258817113)
  ·
    refine ⟨72814562311899240944112835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97086083082532321258817113 72814562311899240944112835)
    ·
      refine ⟨109221843467848861416169253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72814562311899240944112835 109221843467848861416169253)
      ·
        refine ⟨20479095650221661515531735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 109221843467848861416169253 20479095650221661515531735)
        ·
          refine ⟨30718643475332492273297603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20479095650221661515531735 30718643475332492273297603)
          ·
            refine ⟨46077965212998738409946405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30718643475332492273297603 46077965212998738409946405)
            ·
              refine ⟨8639618477437263451864951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46077965212998738409946405 8639618477437263451864951)
              ·
                refine ⟨12959427716155895177797427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8639618477437263451864951 12959427716155895177797427)
                ·
                  refine ⟨19439141574233842766696141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12959427716155895177797427 19439141574233842766696141)
                  ·
                    refine ⟨7289678090337691037511053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19439141574233842766696141 7289678090337691037511053)
                    ·
                      refine ⟨2733629283876634139066645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7289678090337691037511053 2733629283876634139066645)
                      ·
                        rfl

theorem cell23_5323724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 1, 1, 3, 3].length) (baseStart_5323724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5323724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5323724 prefixEnd_5323724 := by exact prefixLift 5323724
  have htrace : WordTrace (prefixWord ++ tailWord_5323724) baseStart_5323724 baseEnd_5323724 := by
    simpa [prefixWord, tailWord_5323724, baseEnd_5323724] using wordTrace_append hprefix tailTrace_5323724
  have hstable : (prefixWord ++ tailWord_5323724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5323724).length < 2 ^ (prefixWord ++ tailWord_5323724).sum := by decide
  have hdescent : baseEnd_5323724 < baseStart_5323724 := by decide
  rcases family_descends (prefixWord ++ tailWord_5323724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5323787 : List Nat := [1, 1, 1, 1, 6, 2, 2, 2, 7]
def baseStart_5323787 : Nat := 118140960795 + 5323787 * 2 ^ 59
def prefixEnd_5323787 : Nat := 4983230072969 + 3 ^ 40 * 5323787 * 2
def baseEnd_5323787 : Nat := 303740181461985265842095

theorem tailTrace_5323787 : CollatzResearch.WordTrace tailWord_5323787 prefixEnd_5323787 303740181461985265842095 := by
  unfold tailWord_5323787
  simp only [CollatzResearch.WordTrace]
  refine ⟨194174463963836404277177615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129449642642557602851451743 194174463963836404277177615)
  ·
    refine ⟨291261695945754606415766423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194174463963836404277177615 291261695945754606415766423)
    ·
      refine ⟨436892543918631909623649635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 291261695945754606415766423 436892543918631909623649635)
      ·
        refine ⟨655338815877947864435474453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 436892543918631909623649635 655338815877947864435474453)
        ·
          refine ⟨30719006994278806145412865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 655338815877947864435474453 30719006994278806145412865)
          ·
            refine ⟨23039255245709104609059649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30719006994278806145412865 23039255245709104609059649)
            ·
              refine ⟨17279441434281828456794737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23039255245709104609059649 17279441434281828456794737)
              ·
                refine ⟨12959581075711371342596053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17279441434281828456794737 12959581075711371342596053)
                ·
                  refine ⟨303740181461985265842095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12959581075711371342596053 303740181461985265842095)
                  ·
                    rfl

theorem cell23_5323787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 2, 7].length) (baseStart_5323787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5323787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5323787 prefixEnd_5323787 := by exact prefixLift 5323787
  have htrace : WordTrace (prefixWord ++ tailWord_5323787) baseStart_5323787 baseEnd_5323787 := by
    simpa [prefixWord, tailWord_5323787, baseEnd_5323787] using wordTrace_append hprefix tailTrace_5323787
  have hstable : (prefixWord ++ tailWord_5323787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5323787).length < 2 ^ (prefixWord ++ tailWord_5323787).sum := by decide
  have hdescent : baseEnd_5323787 < baseStart_5323787 := by decide
  rcases family_descends (prefixWord ++ tailWord_5323787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5323824 : List Nat := [2, 1, 1, 1, 2, 4, 2, 1, 2, 5, 2]
def baseStart_5323824 : Nat := 118140960795 + 5323824 * 2 ^ 59
def prefixEnd_5323824 : Nat := 4983230072969 + 3 ^ 40 * 5323824 * 2
def baseEnd_5323824 : Nat := 2733680631942083747816185

theorem tailTrace_5323824 : CollatzResearch.WordTrace tailWord_5323824 prefixEnd_5323824 2733680631942083747816185 := by
  unfold tailWord_5323824
  simp only [CollatzResearch.WordTrace]
  refine ⟨97087906732351179798137263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129450542309801573064183017 97087906732351179798137263)
  ·
    refine ⟨145631860098526769697205895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97087906732351179798137263 145631860098526769697205895)
    ·
      refine ⟨218447790147790154545808843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145631860098526769697205895 218447790147790154545808843)
      ·
        refine ⟨327671685221685231818713265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218447790147790154545808843 327671685221685231818713265)
        ·
          refine ⟨245753763916263923864034949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 327671685221685231818713265 245753763916263923864034949)
          ·
            refine ⟨46078830734299485724506553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 245753763916263923864034949 46078830734299485724506553)
            ·
              refine ⟨34559123050724614293379915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46078830734299485724506553 34559123050724614293379915)
              ·
                refine ⟨51838684576086921440069873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34559123050724614293379915 51838684576086921440069873)
                ·
                  refine ⟨38879013432065191080052405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51838684576086921440069873 38879013432065191080052405)
                  ·
                    refine ⟨3644907509256111663754913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38879013432065191080052405 3644907509256111663754913)
                    ·
                      refine ⟨2733680631942083747816185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3644907509256111663754913 2733680631942083747816185)
                      ·
                        rfl

theorem cell23_5323824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 1, 2, 5, 2].length) (baseStart_5323824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5323824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5323824 prefixEnd_5323824 := by exact prefixLift 5323824
  have htrace : WordTrace (prefixWord ++ tailWord_5323824) baseStart_5323824 baseEnd_5323824 := by
    simpa [prefixWord, tailWord_5323824, baseEnd_5323824] using wordTrace_append hprefix tailTrace_5323824
  have hstable : (prefixWord ++ tailWord_5323824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5323824).length < 2 ^ (prefixWord ++ tailWord_5323824).sum := by decide
  have hdescent : baseEnd_5323824 < baseStart_5323824 := by decide
  rcases family_descends (prefixWord ++ tailWord_5323824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5323902 : List Nat := [4, 2, 4, 1, 1, 2, 1, 1, 2, 5]
def baseStart_5323902 : Nat := 118140960795 + 5323902 * 2 ^ 59
def prefixEnd_5323902 : Nat := 4983230072969 + 3 ^ 40 * 5323902 * 2
def baseEnd_5323902 : Nat := 911240227811044814213609

theorem tailTrace_5323902 : CollatzResearch.WordTrace tailWord_5323902 prefixEnd_5323902 911240227811044814213609 := by
  unfold tailWord_5323902
  simp only [CollatzResearch.WordTrace]
  refine ⟨24272332294802472364701745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129452438905613185945075973 24272332294802472364701745)
  ·
    refine ⟨18204249221101854273526309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24272332294802472364701745 18204249221101854273526309)
    ·
      refine ⟨3413296728956597676286183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18204249221101854273526309 3413296728956597676286183)
      ·
        refine ⟨5119945093434896514429275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3413296728956597676286183 5119945093434896514429275)
        ·
          refine ⟨7679917640152344771643913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5119945093434896514429275 7679917640152344771643913)
          ·
            refine ⟨5759938230114258578732935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7679917640152344771643913 5759938230114258578732935)
            ·
              refine ⟨8639907345171387868099403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5759938230114258578732935 8639907345171387868099403)
              ·
                refine ⟨12959861017757081802149105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8639907345171387868099403 12959861017757081802149105)
                ·
                  refine ⟨9719895763317811351611829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12959861017757081802149105 9719895763317811351611829)
                  ·
                    refine ⟨911240227811044814213609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9719895763317811351611829 911240227811044814213609)
                    ·
                      rfl

theorem cell23_5323902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_5323902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5323902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5323902 prefixEnd_5323902 := by exact prefixLift 5323902
  have htrace : WordTrace (prefixWord ++ tailWord_5323902) baseStart_5323902 baseEnd_5323902 := by
    simpa [prefixWord, tailWord_5323902, baseEnd_5323902] using wordTrace_append hprefix tailTrace_5323902
  have hstable : (prefixWord ++ tailWord_5323902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5323902).length < 2 ^ (prefixWord ++ tailWord_5323902).sum := by decide
  have hdescent : baseEnd_5323902 < baseStart_5323902 := by decide
  rcases family_descends (prefixWord ++ tailWord_5323902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5323908 : List Nat := [2, 3, 2, 1, 2, 4, 1, 1, 2, 2, 3]
def baseStart_5323908 : Nat := 118140960795 + 5323908 * 2 ^ 59
def prefixEnd_5323908 : Nat := 4983230072969 + 3 ^ 40 * 5323908 * 2
def baseEnd_5323908 : Nat := 2733723764317061419165799

theorem tailTrace_5323908 : CollatzResearch.WordTrace tailWord_5323908 prefixEnd_5323908 2733723764317061419165799 := by
  unfold tailWord_5323908
  simp only [CollatzResearch.WordTrace]
  refine ⟨97089438598199020971166189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129452584797598694628221585 97089438598199020971166189)
  ·
    refine ⟨36408539474324632864187321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97089438598199020971166189 36408539474324632864187321)
    ·
      refine ⟨27306404605743474648140491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36408539474324632864187321 27306404605743474648140491)
      ·
        refine ⟨40959606908615211972210737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27306404605743474648140491 40959606908615211972210737)
        ·
          refine ⟨30719705181461408979158053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40959606908615211972210737 30719705181461408979158053)
          ·
            refine ⟨5759944721524014183592135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30719705181461408979158053 5759944721524014183592135)
            ·
              refine ⟨8639917082286021275388203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5759944721524014183592135 8639917082286021275388203)
              ·
                refine ⟨12959875623429031913082305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8639917082286021275388203 12959875623429031913082305)
                ·
                  refine ⟨9719906717571773934811729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12959875623429031913082305 9719906717571773934811729)
                  ·
                    refine ⟨7289930038178830451108797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9719906717571773934811729 7289930038178830451108797)
                    ·
                      refine ⟨2733723764317061419165799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7289930038178830451108797 2733723764317061419165799)
                      ·
                        rfl

theorem cell23_5323908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 1, 2, 2, 3].length) (baseStart_5323908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5323908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5323908 prefixEnd_5323908 := by exact prefixLift 5323908
  have htrace : WordTrace (prefixWord ++ tailWord_5323908) baseStart_5323908 baseEnd_5323908 := by
    simpa [prefixWord, tailWord_5323908, baseEnd_5323908] using wordTrace_append hprefix tailTrace_5323908
  have hstable : (prefixWord ++ tailWord_5323908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5323908).length < 2 ^ (prefixWord ++ tailWord_5323908).sum := by decide
  have hdescent : baseEnd_5323908 < baseStart_5323908 := by decide
  rcases family_descends (prefixWord ++ tailWord_5323908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5323961 : List Nat := [1, 2, 1, 4, 1, 3, 1, 4, 1, 1, 4]
def baseStart_5323961 : Nat := 118140960795 + 5323961 * 2 ^ 59
def prefixEnd_5323961 : Nat := 4983230072969 + 3 ^ 40 * 5323961 * 2
def baseEnd_5323961 : Nat := 2733750978791749711803055

theorem tailTrace_5323961 : CollatzResearch.WordTrace tailWord_5323961 prefixEnd_5323961 2733750978791749711803055 := by
  unfold tailWord_5323961
  simp only [CollatzResearch.WordTrace]
  refine ⟨194180810265206031994011737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129453873510137354662674491 194180810265206031994011737)
  ·
    refine ⟨145635607698904523995508803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194180810265206031994011737 145635607698904523995508803)
    ·
      refine ⟨218453411548356785993263205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145635607698904523995508803 218453411548356785993263205)
      ·
        refine ⟨40960014665316897373736851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 218453411548356785993263205 40960014665316897373736851)
        ·
          refine ⟨61440021997975346060605277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40960014665316897373736851 61440021997975346060605277)
          ·
            refine ⟨23040008249240754772726979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61440021997975346060605277 23040008249240754772726979)
            ·
              refine ⟨34560012373861132159090469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23040008249240754772726979 34560012373861132159090469)
              ·
                refine ⟨6480002320098962279829463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34560012373861132159090469 6480002320098962279829463)
                ·
                  refine ⟨9720003480148443419744195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6480002320098962279829463 9720003480148443419744195)
                  ·
                    refine ⟨14580005220222665129616293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9720003480148443419744195 14580005220222665129616293)
                    ·
                      refine ⟨2733750978791749711803055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14580005220222665129616293 2733750978791749711803055)
                      ·
                        rfl

theorem cell23_5323961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 4, 1, 1, 4].length) (baseStart_5323961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5323961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5323961 prefixEnd_5323961 := by exact prefixLift 5323961
  have htrace : WordTrace (prefixWord ++ tailWord_5323961) baseStart_5323961 baseEnd_5323961 := by
    simpa [prefixWord, tailWord_5323961, baseEnd_5323961] using wordTrace_append hprefix tailTrace_5323961
  have hstable : (prefixWord ++ tailWord_5323961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5323961).length < 2 ^ (prefixWord ++ tailWord_5323961).sum := by decide
  have hdescent : baseEnd_5323961 < baseStart_5323961 := by decide
  rcases family_descends (prefixWord ++ tailWord_5323961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5324015 : List Nat := [1, 1, 2, 1, 7, 2, 1, 2, 1, 2, 3]
def baseStart_5324015 : Nat := 118140960795 + 5324015 * 2 ^ 59
def prefixEnd_5324015 : Nat := 4983230072969 + 3 ^ 40 * 5324015 * 2
def baseEnd_5324015 : Nat := 2733778706747092500527807

theorem tailTrace_5324015 : CollatzResearch.WordTrace tailWord_5324015 prefixEnd_5324015 2733778706747092500527807 := by
  unfold tailWord_5324015
  simp only [CollatzResearch.WordTrace]
  refine ⟨194182779807010399216477499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129455186538006932810984999 194182779807010399216477499)
  ·
    refine ⟨291274169710515598824716249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194182779807010399216477499 291274169710515598824716249)
    ·
      refine ⟨218455627282886699118537187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 291274169710515598824716249 218455627282886699118537187)
      ·
        refine ⟨327683440924330048677805781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218455627282886699118537187 327683440924330048677805781)
        ·
          refine ⟨7680080646663985515886073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 327683440924330048677805781 7680080646663985515886073)
          ·
            refine ⟨5760060484997989136914555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7680080646663985515886073 5760060484997989136914555)
            ·
              refine ⟨8640090727496983705371833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5760060484997989136914555 8640090727496983705371833)
              ·
                refine ⟨6480068045622737779028875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8640090727496983705371833 6480068045622737779028875)
                ·
                  refine ⟨9720102068434106668543313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6480068045622737779028875 9720102068434106668543313)
                  ·
                    refine ⟨7290076551325580001407485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9720102068434106668543313 7290076551325580001407485)
                    ·
                      refine ⟨2733778706747092500527807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7290076551325580001407485 2733778706747092500527807)
                      ·
                        rfl

theorem cell23_5324015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 2, 1, 2, 3].length) (baseStart_5324015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5324015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5324015 prefixEnd_5324015 := by exact prefixLift 5324015
  have htrace : WordTrace (prefixWord ++ tailWord_5324015) baseStart_5324015 baseEnd_5324015 := by
    simpa [prefixWord, tailWord_5324015, baseEnd_5324015] using wordTrace_append hprefix tailTrace_5324015
  have hstable : (prefixWord ++ tailWord_5324015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5324015).length < 2 ^ (prefixWord ++ tailWord_5324015).sum := by decide
  have hdescent : baseEnd_5324015 < baseStart_5324015 := by decide
  rcases family_descends (prefixWord ++ tailWord_5324015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5324028 : List Nat := [2, 2, 2, 1, 5, 1, 1, 2, 1, 3, 3]
def baseStart_5324028 : Nat := 118140960795 + 5324028 * 2 ^ 59
def prefixEnd_5324028 : Nat := 4983230072969 + 3 ^ 40 * 5324028 * 2
def baseEnd_5324028 : Nat := 2733785381995600949665247

theorem tailTrace_5324028 : CollatzResearch.WordTrace tailWord_5324028 prefixEnd_5324028 2733785381995600949665247 := by
  unfold tailWord_5324028
  simp only [CollatzResearch.WordTrace]
  refine ⟨97091626977981651218350369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129455502637308868291133825 97091626977981651218350369)
  ·
    refine ⟨72818720233486238413762777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97091626977981651218350369 72818720233486238413762777)
    ·
      refine ⟨54614040175114678810322083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72818720233486238413762777 54614040175114678810322083)
      ·
        refine ⟨81921060262672018215483125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54614040175114678810322083 81921060262672018215483125)
        ·
          refine ⟨7680099399625501707701543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 81921060262672018215483125 7680099399625501707701543)
          ·
            refine ⟨11520149099438252561552315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7680099399625501707701543 11520149099438252561552315)
            ·
              refine ⟨17280223649157378842328473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11520149099438252561552315 17280223649157378842328473)
              ·
                refine ⟨12960167736868034131746355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17280223649157378842328473 12960167736868034131746355)
                ·
                  refine ⟨19440251605302051197619533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12960167736868034131746355 19440251605302051197619533)
                  ·
                    refine ⟨7290094351988269199107325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19440251605302051197619533 7290094351988269199107325)
                    ·
                      refine ⟨2733785381995600949665247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7290094351988269199107325 2733785381995600949665247)
                      ·
                        rfl

theorem cell23_5324028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 2, 1, 3, 3].length) (baseStart_5324028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5324028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5324028 prefixEnd_5324028 := by exact prefixLift 5324028
  have htrace : WordTrace (prefixWord ++ tailWord_5324028) baseStart_5324028 baseEnd_5324028 := by
    simpa [prefixWord, tailWord_5324028, baseEnd_5324028] using wordTrace_append hprefix tailTrace_5324028
  have hstable : (prefixWord ++ tailWord_5324028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5324028).length < 2 ^ (prefixWord ++ tailWord_5324028).sum := by decide
  have hdescent : baseEnd_5324028 < baseStart_5324028 := by decide
  rcases family_descends (prefixWord ++ tailWord_5324028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5324061 : List Nat := [1, 4, 2, 3, 1, 1, 1, 1, 1, 8]
def baseStart_5324061 : Nat := 118140960795 + 5324061 * 2 ^ 59
def prefixEnd_5324061 : Nat := 4983230072969 + 3 ^ 40 * 5324061 * 2
def baseEnd_5324061 : Nat := 911267442285733106850865

theorem tailTrace_5324061 : CollatzResearch.WordTrace tailWord_5324061 prefixEnd_5324061 911267442285733106850865 := by
  unfold tailWord_5324061
  simp only [CollatzResearch.WordTrace]
  refine ⟨194184457564843749072652037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129456305043229166048434691 194184457564843749072652037)
  ·
    refine ⟨36409585793408202951122257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 194184457564843749072652037 36409585793408202951122257)
    ·
      refine ⟨27307189345056152213341693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36409585793408202951122257 27307189345056152213341693)
      ·
        refine ⟨10240196004396057080003135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27307189345056152213341693 10240196004396057080003135)
        ·
          refine ⟨15360294006594085620004703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10240196004396057080003135 15360294006594085620004703)
          ·
            refine ⟨23040441009891128430007055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15360294006594085620004703 23040441009891128430007055)
            ·
              refine ⟨34560661514836692645010583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23040441009891128430007055 34560661514836692645010583)
              ·
                refine ⟨51840992272255038967515875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34560661514836692645010583 51840992272255038967515875)
                ·
                  refine ⟨77761488408382558451273813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51840992272255038967515875 77761488408382558451273813)
                  ·
                    refine ⟨911267442285733106850865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 77761488408382558451273813 911267442285733106850865)
                    ·
                      rfl

theorem cell23_5324061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 1, 1, 8].length) (baseStart_5324061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5324061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5324061 prefixEnd_5324061 := by exact prefixLift 5324061
  have htrace : WordTrace (prefixWord ++ tailWord_5324061) baseStart_5324061 baseEnd_5324061 := by
    simpa [prefixWord, tailWord_5324061, baseEnd_5324061] using wordTrace_append hprefix tailTrace_5324061
  have hstable : (prefixWord ++ tailWord_5324061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5324061).length < 2 ^ (prefixWord ++ tailWord_5324061).sum := by decide
  have hdescent : baseEnd_5324061 < baseStart_5324061 := by decide
  rcases family_descends (prefixWord ++ tailWord_5324061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5324062 : List Nat := [4, 3, 2, 1, 2, 1, 2, 1, 1, 3, 3]
def baseStart_5324062 : Nat := 118140960795 + 5324062 * 2 ^ 59
def prefixEnd_5324062 : Nat := 4983230072969 + 3 ^ 40 * 5324062 * 2
def baseEnd_5324062 : Nat := 2733802840337853816640091

theorem tailTrace_5324062 : CollatzResearch.WordTrace tailWord_5324062 prefixEnd_5324062 2733802840337853816640091 := by
  unfold tailWord_5324062
  simp only [CollatzResearch.WordTrace]
  refine ⟨24273061754730015780429805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129456329358560084162292293 24273061754730015780429805)
  ·
    refine ⟨9102398158023755917661177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24273061754730015780429805 9102398158023755917661177)
    ·
      refine ⟨6826798618517816938245883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9102398158023755917661177 6826798618517816938245883)
      ·
        refine ⟨10240197927776725407368825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6826798618517816938245883 10240197927776725407368825)
        ·
          refine ⟨7680148445832544055526619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10240197927776725407368825 7680148445832544055526619)
          ·
            refine ⟨11520222668748816083289929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7680148445832544055526619 11520222668748816083289929)
            ·
              refine ⟨8640167001561612062467447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11520222668748816083289929 8640167001561612062467447)
              ·
                refine ⟨12960250502342418093701171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8640167001561612062467447 12960250502342418093701171)
                ·
                  refine ⟨19440375753513627140551757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12960250502342418093701171 19440375753513627140551757)
                  ·
                    refine ⟨7290140907567610177706909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19440375753513627140551757 7290140907567610177706909)
                    ·
                      refine ⟨2733802840337853816640091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7290140907567610177706909 2733802840337853816640091)
                      ·
                        rfl

theorem cell23_5324062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_5324062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5324062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5324062 prefixEnd_5324062 := by exact prefixLift 5324062
  have htrace : WordTrace (prefixWord ++ tailWord_5324062) baseStart_5324062 baseEnd_5324062 := by
    simpa [prefixWord, tailWord_5324062, baseEnd_5324062] using wordTrace_append hprefix tailTrace_5324062
  have hstable : (prefixWord ++ tailWord_5324062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5324062).length < 2 ^ (prefixWord ++ tailWord_5324062).sum := by decide
  have hdescent : baseEnd_5324062 < baseStart_5324062 := by decide
  rcases family_descends (prefixWord ++ tailWord_5324062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5324089 : List Nat := [1, 2, 1, 6, 2, 2, 2, 1, 1, 3, 2]
def baseStart_5324089 : Nat := 118140960795 + 5324089 * 2 ^ 59
def prefixEnd_5324089 : Nat := 4983230072969 + 3 ^ 40 * 5324089 * 2
def baseEnd_5324089 : Nat := 2733816704315525211002467

theorem tailTrace_5324089 : CollatzResearch.WordTrace tailWord_5324089 prefixEnd_5324089 2733816704315525211002467 := by
  unfold tailWord_5324089
  simp only [CollatzResearch.WordTrace]
  refine ⟨194185478808742309854671321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129456985872494873236447547 194185478808742309854671321)
  ·
    refine ⟨145639109106556732391003491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194185478808742309854671321 145639109106556732391003491)
    ·
      refine ⟨218458663659835098586505237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145639109106556732391003491 218458663659835098586505237)
      ·
        refine ⟨10240249859054770246242433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 218458663659835098586505237 10240249859054770246242433)
        ·
          refine ⟨7680187394291077684681825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10240249859054770246242433 7680187394291077684681825)
          ·
            refine ⟨5760140545718308263511369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7680187394291077684681825 5760140545718308263511369)
            ·
              refine ⟨4320105409288731197633527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5760140545718308263511369 4320105409288731197633527)
              ·
                refine ⟨6480158113933096796450291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4320105409288731197633527 6480158113933096796450291)
                ·
                  refine ⟨9720237170899645194675437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6480158113933096796450291 9720237170899645194675437)
                  ·
                    refine ⟨3645088939087366948003289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9720237170899645194675437 3645088939087366948003289)
                    ·
                      refine ⟨2733816704315525211002467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3645088939087366948003289 2733816704315525211002467)
                      ·
                        rfl

theorem cell23_5324089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 2, 1, 1, 3, 2].length) (baseStart_5324089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5324089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5324089 prefixEnd_5324089 := by exact prefixLift 5324089
  have htrace : WordTrace (prefixWord ++ tailWord_5324089) baseStart_5324089 baseEnd_5324089 := by
    simpa [prefixWord, tailWord_5324089, baseEnd_5324089] using wordTrace_append hprefix tailTrace_5324089
  have hstable : (prefixWord ++ tailWord_5324089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5324089).length < 2 ^ (prefixWord ++ tailWord_5324089).sum := by decide
  have hdescent : baseEnd_5324089 < baseStart_5324089 := by decide
  rcases family_descends (prefixWord ++ tailWord_5324089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5324108 : List Nat := [2, 2, 1, 3, 2, 2, 2, 4, 5]
def baseStart_5324108 : Nat := 118140960795 + 5324108 * 2 ^ 59
def prefixEnd_5324108 : Nat := 4983230072969 + 3 ^ 40 * 5324108 * 2
def baseEnd_5324108 : Nat := 303758495605328959629431

theorem tailTrace_5324108 : CollatzResearch.WordTrace tailWord_5324108 prefixEnd_5324108 303758495605328959629431 := by
  unfold tailWord_5324108
  simp only [CollatzResearch.WordTrace]
  refine ⟨97093085897836738049806489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129457447863782317399741985 97093085897836738049806489)
  ·
    refine ⟨72819814423377553537354867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97093085897836738049806489 72819814423377553537354867)
    ·
      refine ⟨109229721635066330306032301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72819814423377553537354867 109229721635066330306032301)
      ·
        refine ⟨40961145613149873864762113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109229721635066330306032301 40961145613149873864762113)
        ·
          refine ⟨30720859209862405398571585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40961145613149873864762113 30720859209862405398571585)
          ·
            refine ⟨23040644407396804048928689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30720859209862405398571585 23040644407396804048928689)
            ·
              refine ⟨17280483305547603036696517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23040644407396804048928689 17280483305547603036696517)
              ·
                refine ⟨3240090619790175569380597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17280483305547603036696517 3240090619790175569380597)
                ·
                  refine ⟨303758495605328959629431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3240090619790175569380597 303758495605328959629431)
                  ·
                    rfl

theorem cell23_5324108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 4, 5].length) (baseStart_5324108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5324108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5324108 prefixEnd_5324108 := by exact prefixLift 5324108
  have htrace : WordTrace (prefixWord ++ tailWord_5324108) baseStart_5324108 baseEnd_5324108 := by
    simpa [prefixWord, tailWord_5324108, baseEnd_5324108] using wordTrace_append hprefix tailTrace_5324108
  have hstable : (prefixWord ++ tailWord_5324108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5324108).length < 2 ^ (prefixWord ++ tailWord_5324108).sum := by decide
  have hdescent : baseEnd_5324108 < baseStart_5324108 := by decide
  rcases family_descends (prefixWord ++ tailWord_5324108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5324208 : List Nat := [2, 1, 1, 1, 2, 1, 1, 3, 7, 1, 3]
def baseStart_5324208 : Nat := 118140960795 + 5324208 * 2 ^ 59
def prefixEnd_5324208 : Nat := 4983230072969 + 3 ^ 40 * 5324208 * 2
def baseEnd_5324208 : Nat := 2733877808513410245414419

theorem tailTrace_5324208 : CollatzResearch.WordTrace tailWord_5324208 prefixEnd_5324208 2733877808513410245414419 := by
  unfold tailWord_5324208
  simp only [CollatzResearch.WordTrace]
  refine ⟨97094909547655596589126639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129459879396874128785502185 97094909547655596589126639)
  ·
    refine ⟨145642364321483394883689959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97094909547655596589126639 145642364321483394883689959)
    ·
      refine ⟨218463546482225092325534939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145642364321483394883689959 218463546482225092325534939)
      ·
        refine ⟨327695319723337638488302409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218463546482225092325534939 327695319723337638488302409)
        ·
          refine ⟨245771489792503228866226807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 327695319723337638488302409 245771489792503228866226807)
          ·
            refine ⟨368657234688754843299340211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 245771489792503228866226807 368657234688754843299340211)
            ·
              refine ⟨552985852033132264949010317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 368657234688754843299340211 552985852033132264949010317)
              ·
                refine ⟨207369694512424599355878869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 552985852033132264949010317 207369694512424599355878869)
                ·
                  refine ⟨4860227215134951547403411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 207369694512424599355878869 4860227215134951547403411)
                  ·
                    refine ⟨7290340822702427321105117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4860227215134951547403411 7290340822702427321105117)
                    ·
                      refine ⟨2733877808513410245414419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7290340822702427321105117 2733877808513410245414419)
                      ·
                        rfl

theorem cell23_5324208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 7, 1, 3].length) (baseStart_5324208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5324208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5324208 prefixEnd_5324208 := by exact prefixLift 5324208
  have htrace : WordTrace (prefixWord ++ tailWord_5324208) baseStart_5324208 baseEnd_5324208 := by
    simpa [prefixWord, tailWord_5324208, baseEnd_5324208] using wordTrace_append hprefix tailTrace_5324208
  have hstable : (prefixWord ++ tailWord_5324208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5324208).length < 2 ^ (prefixWord ++ tailWord_5324208).sum := by decide
  have hdescent : baseEnd_5324208 < baseStart_5324208 := by decide
  rcases family_descends (prefixWord ++ tailWord_5324208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5324218 : List Nat := [3, 1, 1, 1, 2, 1, 1, 1, 5, 5, 2]
def baseStart_5324218 : Nat := 118140960795 + 5324218 * 2 ^ 59
def prefixEnd_5324218 : Nat := 4983230072969 + 3 ^ 40 * 5324218 * 2
def baseEnd_5324218 : Nat := 2733882943319955206289373

theorem tailTrace_5324218 : CollatzResearch.WordTrace tailWord_5324218 prefixEnd_5324218 2733882943319955206289373 := by
  unfold tailWord_5324218
  simp only [CollatzResearch.WordTrace]
  refine ⟨48547545956318741221529327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129460122550183309924078205 48547545956318741221529327)
  ·
    refine ⟨72821318934478111832293991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48547545956318741221529327 72821318934478111832293991)
    ·
      refine ⟨109231978401717167748440987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72821318934478111832293991 109231978401717167748440987)
      ·
        refine ⟨163847967602575751622661481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109231978401717167748440987 163847967602575751622661481)
        ·
          refine ⟨122885975701931813716996111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163847967602575751622661481 122885975701931813716996111)
          ·
            refine ⟨184328963552897720575494167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122885975701931813716996111 184328963552897720575494167)
            ·
              refine ⟨276493445329346580863241251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 184328963552897720575494167 276493445329346580863241251)
              ·
                refine ⟨414740167994019871294861877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 276493445329346580863241251 414740167994019871294861877)
                ·
                  refine ⟨38881890749439362933893301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 414740167994019871294861877 38881890749439362933893301)
                  ·
                    refine ⟨3645177257759940275052497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38881890749439362933893301 3645177257759940275052497)
                    ·
                      refine ⟨2733882943319955206289373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3645177257759940275052497 2733882943319955206289373)
                      ·
                        rfl

theorem cell23_5324218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 5, 5, 2].length) (baseStart_5324218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5324218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5324218 prefixEnd_5324218 := by exact prefixLift 5324218
  have htrace : WordTrace (prefixWord ++ tailWord_5324218) baseStart_5324218 baseEnd_5324218 := by
    simpa [prefixWord, tailWord_5324218, baseEnd_5324218] using wordTrace_append hprefix tailTrace_5324218
  have hstable : (prefixWord ++ tailWord_5324218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5324218).length < 2 ^ (prefixWord ++ tailWord_5324218).sum := by decide
  have hdescent : baseEnd_5324218 < baseStart_5324218 := by decide
  rcases family_descends (prefixWord ++ tailWord_5324218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5324248 : List Nat := [2, 1, 2, 2, 2, 1, 4, 1, 3, 1, 4]
def baseStart_5324248 : Nat := 118140960795 + 5324248 * 2 ^ 59
def prefixEnd_5324248 : Nat := 4983230072969 + 3 ^ 40 * 5324248 * 2
def baseEnd_5324248 : Nat := 2733898347739590088914235

theorem tailTrace_5324248 : CollatzResearch.WordTrace tailWord_5324248 prefixEnd_5324248 2733898347739590088914235 := by
  unfold tailWord_5324248
  simp only [CollatzResearch.WordTrace]
  refine ⟨97095639007583140004854699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129460852010110853339806265 97095639007583140004854699)
  ·
    refine ⟨145643458511374710007282049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97095639007583140004854699 145643458511374710007282049)
    ·
      refine ⟨109232593883531032505461537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145643458511374710007282049 109232593883531032505461537)
      ·
        refine ⟨81924445412648274379096153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109232593883531032505461537 81924445412648274379096153)
        ·
          refine ⟨61443334059486205784322115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81924445412648274379096153 61443334059486205784322115)
          ·
            refine ⟨92165001089229308676483173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61443334059486205784322115 92165001089229308676483173)
            ·
              refine ⟨17280937704230495376840595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 92165001089229308676483173 17280937704230495376840595)
              ·
                refine ⟨25921406556345743065260893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17280937704230495376840595 25921406556345743065260893)
                ·
                  refine ⟨9720527458629653649472835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25921406556345743065260893 9720527458629653649472835)
                  ·
                    refine ⟨14580791187944480474209253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9720527458629653649472835 14580791187944480474209253)
                    ·
                      refine ⟨2733898347739590088914235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14580791187944480474209253 2733898347739590088914235)
                      ·
                        rfl

theorem cell23_5324248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 1, 3, 1, 4].length) (baseStart_5324248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5324248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5324248 prefixEnd_5324248 := by exact prefixLift 5324248
  have htrace : WordTrace (prefixWord ++ tailWord_5324248) baseStart_5324248 baseEnd_5324248 := by
    simpa [prefixWord, tailWord_5324248, baseEnd_5324248] using wordTrace_append hprefix tailTrace_5324248
  have hstable : (prefixWord ++ tailWord_5324248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5324248).length < 2 ^ (prefixWord ++ tailWord_5324248).sum := by decide
  have hdescent : baseEnd_5324248 < baseStart_5324248 := by decide
  rcases family_descends (prefixWord ++ tailWord_5324248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5324259 : List Nat := [1, 1, 1, 6, 2, 2, 2, 3, 1, 1, 3]
def baseStart_5324259 : Nat := 118140960795 + 5324259 * 2 ^ 59
def prefixEnd_5324259 : Nat := 4983230072969 + 3 ^ 40 * 5324259 * 2
def baseEnd_5324259 : Nat := 2733903996026789545876685

theorem tailTrace_5324259 : CollatzResearch.WordTrace tailWord_5324259 prefixEnd_5324259 2733903996026789545876685 := by
  unfold tailWord_5324259
  simp only [CollatzResearch.WordTrace]
  refine ⟨194191679218126428888359831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129461119478750952592239887 194191679218126428888359831)
  ·
    refine ⟨291287518827189643332539747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194191679218126428888359831 291287518827189643332539747)
    ·
      refine ⟨436931278240784464998809621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 291287518827189643332539747 436931278240784464998809621)
      ·
        refine ⟨20481153667536771796819201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 436931278240784464998809621 20481153667536771796819201)
        ·
          refine ⟨15360865250652578847614401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20481153667536771796819201 15360865250652578847614401)
          ·
            refine ⟨11520648937989434135710801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15360865250652578847614401 11520648937989434135710801)
            ·
              refine ⟨8640486703492075601783101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11520648937989434135710801 8640486703492075601783101)
              ·
                refine ⟨3240182513809528350668663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8640486703492075601783101 3240182513809528350668663)
                ·
                  refine ⟨4860273770714292526002995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3240182513809528350668663 4860273770714292526002995)
                  ·
                    refine ⟨7290410656071438789004493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4860273770714292526002995 7290410656071438789004493)
                    ·
                      refine ⟨2733903996026789545876685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7290410656071438789004493 2733903996026789545876685)
                      ·
                        rfl

theorem cell23_5324259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 3, 1, 1, 3].length) (baseStart_5324259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5324259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5324259 prefixEnd_5324259 := by exact prefixLift 5324259
  have htrace : WordTrace (prefixWord ++ tailWord_5324259) baseStart_5324259 baseEnd_5324259 := by
    simpa [prefixWord, tailWord_5324259, baseEnd_5324259] using wordTrace_append hprefix tailTrace_5324259
  have hstable : (prefixWord ++ tailWord_5324259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5324259).length < 2 ^ (prefixWord ++ tailWord_5324259).sum := by decide
  have hdescent : baseEnd_5324259 < baseStart_5324259 := by decide
  rcases family_descends (prefixWord ++ tailWord_5324259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5324268 : List Nat := [2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 3]
def baseStart_5324268 : Nat := 118140960795 + 5324268 * 2 ^ 59
def prefixEnd_5324268 : Nat := 4983230072969 + 3 ^ 40 * 5324268 * 2
def baseEnd_5324268 : Nat := 2733908617352680010664143

theorem tailTrace_5324268 : CollatzResearch.WordTrace tailWord_5324268 prefixEnd_5324268 2733908617352680010664143 := by
  unfold tailWord_5324268
  simp only [CollatzResearch.WordTrace]
  refine ⟨97096003737546911712718729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129461338316729215616958305 97096003737546911712718729)
  ·
    refine ⟨72822002803160183784539047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97096003737546911712718729 72822002803160183784539047)
    ·
      refine ⟨109233004204740275676808571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72822002803160183784539047 109233004204740275676808571)
      ·
        refine ⟨163849506307110413515212857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109233004204740275676808571 163849506307110413515212857)
        ·
          refine ⟨122887129730332810136409643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163849506307110413515212857 122887129730332810136409643)
          ·
            refine ⟨184330694595499215204614465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122887129730332810136409643 184330694595499215204614465)
            ·
              refine ⟨138248020946624411403460849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 184330694595499215204614465 138248020946624411403460849)
              ·
                refine ⟨103686015709968308552595637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 138248020946624411403460849 103686015709968308552595637)
                ·
                  refine ⟨9720563972809528926805841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 103686015709968308552595637 9720563972809528926805841)
                  ·
                    refine ⟨7290422979607146695104381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9720563972809528926805841 7290422979607146695104381)
                    ·
                      refine ⟨2733908617352680010664143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7290422979607146695104381 2733908617352680010664143)
                      ·
                        rfl

theorem cell23_5324268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 3].length) (baseStart_5324268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5324268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5324268 prefixEnd_5324268 := by exact prefixLift 5324268
  have htrace : WordTrace (prefixWord ++ tailWord_5324268) baseStart_5324268 baseEnd_5324268 := by
    simpa [prefixWord, tailWord_5324268, baseEnd_5324268] using wordTrace_append hprefix tailTrace_5324268
  have hstable : (prefixWord ++ tailWord_5324268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5324268).length < 2 ^ (prefixWord ++ tailWord_5324268).sum := by decide
  have hdescent : baseEnd_5324268 < baseStart_5324268 := by decide
  rcases family_descends (prefixWord ++ tailWord_5324268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5324281 : List Nat := [1, 2, 1, 3, 1, 2, 1, 1, 2, 2, 7]
def baseStart_5324281 : Nat := 118140960795 + 5324281 * 2 ^ 59
def prefixEnd_5324281 : Nat := 4983230072969 + 3 ^ 40 * 5324281 * 2
def baseEnd_5324281 : Nat := 2733915292601188459801583

theorem tailTrace_5324281 : CollatzResearch.WordTrace tailWord_5324281 prefixEnd_5324281 2733915292601188459801583 := by
  unfold tailWord_5324281
  simp only [CollatzResearch.WordTrace]
  refine ⟨194192481624046726645660697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129461654416031151097107131 194192481624046726645660697)
  ·
    refine ⟨145644361218035044984245523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194192481624046726645660697 145644361218035044984245523)
    ·
      refine ⟨218466541827052567476368285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145644361218035044984245523 218466541827052567476368285)
      ·
        refine ⟨81924953185144712803638107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 218466541827052567476368285 81924953185144712803638107)
        ·
          refine ⟨122887429777717069205457161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81924953185144712803638107 122887429777717069205457161)
          ·
            refine ⟨92165572333287801904092871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122887429777717069205457161 92165572333287801904092871)
            ·
              refine ⟨138248358499931702856139307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92165572333287801904092871 138248358499931702856139307)
              ·
                refine ⟨207372537749897554284208961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 138248358499931702856139307 207372537749897554284208961)
                ·
                  refine ⟨155529403312423165713156721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 207372537749897554284208961 155529403312423165713156721)
                  ·
                    refine ⟨116647052484317374284867541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 155529403312423165713156721 116647052484317374284867541)
                    ·
                      refine ⟨2733915292601188459801583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 116647052484317374284867541 2733915292601188459801583)
                      ·
                        rfl

theorem cell23_5324281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 2, 7].length) (baseStart_5324281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5324281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5324281 prefixEnd_5324281 := by exact prefixLift 5324281
  have htrace : WordTrace (prefixWord ++ tailWord_5324281) baseStart_5324281 baseEnd_5324281 := by
    simpa [prefixWord, tailWord_5324281, baseEnd_5324281] using wordTrace_append hprefix tailTrace_5324281
  have hstable : (prefixWord ++ tailWord_5324281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5324281).length < 2 ^ (prefixWord ++ tailWord_5324281).sum := by decide
  have hdescent : baseEnd_5324281 < baseStart_5324281 := by decide
  rcases family_descends (prefixWord ++ tailWord_5324281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5324282 : List Nat := [3, 1, 1, 1, 1, 2, 6, 1, 3, 2, 2]
def baseStart_5324282 : Nat := 118140960795 + 5324282 * 2 ^ 59
def prefixEnd_5324282 : Nat := 4983230072969 + 3 ^ 40 * 5324282 * 2
def baseEnd_5324282 : Nat := 2733915806081842955889079

theorem tailTrace_5324282 : CollatzResearch.WordTrace tailWord_5324282 prefixEnd_5324282 2733915806081842955889079 := by
  unfold tailWord_5324282
  simp only [CollatzResearch.WordTrace]
  refine ⟨48548129524260775954111775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129461678731362069210964733 48548129524260775954111775)
  ·
    refine ⟨72822194286391163931167663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48548129524260775954111775 72822194286391163931167663)
    ·
      refine ⟨109233291429586745896751495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72822194286391163931167663 109233291429586745896751495)
      ·
        refine ⟨163849937144380118845127243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109233291429586745896751495 163849937144380118845127243)
        ·
          refine ⟨245774905716570178267690865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163849937144380118845127243 245774905716570178267690865)
          ·
            refine ⟨184331179287427633700768149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 245774905716570178267690865 184331179287427633700768149)
            ·
              refine ⟨8640524029098170329723507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 184331179287427633700768149 8640524029098170329723507)
              ·
                refine ⟨12960786043647255494585261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8640524029098170329723507 12960786043647255494585261)
                ·
                  refine ⟨4860294766367720810469473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12960786043647255494585261 4860294766367720810469473)
                  ·
                    refine ⟨3645221074775790607852105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4860294766367720810469473 3645221074775790607852105)
                    ·
                      refine ⟨2733915806081842955889079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3645221074775790607852105 2733915806081842955889079)
                      ·
                        rfl

theorem cell23_5324282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 1, 3, 2, 2].length) (baseStart_5324282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5324282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5324282 prefixEnd_5324282 := by exact prefixLift 5324282
  have htrace : WordTrace (prefixWord ++ tailWord_5324282) baseStart_5324282 baseEnd_5324282 := by
    simpa [prefixWord, tailWord_5324282, baseEnd_5324282] using wordTrace_append hprefix tailTrace_5324282
  have hstable : (prefixWord ++ tailWord_5324282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5324282).length < 2 ^ (prefixWord ++ tailWord_5324282).sum := by decide
  have hdescent : baseEnd_5324282 < baseStart_5324282 := by decide
  rcases family_descends (prefixWord ++ tailWord_5324282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5324291 : List Nat := [1, 1, 1, 3, 2, 1, 2, 1, 1, 4, 6]
def baseStart_5324291 : Nat := 118140960795 + 5324291 * 2 ^ 59
def prefixEnd_5324291 : Nat := 4983230072969 + 3 ^ 40 * 5324291 * 2
def baseEnd_5324291 : Nat := 2733920427407733420676537

theorem tailTrace_5324291 : CollatzResearch.WordTrace tailWord_5324291 prefixEnd_5324291 2733920427407733420676537 := by
  unfold tailWord_5324291
  simp only [CollatzResearch.WordTrace]
  refine ⟨194192846354010498353524727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129461897569340332235683151 194192846354010498353524727)
  ·
    refine ⟨291289269531015747530287091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194192846354010498353524727 291289269531015747530287091)
    ·
      refine ⟨436933904296523621295430637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 291289269531015747530287091 436933904296523621295430637)
      ·
        refine ⟨163850214111196357985786489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 436933904296523621295430637 163850214111196357985786489)
        ·
          refine ⟨122887660583397268489339867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163850214111196357985786489 122887660583397268489339867)
          ·
            refine ⟨184331490875095902734009801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122887660583397268489339867 184331490875095902734009801)
            ·
              refine ⟨138248618156321927050507351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 184331490875095902734009801 138248618156321927050507351)
              ·
                refine ⟨207372927234482890575761027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 138248618156321927050507351 207372927234482890575761027)
                ·
                  refine ⟨311059390851724335863641541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 207372927234482890575761027 311059390851724335863641541)
                  ·
                    refine ⟨58323635784698312974432789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 311059390851724335863641541 58323635784698312974432789)
                    ·
                      refine ⟨2733920427407733420676537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58323635784698312974432789 2733920427407733420676537)
                      ·
                        rfl

theorem cell23_5324291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 4, 6].length) (baseStart_5324291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5324291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5324291 prefixEnd_5324291 := by exact prefixLift 5324291
  have htrace : WordTrace (prefixWord ++ tailWord_5324291) baseStart_5324291 baseEnd_5324291 := by
    simpa [prefixWord, tailWord_5324291, baseEnd_5324291] using wordTrace_append hprefix tailTrace_5324291
  have hstable : (prefixWord ++ tailWord_5324291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5324291).length < 2 ^ (prefixWord ++ tailWord_5324291).sum := by decide
  have hdescent : baseEnd_5324291 < baseStart_5324291 := by decide
  rcases family_descends (prefixWord ++ tailWord_5324291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5324292 : List Nat := [2, 3, 2, 3, 2, 2, 1, 1, 1, 6]
def baseStart_5324292 : Nat := 118140960795 + 5324292 * 2 ^ 59
def prefixEnd_5324292 : Nat := 4983230072969 + 3 ^ 40 * 5324292 * 2
def baseEnd_5324292 : Nat := 911306980296129305588011

theorem tailTrace_5324292 : CollatzResearch.WordTrace tailWord_5324292 prefixEnd_5324292 911306980296129305588011 := by
  unfold tailWord_5324292
  simp only [CollatzResearch.WordTrace]
  refine ⟨97096441413503437762155565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129461921884671250349540753 97096441413503437762155565)
  ·
    refine ⟨36411165530063789160808337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97096441413503437762155565 36411165530063789160808337)
    ·
      refine ⟨27308374147547841870606253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36411165530063789160808337 27308374147547841870606253)
      ·
        refine ⟨10240640305330440701477345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27308374147547841870606253 10240640305330440701477345)
        ·
          refine ⟨7680480228997830526108009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10240640305330440701477345 7680480228997830526108009)
          ·
            refine ⟨5760360171748372894581007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7680480228997830526108009 5760360171748372894581007)
            ·
              refine ⟨8640540257622559341871511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5760360171748372894581007 8640540257622559341871511)
              ·
                refine ⟨12960810386433839012807267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8640540257622559341871511 12960810386433839012807267)
                ·
                  refine ⟨19441215579650758519210901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12960810386433839012807267 19441215579650758519210901)
                  ·
                    refine ⟨911306980296129305588011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19441215579650758519210901 911306980296129305588011)
                    ·
                      rfl

theorem cell23_5324292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 1, 1, 6].length) (baseStart_5324292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5324292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5324292 prefixEnd_5324292 := by exact prefixLift 5324292
  have htrace : WordTrace (prefixWord ++ tailWord_5324292) baseStart_5324292 baseEnd_5324292 := by
    simpa [prefixWord, tailWord_5324292, baseEnd_5324292] using wordTrace_append hprefix tailTrace_5324292
  have hstable : (prefixWord ++ tailWord_5324292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5324292).length < 2 ^ (prefixWord ++ tailWord_5324292).sum := by decide
  have hdescent : baseEnd_5324292 < baseStart_5324292 := by decide
  rcases family_descends (prefixWord ++ tailWord_5324292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5324295 : List Nat := [1, 1, 4, 3, 2, 1, 3, 1, 1, 2, 4]
def baseStart_5324295 : Nat := 118140960795 + 5324295 * 2 ^ 59
def prefixEnd_5324295 : Nat := 4983230072969 + 3 ^ 40 * 5324295 * 2
def baseEnd_5324295 : Nat := 2733922481330351405026519

theorem tailTrace_5324295 : CollatzResearch.WordTrace tailWord_5324295 prefixEnd_5324295 2733922481330351405026519 := by
  unfold tailWord_5324295
  simp only [CollatzResearch.WordTrace]
  refine ⟨194192992245996007036670339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129461994830664004691113559 194192992245996007036670339)
  ·
    refine ⟨291289488368994010555005509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194192992245996007036670339 291289488368994010555005509)
    ·
      refine ⟨54616779069186376979063533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 291289488368994010555005509 54616779069186376979063533)
      ·
        refine ⟨20481292150944891367148825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54616779069186376979063533 20481292150944891367148825)
        ·
          refine ⟨15360969113208668525361619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20481292150944891367148825 15360969113208668525361619)
          ·
            refine ⟨23041453669813002788042429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15360969113208668525361619 23041453669813002788042429)
            ·
              refine ⟨8640545126179876045515911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23041453669813002788042429 8640545126179876045515911)
              ·
                refine ⟨12960817689269814068273867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8640545126179876045515911 12960817689269814068273867)
                ·
                  refine ⟨19441226533904721102410801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12960817689269814068273867 19441226533904721102410801)
                  ·
                    refine ⟨14580919900428540826808101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19441226533904721102410801 14580919900428540826808101)
                    ·
                      refine ⟨2733922481330351405026519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14580919900428540826808101 2733922481330351405026519)
                      ·
                        rfl

theorem cell23_5324295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 1, 1, 2, 4].length) (baseStart_5324295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5324295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5324295 prefixEnd_5324295 := by exact prefixLift 5324295
  have htrace : WordTrace (prefixWord ++ tailWord_5324295) baseStart_5324295 baseEnd_5324295 := by
    simpa [prefixWord, tailWord_5324295, baseEnd_5324295] using wordTrace_append hprefix tailTrace_5324295
  have hstable : (prefixWord ++ tailWord_5324295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5324295).length < 2 ^ (prefixWord ++ tailWord_5324295).sum := by decide
  have hdescent : baseEnd_5324295 < baseStart_5324295 := by decide
  rcases family_descends (prefixWord ++ tailWord_5324295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5324325 : List Nat := [1, 3, 1, 2, 2, 1, 1, 2, 5, 3, 2]
def baseStart_5324325 : Nat := 118140960795 + 5324325 * 2 ^ 59
def prefixEnd_5324325 : Nat := 4983230072969 + 3 ^ 40 * 5324325 * 2
def baseEnd_5324325 : Nat := 2733937885749986287651381

theorem tailTrace_5324325 : CollatzResearch.WordTrace tailWord_5324325 prefixEnd_5324325 2733937885749986287651381 := by
  unfold tailWord_5324325
  simp only [CollatzResearch.WordTrace]
  refine ⟨194194086435887322160262429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129462724290591548106841619 194194086435887322160262429)
  ·
    refine ⟨72822782413457745810098411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 194194086435887322160262429 72822782413457745810098411)
    ·
      refine ⟨109234173620186618715147617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72822782413457745810098411 109234173620186618715147617)
      ·
        refine ⟨81925630215139964036360713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109234173620186618715147617 81925630215139964036360713)
        ·
          refine ⟨61444222661354973027270535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81925630215139964036360713 61444222661354973027270535)
          ·
            refine ⟨92166333992032459540905803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61444222661354973027270535 92166333992032459540905803)
            ·
              refine ⟨138249500988048689311358705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92166333992032459540905803 138249500988048689311358705)
              ·
                refine ⟨103687125741036516983519029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 138249500988048689311358705 103687125741036516983519029)
                ·
                  refine ⟨9720668038222173467204909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 103687125741036516983519029 9720668038222173467204909)
                  ·
                    refine ⟨3645250514333315050201841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9720668038222173467204909 3645250514333315050201841)
                    ·
                      refine ⟨2733937885749986287651381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3645250514333315050201841 2733937885749986287651381)
                      ·
                        rfl

theorem cell23_5324325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 5, 3, 2].length) (baseStart_5324325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5324325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5324325 prefixEnd_5324325 := by exact prefixLift 5324325
  have htrace : WordTrace (prefixWord ++ tailWord_5324325) baseStart_5324325 baseEnd_5324325 := by
    simpa [prefixWord, tailWord_5324325, baseEnd_5324325] using wordTrace_append hprefix tailTrace_5324325
  have hstable : (prefixWord ++ tailWord_5324325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5324325).length < 2 ^ (prefixWord ++ tailWord_5324325).sum := by decide
  have hdescent : baseEnd_5324325 < baseStart_5324325 := by decide
  rcases family_descends (prefixWord ++ tailWord_5324325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5324338 : List Nat := [3, 2, 1, 1, 2, 1, 1, 3, 2, 3, 4]
def baseStart_5324338 : Nat := 118140960795 + 5324338 * 2 ^ 59
def prefixEnd_5324338 : Nat := 4983230072969 + 3 ^ 40 * 5324338 * 2
def baseEnd_5324338 : Nat := 2733944560998494736788821

theorem tailTrace_5324338 : CollatzResearch.WordTrace tailWord_5324338 prefixEnd_5324338 2733944560998494736788821 := by
  unfold tailWord_5324338
  simp only [CollatzResearch.WordTrace]
  refine ⟨48548640146210056345121417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129463040389893483586990445 48548640146210056345121417)
  ·
    refine ⟨36411480109657542258841063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48548640146210056345121417 36411480109657542258841063)
    ·
      refine ⟨54617220164486313388261595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36411480109657542258841063 54617220164486313388261595)
      ·
        refine ⟨81925830246729470082392393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54617220164486313388261595 81925830246729470082392393)
        ·
          refine ⟨61444372685047102561794295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81925830246729470082392393 61444372685047102561794295)
          ·
            refine ⟨92166559027570653842691443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61444372685047102561794295 92166559027570653842691443)
            ·
              refine ⟨138249838541355980764037165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92166559027570653842691443 138249838541355980764037165)
              ·
                refine ⟨51843689453008492786513937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 138249838541355980764037165 51843689453008492786513937)
                ·
                  refine ⟨38882767089756369589885453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51843689453008492786513937 38882767089756369589885453)
                  ·
                    refine ⟨14581037658658638596207045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38882767089756369589885453 14581037658658638596207045)
                    ·
                      refine ⟨2733944560998494736788821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14581037658658638596207045 2733944560998494736788821)
                      ·
                        rfl

theorem cell23_5324338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 3, 2, 3, 4].length) (baseStart_5324338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5324338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5324338 prefixEnd_5324338 := by exact prefixLift 5324338
  have htrace : WordTrace (prefixWord ++ tailWord_5324338) baseStart_5324338 baseEnd_5324338 := by
    simpa [prefixWord, tailWord_5324338, baseEnd_5324338] using wordTrace_append hprefix tailTrace_5324338
  have hstable : (prefixWord ++ tailWord_5324338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5324338).length < 2 ^ (prefixWord ++ tailWord_5324338).sum := by decide
  have hdescent : baseEnd_5324338 < baseStart_5324338 := by decide
  rcases family_descends (prefixWord ++ tailWord_5324338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5324349 : List Nat := [1, 4, 1, 3, 3, 1, 1, 3, 2, 1, 3]
def baseStart_5324349 : Nat := 118140960795 + 5324349 * 2 ^ 59
def prefixEnd_5324349 : Nat := 4983230072969 + 3 ^ 40 * 5324349 * 2
def baseEnd_5324349 : Nat := 2733950209285694193751271

theorem tailTrace_5324349 : CollatzResearch.WordTrace tailWord_5324349 prefixEnd_5324349 2733950209285694193751271 := by
  unfold tailWord_5324349
  simp only [CollatzResearch.WordTrace]
  refine ⟨194194961787800374259136101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129463307858533582839424067 194194961787800374259136101)
  ·
    refine ⟨36411555335212570173588019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 194194961787800374259136101 36411555335212570173588019)
    ·
      refine ⟨54617333002818855260382029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36411555335212570173588019 54617333002818855260382029)
      ·
        refine ⟨20481499876057070722643261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54617333002818855260382029 20481499876057070722643261)
        ·
          refine ⟨7680562453521401520991223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20481499876057070722643261 7680562453521401520991223)
          ·
            refine ⟨11520843680282102281486835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7680562453521401520991223 11520843680282102281486835)
            ·
              refine ⟨17281265520423153422230253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11520843680282102281486835 17281265520423153422230253)
              ·
                refine ⟨6480474570158682533336345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17281265520423153422230253 6480474570158682533336345)
                ·
                  refine ⟨4860355927619011900002259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6480474570158682533336345 4860355927619011900002259)
                  ·
                    refine ⟨7290533891428517850003389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4860355927619011900002259 7290533891428517850003389)
                    ·
                      refine ⟨2733950209285694193751271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7290533891428517850003389 2733950209285694193751271)
                      ·
                        rfl

theorem cell23_5324349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 3, 2, 1, 3].length) (baseStart_5324349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5324349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5324349 prefixEnd_5324349 := by exact prefixLift 5324349
  have htrace : WordTrace (prefixWord ++ tailWord_5324349) baseStart_5324349 baseEnd_5324349 := by
    simpa [prefixWord, tailWord_5324349, baseEnd_5324349] using wordTrace_append hprefix tailTrace_5324349
  have hstable : (prefixWord ++ tailWord_5324349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5324349).length < 2 ^ (prefixWord ++ tailWord_5324349).sum := by decide
  have hdescent : baseEnd_5324349 < baseStart_5324349 := by decide
  rcases family_descends (prefixWord ++ tailWord_5324349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5324372 : List Nat := [2, 4, 1, 1, 1, 2, 3, 2, 1, 4, 2]
def baseStart_5324372 : Nat := 118140960795 + 5324372 * 2 ^ 59
def prefixEnd_5324372 : Nat := 4983230072969 + 3 ^ 40 * 5324372 * 2
def baseEnd_5324372 : Nat := 2733962019340747603763665

theorem tailTrace_5324372 : CollatzResearch.WordTrace tailWord_5324372 prefixEnd_5324372 2733962019340747603763665 := by
  unfold tailWord_5324372
  simp only [CollatzResearch.WordTrace]
  refine ⟨97097900333358524593611685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129463867111144699458148913 97097900333358524593611685)
  ·
    refine ⟨18205856312504723361302191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97097900333358524593611685 18205856312504723361302191)
    ·
      refine ⟨27308784468757085041953287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18205856312504723361302191 27308784468757085041953287)
      ·
        refine ⟨40963176703135627562929931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27308784468757085041953287 40963176703135627562929931)
        ·
          refine ⟨61444765054703441344394897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40963176703135627562929931 61444765054703441344394897)
          ·
            refine ⟨46083573791027581008296173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61444765054703441344394897 46083573791027581008296173)
            ·
              refine ⟨17281340171635342878111065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46083573791027581008296173 17281340171635342878111065)
              ·
                refine ⟨12961005128726507158583299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17281340171635342878111065 12961005128726507158583299)
                ·
                  refine ⟨19441507693089760737874949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12961005128726507158583299 19441507693089760737874949)
                  ·
                    refine ⟨3645282692454330138351553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19441507693089760737874949 3645282692454330138351553)
                    ·
                      refine ⟨2733962019340747603763665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3645282692454330138351553 2733962019340747603763665)
                      ·
                        rfl

theorem cell23_5324372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 2, 1, 4, 2].length) (baseStart_5324372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5324372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5324372 prefixEnd_5324372 := by exact prefixLift 5324372
  have htrace : WordTrace (prefixWord ++ tailWord_5324372) baseStart_5324372 baseEnd_5324372 := by
    simpa [prefixWord, tailWord_5324372, baseEnd_5324372] using wordTrace_append hprefix tailTrace_5324372
  have hstable : (prefixWord ++ tailWord_5324372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5324372).length < 2 ^ (prefixWord ++ tailWord_5324372).sum := by decide
  have hdescent : baseEnd_5324372 < baseStart_5324372 := by decide
  rcases family_descends (prefixWord ++ tailWord_5324372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5324389 : List Nat := [1, 3, 1, 3, 3, 1, 1, 4, 2, 2, 2]
def baseStart_5324389 : Nat := 118140960795 + 5324389 * 2 ^ 59
def prefixEnd_5324389 : Nat := 4983230072969 + 3 ^ 40 * 5324389 * 2
def baseEnd_5324389 : Nat := 2733970748511874037251087

theorem tailTrace_5324389 : CollatzResearch.WordTrace tailWord_5324389 prefixEnd_5324389 2733970748511874037251087 := by
  unfold tailWord_5324389
  simp only [CollatzResearch.WordTrace]
  refine ⟨194196420707655461090592221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129464280471770307393728147 194196420707655461090592221)
  ·
    refine ⟨72823657765370797908972083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 194196420707655461090592221 72823657765370797908972083)
    ·
      refine ⟨109235486648056196863458125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72823657765370797908972083 109235486648056196863458125)
      ·
        refine ⟨40963307493021073823796797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109235486648056196863458125 40963307493021073823796797)
        ·
          refine ⟨15361240309882902683923799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40963307493021073823796797 15361240309882902683923799)
          ·
            refine ⟨23041860464824354025885699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15361240309882902683923799 23041860464824354025885699)
            ·
              refine ⟨34562790697236531038828549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23041860464824354025885699 34562790697236531038828549)
              ·
                refine ⟨6480523255731849569780353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34562790697236531038828549 6480523255731849569780353)
                ·
                  refine ⟨4860392441798887177335265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6480523255731849569780353 4860392441798887177335265)
                  ·
                    refine ⟨3645294331349165383001449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4860392441798887177335265 3645294331349165383001449)
                    ·
                      refine ⟨2733970748511874037251087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3645294331349165383001449 2733970748511874037251087)
                      ·
                        rfl

theorem cell23_5324389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 4, 2, 2, 2].length) (baseStart_5324389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5324389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5324389 prefixEnd_5324389 := by exact prefixLift 5324389
  have htrace : WordTrace (prefixWord ++ tailWord_5324389) baseStart_5324389 baseEnd_5324389 := by
    simpa [prefixWord, tailWord_5324389, baseEnd_5324389] using wordTrace_append hprefix tailTrace_5324389
  have hstable : (prefixWord ++ tailWord_5324389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5324389).length < 2 ^ (prefixWord ++ tailWord_5324389).sum := by decide
  have hdescent : baseEnd_5324389 < baseStart_5324389 := by decide
  rcases family_descends (prefixWord ++ tailWord_5324389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5324406 : List Nat := [5, 1, 1, 2, 2, 1, 2, 3, 2, 2, 2]
def baseStart_5324406 : Nat := 118140960795 + 5324406 * 2 ^ 59
def prefixEnd_5324406 : Nat := 4983230072969 + 3 ^ 40 * 5324406 * 2
def baseEnd_5324406 : Nat := 2733979477683000470738509

theorem tailTrace_5324406 : CollatzResearch.WordTrace tailWord_5324406 prefixEnd_5324406 2733979477683000470738509 := by
  unfold tailWord_5324406
  simp only [CollatzResearch.WordTrace]
  refine ⟨12137315046787117062122567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 129464693832395915329307381 12137315046787117062122567)
  ·
    refine ⟨18205972570180675593183851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12137315046787117062122567 18205972570180675593183851)
    ·
      refine ⟨27308958855271013389775777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18205972570180675593183851 27308958855271013389775777)
      ·
        refine ⟨20481719141453260042331833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27308958855271013389775777 20481719141453260042331833)
        ·
          refine ⟨15361289356089945031748875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20481719141453260042331833 15361289356089945031748875)
          ·
            refine ⟨23041934034134917547623313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15361289356089945031748875 23041934034134917547623313)
            ·
              refine ⟨17281450525601188160717485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23041934034134917547623313 17281450525601188160717485)
              ·
                refine ⟨6480543947100445560269057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17281450525601188160717485 6480543947100445560269057)
                ·
                  refine ⟨4860407960325334170201793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6480543947100445560269057 4860407960325334170201793)
                  ·
                    refine ⟨3645305970244000627651345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4860407960325334170201793 3645305970244000627651345)
                    ·
                      refine ⟨2733979477683000470738509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3645305970244000627651345 2733979477683000470738509)
                      ·
                        rfl

theorem cell23_5324406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 3, 2, 2, 2].length) (baseStart_5324406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5324406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5324406 prefixEnd_5324406 := by exact prefixLift 5324406
  have htrace : WordTrace (prefixWord ++ tailWord_5324406) baseStart_5324406 baseEnd_5324406 := by
    simpa [prefixWord, tailWord_5324406, baseEnd_5324406] using wordTrace_append hprefix tailTrace_5324406
  have hstable : (prefixWord ++ tailWord_5324406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5324406).length < 2 ^ (prefixWord ++ tailWord_5324406).sum := by decide
  have hdescent : baseEnd_5324406 < baseStart_5324406 := by decide
  rcases family_descends (prefixWord ++ tailWord_5324406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5324425 : List Nat := [1, 2, 1, 1, 4, 1, 5, 1, 2, 5]
def baseStart_5324425 : Nat := 118140960795 + 5324425 * 2 ^ 59
def prefixEnd_5324425 : Nat := 4983230072969 + 3 ^ 40 * 5324425 * 2
def baseEnd_5324425 : Nat := 911329744605145298800307

theorem tailTrace_5324425 : CollatzResearch.WordTrace tailWord_5324425 prefixEnd_5324425 911329744605145298800307 := by
  unfold tailWord_5324425
  simp only [CollatzResearch.WordTrace]
  refine ⟨194197733735525039238902729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129465155823683359492601819 194197733735525039238902729)
  ·
    refine ⟨145648300301643779429177047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194197733735525039238902729 145648300301643779429177047)
    ·
      refine ⟨218472450452465669143765571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145648300301643779429177047 218472450452465669143765571)
      ·
        refine ⟨327708675678698503715648357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218472450452465669143765571 327708675678698503715648357)
        ·
          refine ⟨61445376689755969446684067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 327708675678698503715648357 61445376689755969446684067)
          ·
            refine ⟨92168065034633954170026101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61445376689755969446684067 92168065034633954170026101)
            ·
              refine ⟨8640756096996933203439947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 92168065034633954170026101 8640756096996933203439947)
              ·
                refine ⟨12961134145495399805159921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8640756096996933203439947 12961134145495399805159921)
                ·
                  refine ⟨9720850609121549853869941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12961134145495399805159921 9720850609121549853869941)
                  ·
                    refine ⟨911329744605145298800307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9720850609121549853869941 911329744605145298800307)
                    ·
                      rfl

theorem cell23_5324425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 1, 2, 5].length) (baseStart_5324425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5324425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5324425 prefixEnd_5324425 := by exact prefixLift 5324425
  have htrace : WordTrace (prefixWord ++ tailWord_5324425) baseStart_5324425 baseEnd_5324425 := by
    simpa [prefixWord, tailWord_5324425, baseEnd_5324425] using wordTrace_append hprefix tailTrace_5324425
  have hstable : (prefixWord ++ tailWord_5324425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5324425).length < 2 ^ (prefixWord ++ tailWord_5324425).sum := by decide
  have hdescent : baseEnd_5324425 < baseStart_5324425 := by decide
  rcases family_descends (prefixWord ++ tailWord_5324425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5324445 : List Nat := [1, 4, 2, 1, 1, 1, 1, 3, 4, 1, 4]
def baseStart_5324445 : Nat := 118140960795 + 5324445 * 2 ^ 59
def prefixEnd_5324445 : Nat := 4983230072969 + 3 ^ 40 * 5324445 * 2
def baseEnd_5324445 : Nat := 2733999503428525818150829

theorem tailTrace_5324445 : CollatzResearch.WordTrace tailWord_5324445 prefixEnd_5324445 2733999503428525818150829 := by
  unfold tailWord_5324445
  simp only [CollatzResearch.WordTrace]
  refine ⟨194198463195452582654630789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129465642130301721769753859 194198463195452582654630789)
  ·
    refine ⟨36412211849147359247743273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 194198463195452582654630789 36412211849147359247743273)
    ·
      refine ⟨27309158886860519435807455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36412211849147359247743273 27309158886860519435807455)
      ·
        refine ⟨40963738330290779153711183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27309158886860519435807455 40963738330290779153711183)
        ·
          refine ⟨61445607495436168730566775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40963738330290779153711183 61445607495436168730566775)
          ·
            refine ⟨92168411243154253095850163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61445607495436168730566775 92168411243154253095850163)
            ·
              refine ⟨138252616864731379643775245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92168411243154253095850163 138252616864731379643775245)
              ·
                refine ⟨51844731324274267366415717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 138252616864731379643775245 51844731324274267366415717)
                ·
                  refine ⟨9720887123301425131202947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51844731324274267366415717 9720887123301425131202947)
                  ·
                    refine ⟨14581330684952137696804421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9720887123301425131202947 14581330684952137696804421)
                    ·
                      refine ⟨2733999503428525818150829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14581330684952137696804421 2733999503428525818150829)
                      ·
                        rfl

theorem cell23_5324445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 3, 4, 1, 4].length) (baseStart_5324445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5324445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5324445 prefixEnd_5324445 := by exact prefixLift 5324445
  have htrace : WordTrace (prefixWord ++ tailWord_5324445) baseStart_5324445 baseEnd_5324445 := by
    simpa [prefixWord, tailWord_5324445, baseEnd_5324445] using wordTrace_append hprefix tailTrace_5324445
  have hstable : (prefixWord ++ tailWord_5324445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5324445).length < 2 ^ (prefixWord ++ tailWord_5324445).sum := by decide
  have hdescent : baseEnd_5324445 < baseStart_5324445 := by decide
  rcases family_descends (prefixWord ++ tailWord_5324445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5324506 : List Nat := [3, 1, 1, 2, 2, 4, 3, 2, 1, 4]
def baseStart_5324506 : Nat := 118140960795 + 5324506 * 2 ^ 59
def prefixEnd_5324506 : Nat := 4983230072969 + 3 ^ 40 * 5324506 * 2
def baseEnd_5324506 : Nat := 911343608582816693162683

theorem tailTrace_5324506 : CollatzResearch.WordTrace tailWord_5324506 prefixEnd_5324506 911343608582816693162683 := by
  unfold tailWord_5324506
  simp only [CollatzResearch.WordTrace]
  refine ⟨48550172012057897518150343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129467125365487726715067581 48550172012057897518150343)
  ·
    refine ⟨72825258018086846277225515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48550172012057897518150343 72825258018086846277225515)
    ·
      refine ⟨109237887027130269415838273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72825258018086846277225515 109237887027130269415838273)
      ·
        refine ⟨81928415270347702061878705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109237887027130269415838273 81928415270347702061878705)
        ·
          refine ⟨61446311452760776546409029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81928415270347702061878705 61446311452760776546409029)
          ·
            refine ⟨11521183397392645602451693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61446311452760776546409029 11521183397392645602451693)
            ·
              refine ⟨4320443774022242100919385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11521183397392645602451693 4320443774022242100919385)
              ·
                refine ⟨3240332830516681575689539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4320443774022242100919385 3240332830516681575689539)
                ·
                  refine ⟨4860499245775022363534309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3240332830516681575689539 4860499245775022363534309)
                  ·
                    refine ⟨911343608582816693162683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4860499245775022363534309 911343608582816693162683)
                    ·
                      rfl

theorem cell23_5324506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 3, 2, 1, 4].length) (baseStart_5324506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5324506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5324506 prefixEnd_5324506 := by exact prefixLift 5324506
  have htrace : WordTrace (prefixWord ++ tailWord_5324506) baseStart_5324506 baseEnd_5324506 := by
    simpa [prefixWord, tailWord_5324506, baseEnd_5324506] using wordTrace_append hprefix tailTrace_5324506
  have hstable : (prefixWord ++ tailWord_5324506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5324506).length < 2 ^ (prefixWord ++ tailWord_5324506).sum := by decide
  have hdescent : baseEnd_5324506 < baseStart_5324506 := by decide
  rcases family_descends (prefixWord ++ tailWord_5324506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5324519 : List Nat := [1, 1, 5, 4, 1, 1, 1, 3, 6]
def baseStart_5324519 : Nat := 118140960795 + 5324519 * 2 ^ 59
def prefixEnd_5324519 : Nat := 4983230072969 + 3 ^ 40 * 5324519 * 2
def baseEnd_5324519 : Nat := 303781944555217614291721

theorem tailTrace_5324519 : CollatzResearch.WordTrace tailWord_5324519 prefixEnd_5324519 303781944555217614291721 := by
  unfold tailWord_5324519
  simp only [CollatzResearch.WordTrace]
  refine ⟨194201162197184493292824611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129467441464789662195216407 194201162197184493292824611)
  ·
    refine ⟨291301743295776739939236917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194201162197184493292824611 291301743295776739939236917)
    ·
      refine ⟨27309538433979069369303461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 291301743295776739939236917 27309538433979069369303461)
      ·
        refine ⟨5120538456371075506744399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27309538433979069369303461 5120538456371075506744399)
        ·
          refine ⟨7680807684556613260116599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5120538456371075506744399 7680807684556613260116599)
          ·
            refine ⟨11521211526834919890174899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7680807684556613260116599 11521211526834919890174899)
            ·
              refine ⟨17281817290252379835262349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11521211526834919890174899 17281817290252379835262349)
              ·
                refine ⟨6480681483844642438223381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17281817290252379835262349 6480681483844642438223381)
                ·
                  refine ⟨303781944555217614291721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6480681483844642438223381 303781944555217614291721)
                  ·
                    rfl

theorem cell23_5324519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 3, 6].length) (baseStart_5324519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5324519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5324519 prefixEnd_5324519 := by exact prefixLift 5324519
  have htrace : WordTrace (prefixWord ++ tailWord_5324519) baseStart_5324519 baseEnd_5324519 := by
    simpa [prefixWord, tailWord_5324519, baseEnd_5324519] using wordTrace_append hprefix tailTrace_5324519
  have hstable : (prefixWord ++ tailWord_5324519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5324519).length < 2 ^ (prefixWord ++ tailWord_5324519).sum := by decide
  have hdescent : baseEnd_5324519 < baseStart_5324519 := by decide
  rcases family_descends (prefixWord ++ tailWord_5324519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5324522 : List Nat := [3, 1, 3, 1, 1, 1, 2, 1, 3, 5, 2]
def baseStart_5324522 : Nat := 118140960795 + 5324522 * 2 ^ 59
def prefixEnd_5324522 : Nat := 4983230072969 + 3 ^ 40 * 5324522 * 2
def baseEnd_5324522 : Nat := 2734039041438922016887975

theorem tailTrace_5324522 : CollatzResearch.WordTrace tailWord_5324522 prefixEnd_5324522 2734039041438922016887975 := by
  unfold tailWord_5324522
  simp only [CollatzResearch.WordTrace]
  refine ⟨48550317904043406201295955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129467514410782416536789213 48550317904043406201295955)
  ·
    refine ⟨72825476856065109301943933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48550317904043406201295955 72825476856065109301943933)
    ·
      refine ⟨27309553821024415988228975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72825476856065109301943933 27309553821024415988228975)
      ·
        refine ⟨40964330731536623982343463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27309553821024415988228975 40964330731536623982343463)
        ·
          refine ⟨61446496097304935973515195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40964330731536623982343463 61446496097304935973515195)
          ·
            refine ⟨92169744145957403960272793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61446496097304935973515195 92169744145957403960272793)
            ·
              refine ⟨69127308109468052970204595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92169744145957403960272793 69127308109468052970204595)
              ·
                refine ⟨103690962164202079455306893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69127308109468052970204595 103690962164202079455306893)
                ·
                  refine ⟨38884110811575779795740085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 103690962164202079455306893 38884110811575779795740085)
                  ·
                    refine ⟨3645385388585229355850633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38884110811575779795740085 3645385388585229355850633)
                    ·
                      refine ⟨2734039041438922016887975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3645385388585229355850633 2734039041438922016887975)
                      ·
                        rfl

theorem cell23_5324522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 3, 5, 2].length) (baseStart_5324522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5324522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5324522 prefixEnd_5324522 := by exact prefixLift 5324522
  have htrace : WordTrace (prefixWord ++ tailWord_5324522) baseStart_5324522 baseEnd_5324522 := by
    simpa [prefixWord, tailWord_5324522, baseEnd_5324522] using wordTrace_append hprefix tailTrace_5324522
  have hstable : (prefixWord ++ tailWord_5324522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5324522).length < 2 ^ (prefixWord ++ tailWord_5324522).sum := by decide
  have hdescent : baseEnd_5324522 < baseStart_5324522 := by decide
  rcases family_descends (prefixWord ++ tailWord_5324522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5324545 : List Nat := [1, 2, 4, 1, 1, 1, 3, 1, 3, 6]
def baseStart_5324545 : Nat := 118140960795 + 5324545 * 2 ^ 59
def prefixEnd_5324545 : Nat := 4983230072969 + 3 ^ 40 * 5324545 * 2
def baseEnd_5324545 : Nat := 911350283831325142300123

theorem tailTrace_5324545 : CollatzResearch.WordTrace tailWord_5324545 prefixEnd_5324545 911350283831325142300123 := by
  unfold tailWord_5324545
  simp only [CollatzResearch.WordTrace]
  refine ⟨194202110495090299733271089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129468073663393533155514059 194202110495090299733271089)
  ·
    refine ⟨145651582871317724799953317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194202110495090299733271089 145651582871317724799953317)
    ·
      refine ⟨27309671788372073399991247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 145651582871317724799953317 27309671788372073399991247)
      ·
        refine ⟨40964507682558110099986871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27309671788372073399991247 40964507682558110099986871)
        ·
          refine ⟨61446761523837165149980307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40964507682558110099986871 61446761523837165149980307)
          ·
            refine ⟨92170142285755747724970461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61446761523837165149980307 92170142285755747724970461)
            ·
              refine ⟨34563803357158405396863923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92170142285755747724970461 34563803357158405396863923)
              ·
                refine ⟨51845705035737608095295885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34563803357158405396863923 51845705035737608095295885)
                ·
                  refine ⟨19442139388401603035735957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51845705035737608095295885 19442139388401603035735957)
                  ·
                    refine ⟨911350283831325142300123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19442139388401603035735957 911350283831325142300123)
                    ·
                      rfl

theorem cell23_5324545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 1, 3, 6].length) (baseStart_5324545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5324545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5324545 prefixEnd_5324545 := by exact prefixLift 5324545
  have htrace : WordTrace (prefixWord ++ tailWord_5324545) baseStart_5324545 baseEnd_5324545 := by
    simpa [prefixWord, tailWord_5324545, baseEnd_5324545] using wordTrace_append hprefix tailTrace_5324545
  have hstable : (prefixWord ++ tailWord_5324545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5324545).length < 2 ^ (prefixWord ++ tailWord_5324545).sum := by decide
  have hdescent : baseEnd_5324545 < baseStart_5324545 := by decide
  rcases family_descends (prefixWord ++ tailWord_5324545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5324557 : List Nat := [1, 7, 2, 1, 1, 1, 1, 4, 1, 4]
def baseStart_5324557 : Nat := 118140960795 + 5324557 * 2 ^ 59
def prefixEnd_5324557 : Nat := 4983230072969 + 3 ^ 40 * 5324557 * 2
def baseEnd_5324557 : Nat := 911352337753943126650105

theorem tailTrace_5324557 : CollatzResearch.WordTrace tailWord_5324557 prefixEnd_5324557 911352337753943126650105 := by
  unfold tailWord_5324557
  simp only [CollatzResearch.WordTrace]
  refine ⟨194202548171046825782707925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129468365447364550521805283 194202548171046825782707925)
  ·
    refine ⟨4551622222758909979282217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 194202548171046825782707925 4551622222758909979282217)
    ·
      refine ⟨3413716667069182484461663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4551622222758909979282217 3413716667069182484461663)
      ·
        refine ⟨5120575000603773726692495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3413716667069182484461663 5120575000603773726692495)
        ·
          refine ⟨7680862500905660590038743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5120575000603773726692495 7680862500905660590038743)
          ·
            refine ⟨11521293751358490885058115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7680862500905660590038743 11521293751358490885058115)
            ·
              refine ⟨17281940627037736327587173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11521293751358490885058115 17281940627037736327587173)
              ·
                refine ⟨3240363867569575561422595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17281940627037736327587173 3240363867569575561422595)
                ·
                  refine ⟨4860545801354363342133893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3240363867569575561422595 4860545801354363342133893)
                  ·
                    refine ⟨911352337753943126650105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4860545801354363342133893 911352337753943126650105)
                    ·
                      rfl

theorem cell23_5324557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_5324557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5324557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5324557 prefixEnd_5324557 := by exact prefixLift 5324557
  have htrace : WordTrace (prefixWord ++ tailWord_5324557) baseStart_5324557 baseEnd_5324557 := by
    simpa [prefixWord, tailWord_5324557, baseEnd_5324557] using wordTrace_append hprefix tailTrace_5324557
  have hstable : (prefixWord ++ tailWord_5324557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5324557).length < 2 ^ (prefixWord ++ tailWord_5324557).sum := by decide
  have hdescent : baseEnd_5324557 < baseStart_5324557 := by decide
  rcases family_descends (prefixWord ++ tailWord_5324557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5324572 : List Nat := [2, 2, 3, 1, 1, 2, 1, 1, 5, 2, 3]
def baseStart_5324572 : Nat := 118140960795 + 5324572 * 2 ^ 59
def prefixEnd_5324572 : Nat := 4983230072969 + 3 ^ 40 * 5324572 * 2
def baseEnd_5324572 : Nat := 2734064715471646821262745

theorem tailTrace_5324572 : CollatzResearch.WordTrace tailWord_5324572 prefixEnd_5324572 2734064715471646821262745 := by
  unfold tailWord_5324572
  simp only [CollatzResearch.WordTrace]
  refine ⟨97101547632996241672251985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129468730177328322229669313 97101547632996241672251985)
  ·
    refine ⟨72826160724747181254188989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97101547632996241672251985 72826160724747181254188989)
    ·
      refine ⟨27309810271780192970320871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72826160724747181254188989 27309810271780192970320871)
      ·
        refine ⟨40964715407670289455481307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27309810271780192970320871 40964715407670289455481307)
        ·
          refine ⟨61447073111505434183221961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40964715407670289455481307 61447073111505434183221961)
          ·
            refine ⟨46085304833629075637416471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61447073111505434183221961 46085304833629075637416471)
            ·
              refine ⟨69127957250443613456124707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46085304833629075637416471 69127957250443613456124707)
              ·
                refine ⟨103691935875665420184187061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69127957250443613456124707 103691935875665420184187061)
                ·
                  refine ⟨9721118988343633142267537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 103691935875665420184187061 9721118988343633142267537)
                  ·
                    refine ⟨7290839241257724856700653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9721118988343633142267537 7290839241257724856700653)
                    ·
                      refine ⟨2734064715471646821262745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7290839241257724856700653 2734064715471646821262745)
                      ·
                        rfl

theorem cell23_5324572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 5, 2, 3].length) (baseStart_5324572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5324572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5324572 prefixEnd_5324572 := by exact prefixLift 5324572
  have htrace : WordTrace (prefixWord ++ tailWord_5324572) baseStart_5324572 baseEnd_5324572 := by
    simpa [prefixWord, tailWord_5324572, baseEnd_5324572] using wordTrace_append hprefix tailTrace_5324572
  have hstable : (prefixWord ++ tailWord_5324572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5324572).length < 2 ^ (prefixWord ++ tailWord_5324572).sum := by decide
  have hdescent : baseEnd_5324572 < baseStart_5324572 := by decide
  rcases family_descends (prefixWord ++ tailWord_5324572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5324590 : List Nat := [4, 1, 3, 2, 3, 1, 1, 1, 2, 3, 2]
def baseStart_5324590 : Nat := 118140960795 + 5324590 * 2 ^ 59
def prefixEnd_5324590 : Nat := 4983230072969 + 3 ^ 40 * 5324590 * 2
def baseEnd_5324590 : Nat := 2734073958123427750837663

theorem tailTrace_5324590 : CollatzResearch.WordTrace tailWord_5324590 prefixEnd_5324590 2734073958123427750837663 := by
  unfold tailWord_5324590
  simp only [CollatzResearch.WordTrace]
  refine ⟨24275468972490909052332403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129469167853284848279106149 24275468972490909052332403)
  ·
    refine ⟨36413203458736363578498605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24275468972490909052332403 36413203458736363578498605)
    ·
      refine ⟨13654951297026136341936977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36413203458736363578498605 13654951297026136341936977)
      ·
        refine ⟨10241213472769602256452733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13654951297026136341936977 10241213472769602256452733)
        ·
          refine ⟨3840455052288600846169775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10241213472769602256452733 3840455052288600846169775)
          ·
            refine ⟨5760682578432901269254663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3840455052288600846169775 5760682578432901269254663)
            ·
              refine ⟨8641023867649351903881995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5760682578432901269254663 8641023867649351903881995)
              ·
                refine ⟨12961535801474027855822993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8641023867649351903881995 12961535801474027855822993)
                ·
                  refine ⟨9721151851105520891867245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12961535801474027855822993 9721151851105520891867245)
                  ·
                    refine ⟨3645431944164570334450217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9721151851105520891867245 3645431944164570334450217)
                    ·
                      refine ⟨2734073958123427750837663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3645431944164570334450217 2734073958123427750837663)
                      ·
                        rfl

theorem cell23_5324590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 1, 2, 3, 2].length) (baseStart_5324590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5324590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5324590 prefixEnd_5324590 := by exact prefixLift 5324590
  have htrace : WordTrace (prefixWord ++ tailWord_5324590) baseStart_5324590 baseEnd_5324590 := by
    simpa [prefixWord, tailWord_5324590, baseEnd_5324590] using wordTrace_append hprefix tailTrace_5324590
  have hstable : (prefixWord ++ tailWord_5324590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5324590).length < 2 ^ (prefixWord ++ tailWord_5324590).sum := by decide
  have hdescent : baseEnd_5324590 < baseStart_5324590 := by decide
  rcases family_descends (prefixWord ++ tailWord_5324590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5324606 : List Nat := [4, 2, 1, 2, 2, 2, 1, 3, 1, 2, 3]
def baseStart_5324606 : Nat := 118140960795 + 5324606 * 2 ^ 59
def prefixEnd_5324606 : Nat := 4983230072969 + 3 ^ 40 * 5324606 * 2
def baseEnd_5324606 : Nat := 2734082173813899688237589

theorem tailTrace_5324606 : CollatzResearch.WordTrace tailWord_5324606 prefixEnd_5324606 2734082173813899688237589 := by
  unfold tailWord_5324606
  simp only [CollatzResearch.WordTrace]
  refine ⟨24275541918483663393905209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129469556898579538100827781 24275541918483663393905209)
  ·
    refine ⟨18206656438862747545428907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24275541918483663393905209 18206656438862747545428907)
    ·
      refine ⟨27309984658294121318143361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18206656438862747545428907 27309984658294121318143361)
      ·
        refine ⟨20482488493720590988607521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27309984658294121318143361 20482488493720590988607521)
        ·
          refine ⟨15361866370290443241455641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20482488493720590988607521 15361866370290443241455641)
          ·
            refine ⟨11521399777717832431091731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15361866370290443241455641 11521399777717832431091731)
            ·
              refine ⟨17282099666576748646637597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11521399777717832431091731 17282099666576748646637597)
              ·
                refine ⟨6480787374966280742489099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17282099666576748646637597 6480787374966280742489099)
                ·
                  refine ⟨9721181062449421113733649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6480787374966280742489099 9721181062449421113733649)
                  ·
                    refine ⟨7290885796837065835300237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9721181062449421113733649 7290885796837065835300237)
                    ·
                      refine ⟨2734082173813899688237589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7290885796837065835300237 2734082173813899688237589)
                      ·
                        rfl

theorem cell23_5324606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 3, 1, 2, 3].length) (baseStart_5324606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5324606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5324606 prefixEnd_5324606 := by exact prefixLift 5324606
  have htrace : WordTrace (prefixWord ++ tailWord_5324606) baseStart_5324606 baseEnd_5324606 := by
    simpa [prefixWord, tailWord_5324606, baseEnd_5324606] using wordTrace_append hprefix tailTrace_5324606
  have hstable : (prefixWord ++ tailWord_5324606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5324606).length < 2 ^ (prefixWord ++ tailWord_5324606).sum := by decide
  have hdescent : baseEnd_5324606 < baseStart_5324606 := by decide
  rcases family_descends (prefixWord ++ tailWord_5324606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5324676 : List Nat := [2, 3, 2, 1, 1, 1, 4, 1, 4, 2, 2]
def baseStart_5324676 : Nat := 118140960795 + 5324676 * 2 ^ 59
def prefixEnd_5324676 : Nat := 4983230072969 + 3 ^ 40 * 5324676 * 2
def baseEnd_5324676 : Nat := 2734118117459714414362267

theorem tailTrace_5324676 : CollatzResearch.WordTrace tailWord_5324676 prefixEnd_5324676 2734118117459714414362267 := by
  unfold tailWord_5324676
  simp only [CollatzResearch.WordTrace]
  refine ⟨97103444228807854553144941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129471258971743806070859921 97103444228807854553144941)
  ·
    refine ⟨36413791585802945457429353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97103444228807854553144941 36413791585802945457429353)
    ·
      refine ⟨27310343689352209093072015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36413791585802945457429353 27310343689352209093072015)
      ·
        refine ⟨40965515534028313639608023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27310343689352209093072015 40965515534028313639608023)
        ·
          refine ⟨61448273301042470459412035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40965515534028313639608023 61448273301042470459412035)
          ·
            refine ⟨92172409951563705689118053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61448273301042470459412035 92172409951563705689118053)
            ·
              refine ⟨17282326865918194816709635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 92172409951563705689118053 17282326865918194816709635)
              ·
                refine ⟨25923490298877292225064453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17282326865918194816709635 25923490298877292225064453)
                ·
                  refine ⟨4860654431039492292199585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25923490298877292225064453 4860654431039492292199585)
                  ·
                    refine ⟨3645490823279619219149689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4860654431039492292199585 3645490823279619219149689)
                    ·
                      refine ⟨2734118117459714414362267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3645490823279619219149689 2734118117459714414362267)
                      ·
                        rfl

theorem cell23_5324676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 1, 4, 2, 2].length) (baseStart_5324676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5324676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5324676 prefixEnd_5324676 := by exact prefixLift 5324676
  have htrace : WordTrace (prefixWord ++ tailWord_5324676) baseStart_5324676 baseEnd_5324676 := by
    simpa [prefixWord, tailWord_5324676, baseEnd_5324676] using wordTrace_append hprefix tailTrace_5324676
  have hstable : (prefixWord ++ tailWord_5324676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5324676).length < 2 ^ (prefixWord ++ tailWord_5324676).sum := by decide
  have hdescent : baseEnd_5324676 < baseStart_5324676 := by decide
  rcases family_descends (prefixWord ++ tailWord_5324676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5324733 : List Nat := [1, 4, 1, 2, 3, 3, 2, 2, 5]
def baseStart_5324733 : Nat := 118140960795 + 5324733 * 2 ^ 59
def prefixEnd_5324733 : Nat := 4983230072969 + 3 ^ 40 * 5324733 * 2
def baseEnd_5324733 : Nat := 303794153984113410149945

theorem tailTrace_5324733 : CollatzResearch.WordTrace tailWord_5324733 prefixEnd_5324733 303794153984113410149945 := by
  unfold tailWord_5324733
  simp only [CollatzResearch.WordTrace]
  refine ⟨194208967418409207841114853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129472644945606138560743235 194208967418409207841114853)
  ·
    refine ⟨36414181390951726470209035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 194208967418409207841114853 36414181390951726470209035)
    ·
      refine ⟨54621272086427589705313553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36414181390951726470209035 54621272086427589705313553)
      ·
        refine ⟨40965954064820692278985165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54621272086427589705313553 40965954064820692278985165)
        ·
          refine ⟨15362232774307759604619437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40965954064820692278985165 15362232774307759604619437)
          ·
            refine ⟨5760837290365409851732289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15362232774307759604619437 5760837290365409851732289)
            ·
              refine ⟨4320627967774057388799217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5760837290365409851732289 4320627967774057388799217)
              ·
                refine ⟨3240470975830543041599413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4320627967774057388799217 3240470975830543041599413)
                ·
                  refine ⟨303794153984113410149945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3240470975830543041599413 303794153984113410149945)
                  ·
                    rfl

theorem cell23_5324733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 2, 2, 5].length) (baseStart_5324733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5324733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5324733 prefixEnd_5324733 := by exact prefixLift 5324733
  have htrace : WordTrace (prefixWord ++ tailWord_5324733) baseStart_5324733 baseEnd_5324733 := by
    simpa [prefixWord, tailWord_5324733, baseEnd_5324733] using wordTrace_append hprefix tailTrace_5324733
  have hstable : (prefixWord ++ tailWord_5324733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5324733).length < 2 ^ (prefixWord ++ tailWord_5324733).sum := by decide
  have hdescent : baseEnd_5324733 < baseStart_5324733 := by decide
  rcases family_descends (prefixWord ++ tailWord_5324733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5324759 : List Nat := [1, 1, 3, 2, 1, 1, 5, 2, 3, 4]
def baseStart_5324759 : Nat := 118140960795 + 5324759 * 2 ^ 59
def prefixEnd_5324759 : Nat := 4983230072969 + 3 ^ 40 * 5324759 * 2
def baseEnd_5324759 : Nat := 911386912118012529874795

theorem tailTrace_5324759 : CollatzResearch.WordTrace tailWord_5324759 prefixEnd_5324759 911386912118012529874795 := by
  unfold tailWord_5324759
  simp only [CollatzResearch.WordTrace]
  refine ⟨194209915716315014281561331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129473277144210009521040887 194209915716315014281561331)
  ·
    refine ⟨291314873574472521422341997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194209915716315014281561331 291314873574472521422341997)
    ·
      refine ⟨109243077590427195533378249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 291314873574472521422341997 109243077590427195533378249)
      ·
        refine ⟨81932308192820396650033687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109243077590427195533378249 81932308192820396650033687)
        ·
          refine ⟨122898462289230594975050531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81932308192820396650033687 122898462289230594975050531)
          ·
            refine ⟨184347693433845892462575797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122898462289230594975050531 184347693433845892462575797)
            ·
              refine ⟨17282596259423052418366481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 184347693433845892462575797 17282596259423052418366481)
              ·
                refine ⟨12961947194567289313774861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17282596259423052418366481 12961947194567289313774861)
                ·
                  refine ⟨4860730197962733492665573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12961947194567289313774861 4860730197962733492665573)
                  ·
                    refine ⟨911386912118012529874795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4860730197962733492665573 911386912118012529874795)
                    ·
                      rfl

theorem cell23_5324759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 2, 3, 4].length) (baseStart_5324759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5324759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5324759 prefixEnd_5324759 := by exact prefixLift 5324759
  have htrace : WordTrace (prefixWord ++ tailWord_5324759) baseStart_5324759 baseEnd_5324759 := by
    simpa [prefixWord, tailWord_5324759, baseEnd_5324759] using wordTrace_append hprefix tailTrace_5324759
  have hstable : (prefixWord ++ tailWord_5324759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5324759).length < 2 ^ (prefixWord ++ tailWord_5324759).sum := by decide
  have hdescent : baseEnd_5324759 < baseStart_5324759 := by decide
  rcases family_descends (prefixWord ++ tailWord_5324759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5324772 : List Nat := [2, 3, 1, 1, 1, 1, 4, 2, 8]
def baseStart_5324772 : Nat := 118140960795 + 5324772 * 2 ^ 59
def prefixEnd_5324772 : Nat := 4983230072969 + 3 ^ 40 * 5324772 * 2
def baseEnd_5324772 : Nat := 303796379066949559862425

theorem tailTrace_5324772 : CollatzResearch.WordTrace tailWord_5324772 prefixEnd_5324772 303796379066949559862425 := by
  unfold tailWord_5324772
  simp only [CollatzResearch.WordTrace]
  refine ⟨97105194932633958750892285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129473593243511945001189713 97105194932633958750892285)
  ·
    refine ⟨36414448099737734531584607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97105194932633958750892285 36414448099737734531584607)
    ·
      refine ⟨54621672149606601797376911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36414448099737734531584607 54621672149606601797376911)
      ·
        refine ⟨81932508224409902696065367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54621672149606601797376911 81932508224409902696065367)
        ·
          refine ⟨122898762336614854044098051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81932508224409902696065367 122898762336614854044098051)
          ·
            refine ⟨184348143504922281066147077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122898762336614854044098051 184348143504922281066147077)
            ·
              refine ⟨34565276907172927699902577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 184348143504922281066147077 34565276907172927699902577)
              ·
                refine ⟨25923957680379695774926933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34565276907172927699902577 25923957680379695774926933)
                ·
                  refine ⟨303796379066949559862425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25923957680379695774926933 303796379066949559862425)
                  ·
                    rfl

theorem cell23_5324772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 2, 8].length) (baseStart_5324772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5324772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5324772 prefixEnd_5324772 := by exact prefixLift 5324772
  have htrace : WordTrace (prefixWord ++ tailWord_5324772) baseStart_5324772 baseEnd_5324772 := by
    simpa [prefixWord, tailWord_5324772, baseEnd_5324772] using wordTrace_append hprefix tailTrace_5324772
  have hstable : (prefixWord ++ tailWord_5324772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5324772).length < 2 ^ (prefixWord ++ tailWord_5324772).sum := by decide
  have hdescent : baseEnd_5324772 < baseStart_5324772 := by decide
  rcases family_descends (prefixWord ++ tailWord_5324772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5324792 : List Nat := [2, 1, 2, 1, 1, 3, 3, 1, 1, 2, 6]
def baseStart_5324792 : Nat := 118140960795 + 5324792 * 2 ^ 59
def prefixEnd_5324792 : Nat := 4983230072969 + 3 ^ 40 * 5324792 * 2
def baseEnd_5324792 : Nat := 2734177681215635960511733

theorem tailTrace_5324792 : CollatzResearch.WordTrace tailWord_5324792 prefixEnd_5324792 2734177681215635960511733 := by
  unfold tailWord_5324792
  simp only [CollatzResearch.WordTrace]
  refine ⟨97105559662597730458756315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129474079550130307278341753 97105559662597730458756315)
  ·
    refine ⟨145658339493896595688134473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97105559662597730458756315 145658339493896595688134473)
    ·
      refine ⟨109243754620422446766100855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145658339493896595688134473 109243754620422446766100855)
      ·
        refine ⟨163865631930633670149151283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109243754620422446766100855 163865631930633670149151283)
        ·
          refine ⟨245798447895950505223726925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163865631930633670149151283 245798447895950505223726925)
          ·
            refine ⟨92174417960981439458897597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 245798447895950505223726925 92174417960981439458897597)
            ·
              refine ⟨34565406735368039797086599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92174417960981439458897597 34565406735368039797086599)
              ·
                refine ⟨51848110103052059695629899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34565406735368039797086599 51848110103052059695629899)
                ·
                  refine ⟨77772165154578089543444849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51848110103052059695629899 77772165154578089543444849)
                  ·
                    refine ⟨58329123865933567157583637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 77772165154578089543444849 58329123865933567157583637)
                    ·
                      refine ⟨2734177681215635960511733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58329123865933567157583637 2734177681215635960511733)
                      ·
                        rfl

theorem cell23_5324792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 1, 1, 2, 6].length) (baseStart_5324792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5324792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5324792 prefixEnd_5324792 := by exact prefixLift 5324792
  have htrace : WordTrace (prefixWord ++ tailWord_5324792) baseStart_5324792 baseEnd_5324792 := by
    simpa [prefixWord, tailWord_5324792, baseEnd_5324792] using wordTrace_append hprefix tailTrace_5324792
  have hstable : (prefixWord ++ tailWord_5324792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5324792).length < 2 ^ (prefixWord ++ tailWord_5324792).sum := by decide
  have hdescent : baseEnd_5324792 < baseStart_5324792 := by decide
  rcases family_descends (prefixWord ++ tailWord_5324792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5324819 : List Nat := [1, 1, 1, 2, 1, 4, 3, 4, 1, 5]
def baseStart_5324819 : Nat := 118140960795 + 5324819 * 2 ^ 59
def prefixEnd_5324819 : Nat := 4983230072969 + 3 ^ 40 * 5324819 * 2
def baseEnd_5324819 : Nat := 911397181731102451624703

theorem tailTrace_5324819 : CollatzResearch.WordTrace tailWord_5324819 prefixEnd_5324819 911397181731102451624703 := by
  unfold tailWord_5324819
  simp only [CollatzResearch.WordTrace]
  refine ⟨194212104096097644528745511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129474736064065096352497007 194212104096097644528745511)
  ·
    refine ⟨291318156144146466793118267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194212104096097644528745511 291318156144146466793118267)
    ·
      refine ⟨436977234216219700189677401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 291318156144146466793118267 436977234216219700189677401)
      ·
        refine ⟨327732925662164775142258051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 436977234216219700189677401 327732925662164775142258051)
        ·
          refine ⟨491599388493247162713387077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 327732925662164775142258051 491599388493247162713387077)
          ·
            refine ⟨92174885342483843008760077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 491599388493247162713387077 92174885342483843008760077)
            ·
              refine ⟨34565582003431441128285029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92174885342483843008760077 34565582003431441128285029)
              ·
                refine ⟨6481046625643395211553443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34565582003431441128285029 6481046625643395211553443)
                ·
                  refine ⟨9721569938465092817330165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6481046625643395211553443 9721569938465092817330165)
                  ·
                    refine ⟨911397181731102451624703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9721569938465092817330165 911397181731102451624703)
                    ·
                      rfl

theorem cell23_5324819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 4, 1, 5].length) (baseStart_5324819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5324819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5324819 prefixEnd_5324819 := by exact prefixLift 5324819
  have htrace : WordTrace (prefixWord ++ tailWord_5324819) baseStart_5324819 baseEnd_5324819 := by
    simpa [prefixWord, tailWord_5324819, baseEnd_5324819] using wordTrace_append hprefix tailTrace_5324819
  have hstable : (prefixWord ++ tailWord_5324819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5324819).length < 2 ^ (prefixWord ++ tailWord_5324819).sum := by decide
  have hdescent : baseEnd_5324819 < baseStart_5324819 := by decide
  rcases family_descends (prefixWord ++ tailWord_5324819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5324826 : List Nat := [3, 1, 1, 3, 1, 3, 2, 1, 1, 5, 2]
def baseStart_5324826 : Nat := 118140960795 + 5324826 * 2 ^ 59
def prefixEnd_5324826 : Nat := 4983230072969 + 3 ^ 40 * 5324826 * 2
def baseEnd_5324826 : Nat := 2734195139557888827486577

theorem tailTrace_5324826 : CollatzResearch.WordTrace tailWord_5324826 prefixEnd_5324826 2734195139557888827486577 := by
  unfold tailWord_5324826
  simp only [CollatzResearch.WordTrace]
  refine ⟨48553089851768071181062583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129474906271381523149500221 48553089851768071181062583)
  ·
    refine ⟨72829634777652106771593875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48553089851768071181062583 72829634777652106771593875)
    ·
      refine ⟨109244452166478160157390813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72829634777652106771593875 109244452166478160157390813)
      ·
        refine ⟨40966669562429310059021555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109244452166478160157390813 40966669562429310059021555)
        ·
          refine ⟨61450004343643965088532333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40966669562429310059021555 61450004343643965088532333)
          ·
            refine ⟨23043751628866486908199625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61450004343643965088532333 23043751628866486908199625)
            ·
              refine ⟨17282813721649865181149719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23043751628866486908199625 17282813721649865181149719)
              ·
                refine ⟨25924220582474797771724579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17282813721649865181149719 25924220582474797771724579)
                ·
                  refine ⟨38886330873712196657586869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25924220582474797771724579 38886330873712196657586869)
                  ·
                    refine ⟨3645593519410518436648769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38886330873712196657586869 3645593519410518436648769)
                    ·
                      refine ⟨2734195139557888827486577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3645593519410518436648769 2734195139557888827486577)
                      ·
                        rfl

theorem cell23_5324826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 1, 1, 5, 2].length) (baseStart_5324826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5324826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5324826 prefixEnd_5324826 := by exact prefixLift 5324826
  have htrace : WordTrace (prefixWord ++ tailWord_5324826) baseStart_5324826 baseEnd_5324826 := by
    simpa [prefixWord, tailWord_5324826, baseEnd_5324826] using wordTrace_append hprefix tailTrace_5324826
  have hstable : (prefixWord ++ tailWord_5324826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5324826).length < 2 ^ (prefixWord ++ tailWord_5324826).sum := by decide
  have hdescent : baseEnd_5324826 < baseStart_5324826 := by decide
  rcases family_descends (prefixWord ++ tailWord_5324826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5324859 : List Nat := [1, 1, 1, 1, 1, 2, 1, 5, 5, 2, 3]
def baseStart_5324859 : Nat := 118140960795 + 5324859 * 2 ^ 59
def prefixEnd_5324859 : Nat := 4983230072969 + 3 ^ 40 * 5324859 * 2
def baseEnd_5324859 : Nat := 2734212084419487198373925

theorem tailTrace_5324859 : CollatzResearch.WordTrace tailWord_5324859 prefixEnd_5324859 2734212084419487198373925 := by
  unfold tailWord_5324859
  simp only [CollatzResearch.WordTrace]
  refine ⟨194213563015952731360201631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129475708677301820906801087 194213563015952731360201631)
  ·
    refine ⟨291320344523929097040302447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194213563015952731360201631 291320344523929097040302447)
    ·
      refine ⟨436980516785893645560453671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 291320344523929097040302447 436980516785893645560453671)
      ·
        refine ⟨655470775178840468340680507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 436980516785893645560453671 655470775178840468340680507)
        ·
          refine ⟨983206162768260702511020761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 655470775178840468340680507 983206162768260702511020761)
          ·
            refine ⟨737404622076195526883265571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 983206162768260702511020761 737404622076195526883265571)
            ·
              refine ⟨1106106933114293290324898357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 737404622076195526883265571 1106106933114293290324898357)
              ·
                refine ⟨103697524979464995967959221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1106106933114293290324898357 103697524979464995967959221)
                ·
                  refine ⟨9721642966824843371996177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 103697524979464995967959221 9721642966824843371996177)
                  ·
                    refine ⟨7291232225118632528997133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9721642966824843371996177 7291232225118632528997133)
                    ·
                      refine ⟨2734212084419487198373925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7291232225118632528997133 2734212084419487198373925)
                      ·
                        rfl

theorem cell23_5324859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 5, 2, 3].length) (baseStart_5324859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5324859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5324859 prefixEnd_5324859 := by exact prefixLift 5324859
  have htrace : WordTrace (prefixWord ++ tailWord_5324859) baseStart_5324859 baseEnd_5324859 := by
    simpa [prefixWord, tailWord_5324859, baseEnd_5324859] using wordTrace_append hprefix tailTrace_5324859
  have hstable : (prefixWord ++ tailWord_5324859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5324859).length < 2 ^ (prefixWord ++ tailWord_5324859).sum := by decide
  have hdescent : baseEnd_5324859 < baseStart_5324859 := by decide
  rcases family_descends (prefixWord ++ tailWord_5324859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5324869 : List Nat := [1, 3, 1, 1, 1, 3, 1, 5, 1, 2, 4]
def baseStart_5324869 : Nat := 118140960795 + 5324869 * 2 ^ 59
def prefixEnd_5324869 : Nat := 4983230072969 + 3 ^ 40 * 5324869 * 2
def baseEnd_5324869 : Nat := 2734217219226032159248879

theorem tailTrace_5324869 : CollatzResearch.WordTrace tailWord_5324869 prefixEnd_5324869 2734217219226032159248879 := by
  unfold tailWord_5324869
  simp only [CollatzResearch.WordTrace]
  refine ⟨194213927745916503068065661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129475951830611002045377107 194213927745916503068065661)
  ·
    refine ⟨72830222904718688650524623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 194213927745916503068065661 72830222904718688650524623)
    ·
      refine ⟨109245334357078032975786935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72830222904718688650524623 109245334357078032975786935)
      ·
        refine ⟨163868001535617049463680403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109245334357078032975786935 163868001535617049463680403)
        ·
          refine ⟨245802002303425574195520605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163868001535617049463680403 245802002303425574195520605)
          ·
            refine ⟨92175750863784590323320227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 245802002303425574195520605 92175750863784590323320227)
            ·
              refine ⟨138263626295676885484980341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92175750863784590323320227 138263626295676885484980341)
              ·
                refine ⟨12962214965219708014216907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 138263626295676885484980341 12962214965219708014216907)
                ·
                  refine ⟨19443322447829562021325361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12962214965219708014216907 19443322447829562021325361)
                  ·
                    refine ⟨14582491835872171515994021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19443322447829562021325361 14582491835872171515994021)
                    ·
                      refine ⟨2734217219226032159248879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14582491835872171515994021 2734217219226032159248879)
                      ·
                        rfl

theorem cell23_5324869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 5, 1, 2, 4].length) (baseStart_5324869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5324869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5324869 prefixEnd_5324869 := by exact prefixLift 5324869
  have htrace : WordTrace (prefixWord ++ tailWord_5324869) baseStart_5324869 baseEnd_5324869 := by
    simpa [prefixWord, tailWord_5324869, baseEnd_5324869] using wordTrace_append hprefix tailTrace_5324869
  have hstable : (prefixWord ++ tailWord_5324869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5324869).length < 2 ^ (prefixWord ++ tailWord_5324869).sum := by decide
  have hdescent : baseEnd_5324869 < baseStart_5324869 := by decide
  rcases family_descends (prefixWord ++ tailWord_5324869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5324890 : List Nat := [3, 1, 1, 2, 1, 1, 4, 5, 1, 2, 2]
def baseStart_5324890 : Nat := 118140960795 + 5324890 * 2 ^ 59
def prefixEnd_5324890 : Nat := 4983230072969 + 3 ^ 40 * 5324890 * 2
def baseEnd_5324890 : Nat := 2734228002319776577086283

theorem tailTrace_5324890 : CollatzResearch.WordTrace tailWord_5324890 prefixEnd_5324890 2734228002319776577086283 := by
  unfold tailWord_5324890
  simp only [CollatzResearch.WordTrace]
  refine ⟨48553673419710105913645031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129476462452560282436386749 48553673419710105913645031)
  ·
    refine ⟨72830510129565158870467547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48553673419710105913645031 72830510129565158870467547)
    ·
      refine ⟨109245765194347738305701321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72830510129565158870467547 109245765194347738305701321)
      ·
        refine ⟨81934323895760803729275991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109245765194347738305701321 81934323895760803729275991)
        ·
          refine ⟨122901485843641205593913987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81934323895760803729275991 122901485843641205593913987)
          ·
            refine ⟨184352228765461808390870981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122901485843641205593913987 184352228765461808390870981)
            ·
              refine ⟨34566042893524089073288309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 184352228765461808390870981 34566042893524089073288309)
              ·
                refine ⟨3240566521267883350620779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34566042893524089073288309 3240566521267883350620779)
                ·
                  refine ⟨4860849781901825025931169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3240566521267883350620779 4860849781901825025931169)
                  ·
                    refine ⟨3645637336426368769448377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4860849781901825025931169 3645637336426368769448377)
                    ·
                      refine ⟨2734228002319776577086283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3645637336426368769448377 2734228002319776577086283)
                      ·
                        rfl

theorem cell23_5324890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 5, 1, 2, 2].length) (baseStart_5324890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5324890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5324890 prefixEnd_5324890 := by exact prefixLift 5324890
  have htrace : WordTrace (prefixWord ++ tailWord_5324890) baseStart_5324890 baseEnd_5324890 := by
    simpa [prefixWord, tailWord_5324890, baseEnd_5324890] using wordTrace_append hprefix tailTrace_5324890
  have hstable : (prefixWord ++ tailWord_5324890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5324890).length < 2 ^ (prefixWord ++ tailWord_5324890).sum := by decide
  have hdescent : baseEnd_5324890 < baseStart_5324890 := by decide
  rcases family_descends (prefixWord ++ tailWord_5324890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5324893 : List Nat := [1, 4, 4, 1, 1, 1, 3, 1, 1, 1, 5]
def baseStart_5324893 : Nat := 118140960795 + 5324893 * 2 ^ 59
def prefixEnd_5324893 : Nat := 4983230072969 + 3 ^ 40 * 5324893 * 2
def baseEnd_5324893 : Nat := 2734229542761740065348769

theorem tailTrace_5324893 : CollatzResearch.WordTrace tailWord_5324893 prefixEnd_5324893 2734229542761740065348769 := by
  unfold tailWord_5324893
  simp only [CollatzResearch.WordTrace]
  refine ⟨194214803097829555166939333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129476535398553036777959555 194214803097829555166939333)
  ·
    refine ⟨36415275580843041593801125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 194214803097829555166939333 36415275580843041593801125)
    ·
      refine ⟨6827864171408070298837711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36415275580843041593801125 6827864171408070298837711)
      ·
        refine ⟨10241796257112105448256567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6827864171408070298837711 10241796257112105448256567)
        ·
          refine ⟨15362694385668158172384851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10241796257112105448256567 15362694385668158172384851)
          ·
            refine ⟨23044041578502237258577277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15362694385668158172384851 23044041578502237258577277)
            ·
              refine ⟨8641515591938338971966479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23044041578502237258577277 8641515591938338971966479)
              ·
                refine ⟨12962273387907508457949719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8641515591938338971966479 12962273387907508457949719)
                ·
                  refine ⟨19443410081861262686924579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12962273387907508457949719 19443410081861262686924579)
                  ·
                    refine ⟨29165115122791894030386869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19443410081861262686924579 29165115122791894030386869)
                    ·
                      refine ⟨2734229542761740065348769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29165115122791894030386869 2734229542761740065348769)
                      ·
                        rfl

theorem cell23_5324893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_5324893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5324893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5324893 prefixEnd_5324893 := by exact prefixLift 5324893
  have htrace : WordTrace (prefixWord ++ tailWord_5324893) baseStart_5324893 baseEnd_5324893 := by
    simpa [prefixWord, tailWord_5324893, baseEnd_5324893] using wordTrace_append hprefix tailTrace_5324893
  have hstable : (prefixWord ++ tailWord_5324893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5324893).length < 2 ^ (prefixWord ++ tailWord_5324893).sum := by decide
  have hdescent : baseEnd_5324893 < baseStart_5324893 := by decide
  rcases family_descends (prefixWord ++ tailWord_5324893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5324909 : List Nat := [1, 5, 1, 1, 2, 1, 1, 1, 1, 9]
def baseStart_5324909 : Nat := 118140960795 + 5324909 * 2 ^ 59
def prefixEnd_5324909 : Nat := 4983230072969 + 3 ^ 40 * 5324909 * 2
def baseEnd_5324909 : Nat := 911412586150737334249565

theorem tailTrace_5324909 : CollatzResearch.WordTrace tailWord_5324909 prefixEnd_5324909 911412586150737334249565 := by
  unfold tailWord_5324909
  simp only [CollatzResearch.WordTrace]
  refine ⟨194215386665771589899521781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129476924443847726599681187 194215386665771589899521781)
  ·
    refine ⟨18207692499916086553080167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 194215386665771589899521781 18207692499916086553080167)
    ·
      refine ⟨27311538749874129829620251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18207692499916086553080167 27311538749874129829620251)
      ·
        refine ⟨40967308124811194744430377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27311538749874129829620251 40967308124811194744430377)
        ·
          refine ⟨30725481093608396058322783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40967308124811194744430377 30725481093608396058322783)
          ·
            refine ⟨46088221640412594087484175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30725481093608396058322783 46088221640412594087484175)
            ·
              refine ⟨69132332460618891131226263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46088221640412594087484175 69132332460618891131226263)
              ·
                refine ⟨103698498690928336696839395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69132332460618891131226263 103698498690928336696839395)
                ·
                  refine ⟨155547748036392505045259093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 103698498690928336696839395 155547748036392505045259093)
                  ·
                    refine ⟨911412586150737334249565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 155547748036392505045259093 911412586150737334249565)
                    ·
                      rfl

theorem cell23_5324909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 9].length) (baseStart_5324909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5324909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5324909 prefixEnd_5324909 := by exact prefixLift 5324909
  have htrace : WordTrace (prefixWord ++ tailWord_5324909) baseStart_5324909 baseEnd_5324909 := by
    simpa [prefixWord, tailWord_5324909, baseEnd_5324909] using wordTrace_append hprefix tailTrace_5324909
  have hstable : (prefixWord ++ tailWord_5324909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5324909).length < 2 ^ (prefixWord ++ tailWord_5324909).sum := by decide
  have hdescent : baseEnd_5324909 < baseStart_5324909 := by decide
  rcases family_descends (prefixWord ++ tailWord_5324909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5324933 : List Nat := [1, 3, 1, 1, 5, 1, 2, 1, 3, 3, 2]
def baseStart_5324933 : Nat := 118140960795 + 5324933 * 2 ^ 59
def prefixEnd_5324933 : Nat := 4983230072969 + 3 ^ 40 * 5324933 * 2
def baseEnd_5324933 : Nat := 2734250081987919908848585

theorem tailTrace_5324933 : CollatzResearch.WordTrace tailWord_5324933 prefixEnd_5324933 2734250081987919908848585 := by
  unfold tailWord_5324933
  simp only [CollatzResearch.WordTrace]
  refine ⟨194216262017684641998395453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129477508011789761332263635 194216262017684641998395453)
  ·
    refine ⟨72831098256631740749398295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 194216262017684641998395453 72831098256631740749398295)
    ·
      refine ⟨109246647384947611124097443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72831098256631740749398295 109246647384947611124097443)
      ·
        refine ⟨163869971077421416686146165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109246647384947611124097443 163869971077421416686146165)
        ·
          refine ⟨15362809788508257814326203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 163869971077421416686146165 15362809788508257814326203)
          ·
            refine ⟨23044214682762386721489305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15362809788508257814326203 23044214682762386721489305)
            ·
              refine ⟨17283161012071790041116979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23044214682762386721489305 17283161012071790041116979)
              ·
                refine ⟨25924741518107685061675469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17283161012071790041116979 25924741518107685061675469)
                ·
                  refine ⟨9721778069290381898128301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25924741518107685061675469 9721778069290381898128301)
                  ·
                    refine ⟨3645666775983893211798113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9721778069290381898128301 3645666775983893211798113)
                    ·
                      refine ⟨2734250081987919908848585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3645666775983893211798113 2734250081987919908848585)
                      ·
                        rfl

theorem cell23_5324933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 1, 3, 3, 2].length) (baseStart_5324933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5324933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5324933 prefixEnd_5324933 := by exact prefixLift 5324933
  have htrace : WordTrace (prefixWord ++ tailWord_5324933) baseStart_5324933 baseEnd_5324933 := by
    simpa [prefixWord, tailWord_5324933, baseEnd_5324933] using wordTrace_append hprefix tailTrace_5324933
  have hstable : (prefixWord ++ tailWord_5324933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5324933).length < 2 ^ (prefixWord ++ tailWord_5324933).sum := by decide
  have hdescent : baseEnd_5324933 < baseStart_5324933 := by decide
  rcases family_descends (prefixWord ++ tailWord_5324933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5324949 : List Nat := [1, 3, 2, 1, 1, 1, 4, 1, 1, 3, 5]
def baseStart_5324949 : Nat := 118140960795 + 5324949 * 2 ^ 59
def prefixEnd_5324949 : Nat := 4983230072969 + 3 ^ 40 * 5324949 * 2
def baseEnd_5324949 : Nat := 2734258297678391846248511

theorem tailTrace_5324949 : CollatzResearch.WordTrace tailWord_5324949 prefixEnd_5324949 2734258297678391846248511 := by
  unfold tailWord_5324949
  simp only [CollatzResearch.WordTrace]
  refine ⟨194216845585626676730977901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129477897057084451153985267 194216845585626676730977901)
  ·
    refine ⟨72831317094610003774116713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 194216845585626676730977901 72831317094610003774116713)
    ·
      refine ⟨54623487820957502830587535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72831317094610003774116713 54623487820957502830587535)
      ·
        refine ⟨81935231731436254245881303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54623487820957502830587535 81935231731436254245881303)
        ·
          refine ⟨122902847597154381368821955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81935231731436254245881303 122902847597154381368821955)
          ·
            refine ⟨184354271395731572053232933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122902847597154381368821955 184354271395731572053232933)
            ·
              refine ⟨34566425886699669759981175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 184354271395731572053232933 34566425886699669759981175)
              ·
                refine ⟨51849638830049504639971763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34566425886699669759981175 51849638830049504639971763)
                ·
                  refine ⟨77774458245074256959957645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51849638830049504639971763 77774458245074256959957645)
                  ·
                    refine ⟨29165421841902846359984117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 77774458245074256959957645 29165421841902846359984117)
                    ·
                      refine ⟨2734258297678391846248511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29165421841902846359984117 2734258297678391846248511)
                      ·
                        rfl

theorem cell23_5324949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 1, 1, 3, 5].length) (baseStart_5324949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5324949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5324949 prefixEnd_5324949 := by exact prefixLift 5324949
  have htrace : WordTrace (prefixWord ++ tailWord_5324949) baseStart_5324949 baseEnd_5324949 := by
    simpa [prefixWord, tailWord_5324949, baseEnd_5324949] using wordTrace_append hprefix tailTrace_5324949
  have hstable : (prefixWord ++ tailWord_5324949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5324949).length < 2 ^ (prefixWord ++ tailWord_5324949).sum := by decide
  have hdescent : baseEnd_5324949 < baseStart_5324949 := by decide
  rcases family_descends (prefixWord ++ tailWord_5324949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5324974 : List Nat := [4, 1, 4, 2, 2, 1, 1, 1, 1, 3, 3]
def baseStart_5324974 : Nat := 118140960795 + 5324974 * 2 ^ 59
def prefixEnd_5324974 : Nat := 4983230072969 + 3 ^ 40 * 5324974 * 2
def baseEnd_5324974 : Nat := 2734271134694754248435897

theorem tailTrace_5324974 : CollatzResearch.WordTrace tailWord_5324974 prefixEnd_5324974 2734271134694754248435897 := by
  unfold tailWord_5324974
  simp only [CollatzResearch.WordTrace]
  refine ⟨24277219676317013250079747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129478504940357404000425317 24277219676317013250079747)
  ·
    refine ⟨36415829514475519875119621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24277219676317013250079747 36415829514475519875119621)
    ·
      refine ⟨6827968033964159976584929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36415829514475519875119621 6827968033964159976584929)
      ·
        refine ⟨5120976025473119982438697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6827968033964159976584929 5120976025473119982438697)
        ·
          refine ⟨3840732019104839986829023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5120976025473119982438697 3840732019104839986829023)
          ·
            refine ⟨5761098028657259980243535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3840732019104839986829023 5761098028657259980243535)
            ·
              refine ⟨8641647042985889970365303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5761098028657259980243535 8641647042985889970365303)
              ·
                refine ⟨12962470564478834955547955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8641647042985889970365303 12962470564478834955547955)
                ·
                  refine ⟨19443705846718252433321933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12962470564478834955547955 19443705846718252433321933)
                  ·
                    refine ⟨7291389692519344662495725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19443705846718252433321933 7291389692519344662495725)
                    ·
                      refine ⟨2734271134694754248435897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7291389692519344662495725 2734271134694754248435897)
                      ·
                        rfl

theorem cell23_5324974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_5324974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5324974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5324974 prefixEnd_5324974 := by exact prefixLift 5324974
  have htrace : WordTrace (prefixWord ++ tailWord_5324974) baseStart_5324974 baseEnd_5324974 := by
    simpa [prefixWord, tailWord_5324974, baseEnd_5324974] using wordTrace_append hprefix tailTrace_5324974
  have hstable : (prefixWord ++ tailWord_5324974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5324974).length < 2 ^ (prefixWord ++ tailWord_5324974).sum := by decide
  have hdescent : baseEnd_5324974 < baseStart_5324974 := by decide
  rcases family_descends (prefixWord ++ tailWord_5324974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5325016 : List Nat := [2, 1, 2, 2, 4, 1, 1, 1, 4, 5]
def baseStart_5325016 : Nat := 118140960795 + 5325016 * 2 ^ 59
def prefixEnd_5325016 : Nat := 4983230072969 + 3 ^ 40 * 5325016 * 2
def baseEnd_5325016 : Nat := 911430900294081028036901

theorem tailTrace_5325016 : CollatzResearch.WordTrace tailWord_5325016 prefixEnd_5325016 911430900294081028036901 := by
  unfold tailWord_5325016
  simp only [CollatzResearch.WordTrace]
  refine ⟨97109644638191973586833451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129479526184255964782444601 97109644638191973586833451)
  ·
    refine ⟨145664466957287960380250177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97109644638191973586833451 145664466957287960380250177)
    ·
      refine ⟨109248350217965970285187633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145664466957287960380250177 109248350217965970285187633)
      ·
        refine ⟨81936262663474477713890725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109248350217965970285187633 81936262663474477713890725)
        ·
          refine ⟨15363049249401464571354511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81936262663474477713890725 15363049249401464571354511)
          ·
            refine ⟨23044573874102196857031767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15363049249401464571354511 23044573874102196857031767)
            ·
              refine ⟨34566860811153295285547651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23044573874102196857031767 34566860811153295285547651)
              ·
                refine ⟨51850291216729942928321477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34566860811153295285547651 51850291216729942928321477)
                ·
                  refine ⟨9721929603136864299060277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51850291216729942928321477 9721929603136864299060277)
                  ·
                    refine ⟨911430900294081028036901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9721929603136864299060277 911430900294081028036901)
                    ·
                      rfl

theorem cell23_5325016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 1, 4, 5].length) (baseStart_5325016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5325016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5325016 prefixEnd_5325016 := by exact prefixLift 5325016
  have htrace : WordTrace (prefixWord ++ tailWord_5325016) baseStart_5325016 baseEnd_5325016 := by
    simpa [prefixWord, tailWord_5325016, baseEnd_5325016] using wordTrace_append hprefix tailTrace_5325016
  have hstable : (prefixWord ++ tailWord_5325016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5325016).length < 2 ^ (prefixWord ++ tailWord_5325016).sum := by decide
  have hdescent : baseEnd_5325016 < baseStart_5325016 := by decide
  rcases family_descends (prefixWord ++ tailWord_5325016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5325036 : List Nat := [2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 4]
def baseStart_5325036 : Nat := 118140960795 + 5325036 * 2 ^ 59
def prefixEnd_5325036 : Nat := 4983230072969 + 3 ^ 40 * 5325036 * 2
def baseEnd_5325036 : Nat := 2734302970495333005860611

theorem tailTrace_5325036 : CollatzResearch.WordTrace tailWord_5325036 prefixEnd_5325036 2734302970495333005860611 := by
  unfold tailWord_5325036
  simp only [CollatzResearch.WordTrace]
  refine ⟨97110009368155745294697481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129480012490874327059596641 97110009368155745294697481)
  ·
    refine ⟨72832507026116808971023111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97110009368155745294697481 72832507026116808971023111)
    ·
      refine ⟨109248760539175213456534667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72832507026116808971023111 109248760539175213456534667)
      ·
        refine ⟨163873140808762820184802001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109248760539175213456534667 163873140808762820184802001)
        ·
          refine ⟨122904855606572115138601501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163873140808762820184802001 122904855606572115138601501)
          ·
            refine ⟨46089320852464543176975563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 122904855606572115138601501 46089320852464543176975563)
            ·
              refine ⟨69133981278696814765463345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46089320852464543176975563 69133981278696814765463345)
              ·
                refine ⟨51850485959022611074097509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69133981278696814765463345 51850485959022611074097509)
                ·
                  refine ⟨9721966117316739576393283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51850485959022611074097509 9721966117316739576393283)
                  ·
                    refine ⟨14582949175975109364589925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9721966117316739576393283 14582949175975109364589925)
                    ·
                      refine ⟨2734302970495333005860611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14582949175975109364589925 2734302970495333005860611)
                      ·
                        rfl

theorem cell23_5325036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 4].length) (baseStart_5325036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5325036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5325036 prefixEnd_5325036 := by exact prefixLift 5325036
  have htrace : WordTrace (prefixWord ++ tailWord_5325036) baseStart_5325036 baseEnd_5325036 := by
    simpa [prefixWord, tailWord_5325036, baseEnd_5325036] using wordTrace_append hprefix tailTrace_5325036
  have hstable : (prefixWord ++ tailWord_5325036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5325036).length < 2 ^ (prefixWord ++ tailWord_5325036).sum := by decide
  have hdescent : baseEnd_5325036 < baseStart_5325036 := by decide
  rcases family_descends (prefixWord ++ tailWord_5325036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5325046 : List Nat := [5, 1, 1, 1, 1, 1, 2, 1, 2, 8]
def baseStart_5325046 : Nat := 118140960795 + 5325046 * 2 ^ 59
def prefixEnd_5325046 : Nat := 4983230072969 + 3 ^ 40 * 5325046 * 2
def baseEnd_5325046 : Nat := 911436035100625988911855

theorem tailTrace_5325046 : CollatzResearch.WordTrace tailWord_5325046 prefixEnd_5325046 911436035100625988911855 := by
  unfold tailWord_5325046
  simp only [CollatzResearch.WordTrace]
  refine ⟨12138773966642203893578687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 129480255644183508198172661 12138773966642203893578687)
  ·
    refine ⟨18208160949963305840368031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12138773966642203893578687 18208160949963305840368031)
    ·
      refine ⟨27312241424944958760552047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18208160949963305840368031 27312241424944958760552047)
      ·
        refine ⟨40968362137417438140828071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27312241424944958760552047 40968362137417438140828071)
        ·
          refine ⟨61452543206126157211242107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40968362137417438140828071 61452543206126157211242107)
          ·
            refine ⟨92178814809189235816863161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61452543206126157211242107 92178814809189235816863161)
            ·
              refine ⟨69134111106891926862647371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92178814809189235816863161 69134111106891926862647371)
              ·
                refine ⟨103701166660337890293971057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69134111106891926862647371 103701166660337890293971057)
                ·
                  refine ⟨77775874995253417720478293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 103701166660337890293971057 77775874995253417720478293)
                  ·
                    refine ⟨911436035100625988911855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 77775874995253417720478293 911436035100625988911855)
                    ·
                      rfl

theorem cell23_5325046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 2, 8].length) (baseStart_5325046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5325046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5325046 prefixEnd_5325046 := by exact prefixLift 5325046
  have htrace : WordTrace (prefixWord ++ tailWord_5325046) baseStart_5325046 baseEnd_5325046 := by
    simpa [prefixWord, tailWord_5325046, baseEnd_5325046] using wordTrace_append hprefix tailTrace_5325046
  have hstable : (prefixWord ++ tailWord_5325046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5325046).length < 2 ^ (prefixWord ++ tailWord_5325046).sum := by decide
  have hdescent : baseEnd_5325046 < baseStart_5325046 := by decide
  rcases family_descends (prefixWord ++ tailWord_5325046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5325056 : List Nat := [2, 1, 1, 2, 1, 1, 4, 3, 1, 4, 3]
def baseStart_5325056 : Nat := 118140960795 + 5325056 * 2 ^ 59
def prefixEnd_5325056 : Nat := 4983230072969 + 3 ^ 40 * 5325056 * 2
def baseEnd_5325056 : Nat := 2734313240108422927610519

theorem tailTrace_5325056 : CollatzResearch.WordTrace tailWord_5325056 prefixEnd_5325056 2734313240108422927610519 := by
  unfold tailWord_5325056
  simp only [CollatzResearch.WordTrace]
  refine ⟨97110374098119517002561511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129480498797492689336748681 97110374098119517002561511)
  ·
    refine ⟨145665561147179275503842267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97110374098119517002561511 145665561147179275503842267)
    ·
      refine ⟨218498341720768913255763401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145665561147179275503842267 218498341720768913255763401)
      ·
        refine ⟨163873756290576684941822551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 218498341720768913255763401 163873756290576684941822551)
        ·
          refine ⟨245810634435865027412733827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163873756290576684941822551 245810634435865027412733827)
          ·
            refine ⟨368715951653797541119100741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 245810634435865027412733827 368715951653797541119100741)
            ·
              refine ⟨69134240935087038959831389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 368715951653797541119100741 69134240935087038959831389)
              ·
                refine ⟨25925340350657639609936771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69134240935087038959831389 25925340350657639609936771)
                ·
                  refine ⟨38888010525986459414905157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25925340350657639609936771 38888010525986459414905157)
                  ·
                    refine ⟨7291501973622461140294717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38888010525986459414905157 7291501973622461140294717)
                    ·
                      refine ⟨2734313240108422927610519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7291501973622461140294717 2734313240108422927610519)
                      ·
                        rfl

theorem cell23_5325056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 1, 4, 3].length) (baseStart_5325056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5325056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5325056 prefixEnd_5325056 := by exact prefixLift 5325056
  have htrace : WordTrace (prefixWord ++ tailWord_5325056) baseStart_5325056 baseEnd_5325056 := by
    simpa [prefixWord, tailWord_5325056, baseEnd_5325056] using wordTrace_append hprefix tailTrace_5325056
  have hstable : (prefixWord ++ tailWord_5325056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5325056).length < 2 ^ (prefixWord ++ tailWord_5325056).sum := by decide
  have hdescent : baseEnd_5325056 < baseStart_5325056 := by decide
  rcases family_descends (prefixWord ++ tailWord_5325056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5325073 : List Nat := [1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 3]
def baseStart_5325073 : Nat := 118140960795 + 5325073 * 2 ^ 59
def prefixEnd_5325073 : Nat := 4983230072969 + 3 ^ 40 * 5325073 * 2
def baseEnd_5325073 : Nat := 2734321969279549361097941

theorem tailTrace_5325073 : CollatzResearch.WordTrace tailWord_5325073 prefixEnd_5325073 2734321969279549361097941 := by
  unfold tailWord_5325073
  simp only [CollatzResearch.WordTrace]
  refine ⟨194221368237177445908491873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129480912158118297272327915 194221368237177445908491873)
  ·
    refine ⟨145666026177883084431368905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194221368237177445908491873 145666026177883084431368905)
    ·
      refine ⟨109249519633412313323526679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145666026177883084431368905 109249519633412313323526679)
      ·
        refine ⟨163874279450118469985290019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109249519633412313323526679 163874279450118469985290019)
        ·
          refine ⟨245811419175177704977935029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163874279450118469985290019 245811419175177704977935029)
          ·
            refine ⟨23044820547672909841681409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 245811419175177704977935029 23044820547672909841681409)
            ·
              refine ⟨17283615410754682381261057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23044820547672909841681409 17283615410754682381261057)
              ·
                refine ⟨12962711558066011785945793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17283615410754682381261057 12962711558066011785945793)
                ·
                  refine ⟨9722033668549508839459345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12962711558066011785945793 9722033668549508839459345)
                  ·
                    refine ⟨7291525251412131629594509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9722033668549508839459345 7291525251412131629594509)
                    ·
                      refine ⟨2734321969279549361097941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7291525251412131629594509 2734321969279549361097941)
                      ·
                        rfl

theorem cell23_5325073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 3].length) (baseStart_5325073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5325073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5325073 prefixEnd_5325073 := by exact prefixLift 5325073
  have htrace : WordTrace (prefixWord ++ tailWord_5325073) baseStart_5325073 baseEnd_5325073 := by
    simpa [prefixWord, tailWord_5325073, baseEnd_5325073] using wordTrace_append hprefix tailTrace_5325073
  have hstable : (prefixWord ++ tailWord_5325073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5325073).length < 2 ^ (prefixWord ++ tailWord_5325073).sum := by decide
  have hdescent : baseEnd_5325073 < baseStart_5325073 := by decide
  rcases family_descends (prefixWord ++ tailWord_5325073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5325080 : List Nat := [2, 1, 2, 3, 1, 2, 3, 4, 1, 4]
def baseStart_5325080 : Nat := 118140960795 + 5325080 * 2 ^ 59
def prefixEnd_5325080 : Nat := 4983230072969 + 3 ^ 40 * 5325080 * 2
def baseEnd_5325080 : Nat := 911441854548043611236803

theorem tailTrace_5325080 : CollatzResearch.WordTrace tailWord_5325080 prefixEnd_5325080 911441854548043611236803 := by
  unfold tailWord_5325080
  simp only [CollatzResearch.WordTrace]
  refine ⟨97110811774076043051998347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129481082365434724069331129 97110811774076043051998347)
  ·
    refine ⟨145666217661114064577997521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97110811774076043051998347 145666217661114064577997521)
    ·
      refine ⟨109249663245835548433498141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145666217661114064577997521 109249663245835548433498141)
      ·
        refine ⟨40968623717188330662561803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109249663245835548433498141 40968623717188330662561803)
        ·
          refine ⟨61452935575782495993842705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40968623717188330662561803 61452935575782495993842705)
          ·
            refine ⟨46089701681836871995382029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61452935575782495993842705 46089701681836871995382029)
            ·
              refine ⟨17283638130688826998268261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46089701681836871995382029 17283638130688826998268261)
              ·
                refine ⟨3240682149504155062175299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17283638130688826998268261 3240682149504155062175299)
                ·
                  refine ⟨4861023224256232593262949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3240682149504155062175299 4861023224256232593262949)
                  ·
                    refine ⟨911441854548043611236803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4861023224256232593262949 911441854548043611236803)
                    ·
                      rfl

theorem cell23_5325080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 4, 1, 4].length) (baseStart_5325080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5325080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5325080 prefixEnd_5325080 := by exact prefixLift 5325080
  have htrace : WordTrace (prefixWord ++ tailWord_5325080) baseStart_5325080 baseEnd_5325080 := by
    simpa [prefixWord, tailWord_5325080, baseEnd_5325080] using wordTrace_append hprefix tailTrace_5325080
  have hstable : (prefixWord ++ tailWord_5325080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5325080).length < 2 ^ (prefixWord ++ tailWord_5325080).sum := by decide
  have hdescent : baseEnd_5325080 < baseStart_5325080 := by decide
  rcases family_descends (prefixWord ++ tailWord_5325080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5325103 : List Nat := [1, 1, 2, 1, 2, 1, 5, 1, 5, 1, 3]
def baseStart_5325103 : Nat := 118140960795 + 5325103 * 2 ^ 59
def prefixEnd_5325103 : Nat := 4983230072969 + 3 ^ 40 * 5325103 * 2
def baseEnd_5325103 : Nat := 2734337373699184243722803

theorem tailTrace_5325103 : CollatzResearch.WordTrace tailWord_5325103 prefixEnd_5325103 2734337373699184243722803 := by
  unfold tailWord_5325103
  simp only [CollatzResearch.WordTrace]
  refine ⟨194222462427068761032083963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129481641618045840688055975 194222462427068761032083963)
  ·
    refine ⟨291333693640603141548125945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194222462427068761032083963 291333693640603141548125945)
    ·
      refine ⟨218500270230452356161094459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 291333693640603141548125945 218500270230452356161094459)
      ·
        refine ⟨327750405345678534241641689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218500270230452356161094459 327750405345678534241641689)
        ·
          refine ⟨245812804009258900681231267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 327750405345678534241641689 245812804009258900681231267)
          ·
            refine ⟨368719206013888351021846901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 245812804009258900681231267 368719206013888351021846901)
            ·
              refine ⟨34567425563802032908298147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 368719206013888351021846901 34567425563802032908298147)
              ·
                refine ⟨51851138345703049362447221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34567425563802032908298147 51851138345703049362447221)
                ·
                  refine ⟨4861044219909660877729427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51851138345703049362447221 4861044219909660877729427)
                  ·
                    refine ⟨7291566329864491316594141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4861044219909660877729427 7291566329864491316594141)
                    ·
                      refine ⟨2734337373699184243722803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7291566329864491316594141 2734337373699184243722803)
                      ·
                        rfl

theorem cell23_5325103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 1, 5, 1, 3].length) (baseStart_5325103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5325103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5325103 prefixEnd_5325103 := by exact prefixLift 5325103
  have htrace : WordTrace (prefixWord ++ tailWord_5325103) baseStart_5325103 baseEnd_5325103 := by
    simpa [prefixWord, tailWord_5325103, baseEnd_5325103] using wordTrace_append hprefix tailTrace_5325103
  have hstable : (prefixWord ++ tailWord_5325103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5325103).length < 2 ^ (prefixWord ++ tailWord_5325103).sum := by decide
  have hdescent : baseEnd_5325103 < baseStart_5325103 := by decide
  rcases family_descends (prefixWord ++ tailWord_5325103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5325137 : List Nat := [1, 2, 2, 1, 4, 2, 2, 4, 1, 1, 3]
def baseStart_5325137 : Nat := 118140960795 + 5325137 * 2 ^ 59
def prefixEnd_5325137 : Nat := 4983230072969 + 3 ^ 40 * 5325137 * 2
def baseEnd_5325137 : Nat := 2734354832041437110697647

theorem tailTrace_5325137 : CollatzResearch.WordTrace tailWord_5325137 prefixEnd_5325137 2734354832041437110697647 := by
  unfold tailWord_5325137
  simp only [CollatzResearch.WordTrace]
  refine ⟨194223702508945584838821665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129482468339297056559214443 194223702508945584838821665)
  ·
    refine ⟨145667776881709188629116249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194223702508945584838821665 145667776881709188629116249)
    ·
      refine ⟨109250832661281891471837187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145667776881709188629116249 109250832661281891471837187)
      ·
        refine ⟨163876248991922837207755781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109250832661281891471837187 163876248991922837207755781)
        ·
          refine ⟨30726796685985531976454209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 163876248991922837207755781 30726796685985531976454209)
          ·
            refine ⟨23045097514489148982340657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30726796685985531976454209 23045097514489148982340657)
            ·
              refine ⟨17283823135866861736755493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23045097514489148982340657 17283823135866861736755493)
              ·
                refine ⟨3240716837975036575641655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17283823135866861736755493 3240716837975036575641655)
                ·
                  refine ⟨4861075256962554863462483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3240716837975036575641655 4861075256962554863462483)
                  ·
                    refine ⟨7291612885443832295193725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4861075256962554863462483 7291612885443832295193725)
                    ·
                      refine ⟨2734354832041437110697647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7291612885443832295193725 2734354832041437110697647)
                      ·
                        rfl

theorem cell23_5325137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 4, 1, 1, 3].length) (baseStart_5325137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5325137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5325137 prefixEnd_5325137 := by exact prefixLift 5325137
  have htrace : WordTrace (prefixWord ++ tailWord_5325137) baseStart_5325137 baseEnd_5325137 := by
    simpa [prefixWord, tailWord_5325137, baseEnd_5325137] using wordTrace_append hprefix tailTrace_5325137
  have hstable : (prefixWord ++ tailWord_5325137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5325137).length < 2 ^ (prefixWord ++ tailWord_5325137).sum := by decide
  have hdescent : baseEnd_5325137 < baseStart_5325137 := by decide
  rcases family_descends (prefixWord ++ tailWord_5325137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5325160 : List Nat := [2, 1, 4, 2, 2, 1, 1, 4, 1, 1, 4]
def baseStart_5325160 : Nat := 118140960795 + 5325160 * 2 ^ 59
def prefixEnd_5325160 : Nat := 4983230072969 + 3 ^ 40 * 5325160 * 2
def baseEnd_5325160 : Nat := 2734366642096490520710041

theorem tailTrace_5325160 : CollatzResearch.WordTrace tailWord_5325160 prefixEnd_5325160 2734366642096490520710041 := by
  unfold tailWord_5325160
  simp only [CollatzResearch.WordTrace]
  refine ⟨97112270693931129883454467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129483027591908173177939289 97112270693931129883454467)
  ·
    refine ⟨145668406040896694825181701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97112270693931129883454467 145668406040896694825181701)
    ·
      refine ⟨27312826132668130279721569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 145668406040896694825181701 27312826132668130279721569)
      ·
        refine ⟨20484619599501097709791177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27312826132668130279721569 20484619599501097709791177)
        ·
          refine ⟨15363464699625823282343383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20484619599501097709791177 15363464699625823282343383)
          ·
            refine ⟨23045197049438734923515075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15363464699625823282343383 23045197049438734923515075)
            ·
              refine ⟨34567795574158102385272613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23045197049438734923515075 34567795574158102385272613)
              ·
                refine ⟨6481461670154644197238615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34567795574158102385272613 6481461670154644197238615)
                ·
                  refine ⟨9722192505231966295857923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6481461670154644197238615 9722192505231966295857923)
                  ·
                    refine ⟨14583288757847949443786885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9722192505231966295857923 14583288757847949443786885)
                    ·
                      refine ⟨2734366642096490520710041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14583288757847949443786885 2734366642096490520710041)
                      ·
                        rfl

theorem cell23_5325160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 4, 1, 1, 4].length) (baseStart_5325160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5325160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5325160 prefixEnd_5325160 := by exact prefixLift 5325160
  have htrace : WordTrace (prefixWord ++ tailWord_5325160) baseStart_5325160 baseEnd_5325160 := by
    simpa [prefixWord, tailWord_5325160, baseEnd_5325160] using wordTrace_append hprefix tailTrace_5325160
  have hstable : (prefixWord ++ tailWord_5325160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5325160).length < 2 ^ (prefixWord ++ tailWord_5325160).sum := by decide
  have hdescent : baseEnd_5325160 < baseStart_5325160 := by decide
  rcases family_descends (prefixWord ++ tailWord_5325160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5325214 : List Nat := [4, 3, 1, 2, 1, 1, 3, 2, 1, 2, 3]
def baseStart_5325214 : Nat := 118140960795 + 5325214 * 2 ^ 59
def prefixEnd_5325214 : Nat := 4983230072969 + 3 ^ 40 * 5325214 * 2
def baseEnd_5325214 : Nat := 2734394370051833309434793

theorem tailTrace_5325214 : CollatzResearch.WordTrace tailWord_5325214 prefixEnd_5325214 2734394370051833309434793 := by
  unfold tailWord_5325214
  simp only [CollatzResearch.WordTrace]
  refine ⟨24278313866208328373671837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129484340619777751326249797 24278313866208328373671837)
  ·
    refine ⟨9104367699828123140126939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24278313866208328373671837 9104367699828123140126939)
    ·
      refine ⟨13656551549742184710190409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9104367699828123140126939 13656551549742184710190409)
      ·
        refine ⟨10242413662306638532642807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13656551549742184710190409 10242413662306638532642807)
        ·
          refine ⟨15363620493459957798964211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10242413662306638532642807 15363620493459957798964211)
          ·
            refine ⟨23045430740189936698446317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15363620493459957798964211 23045430740189936698446317)
            ·
              refine ⟨8642036527571226261917369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23045430740189936698446317 8642036527571226261917369)
              ·
                refine ⟨6481527395678419696438027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8642036527571226261917369 6481527395678419696438027)
                ·
                  refine ⟨9722291093517629544657041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6481527395678419696438027 9722291093517629544657041)
                  ·
                    refine ⟨7291718320138222158492781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9722291093517629544657041 7291718320138222158492781)
                    ·
                      refine ⟨2734394370051833309434793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7291718320138222158492781 2734394370051833309434793)
                      ·
                        rfl

theorem cell23_5325214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_5325214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5325214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5325214 prefixEnd_5325214 := by exact prefixLift 5325214
  have htrace : WordTrace (prefixWord ++ tailWord_5325214) baseStart_5325214 baseEnd_5325214 := by
    simpa [prefixWord, tailWord_5325214, baseEnd_5325214] using wordTrace_append hprefix tailTrace_5325214
  have hstable : (prefixWord ++ tailWord_5325214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5325214).length < 2 ^ (prefixWord ++ tailWord_5325214).sum := by decide
  have hdescent : baseEnd_5325214 < baseStart_5325214 := by decide
  rcases family_descends (prefixWord ++ tailWord_5325214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5325244 : List Nat := [2, 2, 2, 4, 1, 2, 2, 2, 2, 1, 3]
def baseStart_5325244 : Nat := 118140960795 + 5325244 * 2 ^ 59
def prefixEnd_5325244 : Nat := 4983230072969 + 3 ^ 40 * 5325244 * 2
def baseEnd_5325244 : Nat := 2734409774471468192059655

theorem tailTrace_5325244 : CollatzResearch.WordTrace tailWord_5325244 prefixEnd_5325244 2734409774471468192059655 := by
  unfold tailWord_5325244
  simp only [CollatzResearch.WordTrace]
  refine ⟨97113802559778971056483393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129485070079705294741977857 97113802559778971056483393)
  ·
    refine ⟨72835351919834228292362545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97113802559778971056483393 72835351919834228292362545)
    ·
      refine ⟨54626513939875671219271909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72835351919834228292362545 54626513939875671219271909)
      ·
        refine ⟨10242471363726688353613483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54626513939875671219271909 10242471363726688353613483)
        ·
          refine ⟨15363707045590032530420225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10242471363726688353613483 15363707045590032530420225)
          ·
            refine ⟨11522780284192524397815169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15363707045590032530420225 11522780284192524397815169)
            ·
              refine ⟨8642085213144393298361377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11522780284192524397815169 8642085213144393298361377)
              ·
                refine ⟨6481563909858294973771033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8642085213144393298361377 6481563909858294973771033)
                ·
                  refine ⟨4861172932393721230328275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6481563909858294973771033 4861172932393721230328275)
                  ·
                    refine ⟨7291759398590581845492413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4861172932393721230328275 7291759398590581845492413)
                    ·
                      refine ⟨2734409774471468192059655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7291759398590581845492413 2734409774471468192059655)
                      ·
                        rfl

theorem cell23_5325244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_5325244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5325244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5325244 prefixEnd_5325244 := by exact prefixLift 5325244
  have htrace : WordTrace (prefixWord ++ tailWord_5325244) baseStart_5325244 baseEnd_5325244 := by
    simpa [prefixWord, tailWord_5325244, baseEnd_5325244] using wordTrace_append hprefix tailTrace_5325244
  have hstable : (prefixWord ++ tailWord_5325244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5325244).length < 2 ^ (prefixWord ++ tailWord_5325244).sum := by decide
  have hdescent : baseEnd_5325244 < baseStart_5325244 := by decide
  rcases family_descends (prefixWord ++ tailWord_5325244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5325260 : List Nat := [2, 2, 1, 4, 3, 1, 1, 1, 2, 6]
def baseStart_5325260 : Nat := 118140960795 + 5325260 * 2 ^ 59
def prefixEnd_5325260 : Nat := 4983230072969 + 3 ^ 40 * 5325260 * 2
def baseEnd_5325260 : Nat := 911472663387313376486527

theorem tailTrace_5325260 : CollatzResearch.WordTrace tailWord_5325260 prefixEnd_5325260 911472663387313376486527 := by
  unfold tailWord_5325260
  simp only [CollatzResearch.WordTrace]
  refine ⟨97114094343749988422774617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129485459124999984563699489 97114094343749988422774617)
  ·
    refine ⟨72835570757812491317080963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97114094343749988422774617 72835570757812491317080963)
    ·
      refine ⟨109253356136718736975621445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72835570757812491317080963 109253356136718736975621445)
      ·
        refine ⟨20485004275634763182929021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 109253356136718736975621445 20485004275634763182929021)
        ·
          refine ⟨7681876603363036193598383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20485004275634763182929021 7681876603363036193598383)
          ·
            refine ⟨11522814905044554290397575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7681876603363036193598383 11522814905044554290397575)
            ·
              refine ⟨17284222357566831435596363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11522814905044554290397575 17284222357566831435596363)
              ·
                refine ⟨25926333536350247153394545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17284222357566831435596363 25926333536350247153394545)
                ·
                  refine ⟨19444750152262685365045909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25926333536350247153394545 19444750152262685365045909)
                  ·
                    refine ⟨911472663387313376486527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19444750152262685365045909 911472663387313376486527)
                    ·
                      rfl

theorem cell23_5325260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 1, 2, 6].length) (baseStart_5325260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5325260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5325260 prefixEnd_5325260 := by exact prefixLift 5325260
  have htrace : WordTrace (prefixWord ++ tailWord_5325260) baseStart_5325260 baseEnd_5325260 := by
    simpa [prefixWord, tailWord_5325260, baseEnd_5325260] using wordTrace_append hprefix tailTrace_5325260
  have hstable : (prefixWord ++ tailWord_5325260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5325260).length < 2 ^ (prefixWord ++ tailWord_5325260).sum := by decide
  have hdescent : baseEnd_5325260 < baseStart_5325260 := by decide
  rcases family_descends (prefixWord ++ tailWord_5325260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5325273 : List Nat := [1, 2, 1, 2, 4, 1, 3, 2, 7]
def baseStart_5325273 : Nat := 118140960795 + 5325273 * 2 ^ 59
def prefixEnd_5325273 : Nat := 4983230072969 + 3 ^ 40 * 5325273 * 2
def baseEnd_5325273 : Nat := 303824962823383175399669

theorem tailTrace_5325273 : CollatzResearch.WordTrace tailWord_5325273 prefixEnd_5325273 303824962823383175399669 := by
  unfold tailWord_5325273
  simp only [CollatzResearch.WordTrace]
  refine ⟨194228662836452880065772473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129485775224301920043848315 194228662836452880065772473)
  ·
    refine ⟨145671497127339660049329355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194228662836452880065772473 145671497127339660049329355)
    ·
      refine ⟨218507245691009490073994033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145671497127339660049329355 218507245691009490073994033)
      ·
        refine ⟨163880434268257117555495525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 218507245691009490073994033 163880434268257117555495525)
        ·
          refine ⟨30727581425298209541655411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 163880434268257117555495525 30727581425298209541655411)
          ·
            refine ⟨46091372137947314312483117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30727581425298209541655411 46091372137947314312483117)
            ·
              refine ⟨17284264551730242867181169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46091372137947314312483117 17284264551730242867181169)
              ·
                refine ⟨12963198413797682150385877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17284264551730242867181169 12963198413797682150385877)
                ·
                  refine ⟨303824962823383175399669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12963198413797682150385877 303824962823383175399669)
                  ·
                    rfl

theorem cell23_5325273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 2, 7].length) (baseStart_5325273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5325273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5325273 prefixEnd_5325273 := by exact prefixLift 5325273
  have htrace : WordTrace (prefixWord ++ tailWord_5325273) baseStart_5325273 baseEnd_5325273 := by
    simpa [prefixWord, tailWord_5325273, baseEnd_5325273] using wordTrace_append hprefix tailTrace_5325273
  have hstable : (prefixWord ++ tailWord_5325273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5325273).length < 2 ^ (prefixWord ++ tailWord_5325273).sum := by decide
  have hdescent : baseEnd_5325273 < baseStart_5325273 := by decide
  rcases family_descends (prefixWord ++ tailWord_5325273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5325301 : List Nat := [1, 3, 5, 1, 2, 1, 1, 1, 4, 2, 2]
def baseStart_5325301 : Nat := 118140960795 + 5325301 * 2 ^ 59
def prefixEnd_5325301 : Nat := 4983230072969 + 3 ^ 40 * 5325301 * 2
def baseEnd_5325301 : Nat := 2734439042868774469046893

theorem tailTrace_5325301 : CollatzResearch.WordTrace tailWord_5325301 prefixEnd_5325301 2734439042868774469046893 := by
  unfold tailWord_5325301
  simp only [CollatzResearch.WordTrace]
  refine ⟨194229684080351440847791757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129486456053567627231861171 194229684080351440847791757)
  ·
    refine ⟨72836131530131790317921909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 194229684080351440847791757 72836131530131790317921909)
    ·
      refine ⟨6828387330949855342305179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 72836131530131790317921909 6828387330949855342305179)
      ·
        refine ⟨10242580996424783013457769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6828387330949855342305179 10242580996424783013457769)
        ·
          refine ⟨7681935747318587260093327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10242580996424783013457769 7681935747318587260093327)
          ·
            refine ⟨11522903620977880890139991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7681935747318587260093327 11522903620977880890139991)
            ·
              refine ⟨17284355431466821335209987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11522903620977880890139991 17284355431466821335209987)
              ·
                refine ⟨25926533147200232002814981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17284355431466821335209987 25926533147200232002814981)
                ·
                  refine ⟨4861224965100043500527809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25926533147200232002814981 4861224965100043500527809)
                  ·
                    refine ⟨3645918723825032625395857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4861224965100043500527809 3645918723825032625395857)
                    ·
                      refine ⟨2734439042868774469046893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3645918723825032625395857 2734439042868774469046893)
                      ·
                        rfl

theorem cell23_5325301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 1, 4, 2, 2].length) (baseStart_5325301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5325301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5325301 prefixEnd_5325301 := by exact prefixLift 5325301
  have htrace : WordTrace (prefixWord ++ tailWord_5325301) baseStart_5325301 baseEnd_5325301 := by
    simpa [prefixWord, tailWord_5325301, baseEnd_5325301] using wordTrace_append hprefix tailTrace_5325301
  have hstable : (prefixWord ++ tailWord_5325301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5325301).length < 2 ^ (prefixWord ++ tailWord_5325301).sum := by decide
  have hdescent : baseEnd_5325301 < baseStart_5325301 := by decide
  rcases family_descends (prefixWord ++ tailWord_5325301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5325318 : List Nat := [6, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2]
def baseStart_5325318 : Nat := 118140960795 + 5325318 * 2 ^ 59
def prefixEnd_5325318 : Nat := 4983230072969 + 3 ^ 40 * 5325318 * 2
def baseEnd_5325318 : Nat := 2734447772039900902534315

theorem tailTrace_5325318 : CollatzResearch.WordTrace tailWord_5325318 prefixEnd_5325318 2734447772039900902534315 := by
  unfold tailWord_5325318
  simp only [CollatzResearch.WordTrace]
  refine ⟨6069697003790307898473769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 129486869414193235167440405 6069697003790307898473769)
  ·
    refine ⟨4552272752842730923855327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6069697003790307898473769 4552272752842730923855327)
    ·
      refine ⟨6828409129264096385782991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4552272752842730923855327 6828409129264096385782991)
      ·
        refine ⟨10242613693896144578674487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6828409129264096385782991 10242613693896144578674487)
        ·
          refine ⟨15363920540844216868011731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10242613693896144578674487 15363920540844216868011731)
          ·
            refine ⟨23045880811266325302017597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15363920540844216868011731 23045880811266325302017597)
            ·
              refine ⟨8642205304224871988256599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23045880811266325302017597 8642205304224871988256599)
              ·
                refine ⟨12963307956337307982384899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8642205304224871988256599 12963307956337307982384899)
                ·
                  refine ⟨19444961934505961973577349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12963307956337307982384899 19444961934505961973577349)
                  ·
                    refine ⟨3645930362719867870045753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19444961934505961973577349 3645930362719867870045753)
                    ·
                      refine ⟨2734447772039900902534315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3645930362719867870045753 2734447772039900902534315)
                      ·
                        rfl

theorem cell23_5325318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2].length) (baseStart_5325318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5325318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5325318 prefixEnd_5325318 := by exact prefixLift 5325318
  have htrace : WordTrace (prefixWord ++ tailWord_5325318) baseStart_5325318 baseEnd_5325318 := by
    simpa [prefixWord, tailWord_5325318, baseEnd_5325318] using wordTrace_append hprefix tailTrace_5325318
  have hstable : (prefixWord ++ tailWord_5325318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5325318).length < 2 ^ (prefixWord ++ tailWord_5325318).sum := by decide
  have hdescent : baseEnd_5325318 < baseStart_5325318 := by decide
  rcases family_descends (prefixWord ++ tailWord_5325318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5325333 : List Nat := [1, 3, 2, 1, 3, 1, 1, 1, 2, 8]
def baseStart_5325333 : Nat := 118140960795 + 5325333 * 2 ^ 59
def prefixEnd_5325333 : Nat := 4983230072969 + 3 ^ 40 * 5325333 * 2
def baseEnd_5325333 : Nat := 911485158083239447948915

theorem tailTrace_5325333 : CollatzResearch.WordTrace tailWord_5325333 prefixEnd_5325333 911485158083239447948915 := by
  unfold tailWord_5325333
  simp only [CollatzResearch.WordTrace]
  refine ⟨194230851216235510312956653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129487234144157006875304435 194230851216235510312956653)
  ·
    refine ⟨72836569206088316367358745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 194230851216235510312956653 72836569206088316367358745)
    ·
      refine ⟨54627426904566237275519059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72836569206088316367358745 54627426904566237275519059)
      ·
        refine ⟨81941140356849355913278589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54627426904566237275519059 81941140356849355913278589)
        ·
          refine ⟨30727927633818508467479471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81941140356849355913278589 30727927633818508467479471)
          ·
            refine ⟨46091891450727762701219207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30727927633818508467479471 46091891450727762701219207)
            ·
              refine ⟨69137837176091644051828811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46091891450727762701219207 69137837176091644051828811)
              ·
                refine ⟨103706755764137466077743217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69137837176091644051828811 103706755764137466077743217)
                ·
                  refine ⟨77780066823103099558307413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 103706755764137466077743217 77780066823103099558307413)
                  ·
                    refine ⟨911485158083239447948915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 77780066823103099558307413 911485158083239447948915)
                    ·
                      rfl

theorem cell23_5325333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 2, 8].length) (baseStart_5325333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5325333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5325333 prefixEnd_5325333 := by exact prefixLift 5325333
  have htrace : WordTrace (prefixWord ++ tailWord_5325333) baseStart_5325333 baseEnd_5325333 := by
    simpa [prefixWord, tailWord_5325333, baseEnd_5325333] using wordTrace_append hprefix tailTrace_5325333
  have hstable : (prefixWord ++ tailWord_5325333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5325333).length < 2 ^ (prefixWord ++ tailWord_5325333).sum := by decide
  have hdescent : baseEnd_5325333 < baseStart_5325333 := by decide
  rcases family_descends (prefixWord ++ tailWord_5325333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5325340 : List Nat := [2, 2, 3, 1, 2, 2, 2, 1, 1, 3, 4]
def baseStart_5325340 : Nat := 118140960795 + 5325340 * 2 ^ 59
def prefixEnd_5325340 : Nat := 4983230072969 + 3 ^ 40 * 5325340 * 2
def baseEnd_5325340 : Nat := 2734459068614299816459213

theorem tailTrace_5325340 : CollatzResearch.WordTrace tailWord_5325340 prefixEnd_5325340 2734459068614299816459213 := by
  unfold tailWord_5325340
  simp only [CollatzResearch.WordTrace]
  refine ⟨97115553263605075254230737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129487404351473433672307649 97115553263605075254230737)
  ·
    refine ⟨72836664947703806440673053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97115553263605075254230737 72836664947703806440673053)
    ·
      refine ⟨27313749355388927415252395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72836664947703806440673053 27313749355388927415252395)
      ·
        refine ⟨40970624033083391122878593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27313749355388927415252395 40970624033083391122878593)
        ·
          refine ⟨30727968024812543342158945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40970624033083391122878593 30727968024812543342158945)
          ·
            refine ⟨23045976018609407506619209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30727968024812543342158945 23045976018609407506619209)
            ·
              refine ⟨17284482013957055629964407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23045976018609407506619209 17284482013957055629964407)
              ·
                refine ⟨25926723020935583444946611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17284482013957055629964407 25926723020935583444946611)
                ·
                  refine ⟨38890084531403375167419917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25926723020935583444946611 38890084531403375167419917)
                  ·
                    refine ⟨14583781699276265687782469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38890084531403375167419917 14583781699276265687782469)
                    ·
                      refine ⟨2734459068614299816459213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14583781699276265687782469 2734459068614299816459213)
                      ·
                        rfl

theorem cell23_5325340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 1, 1, 3, 4].length) (baseStart_5325340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5325340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5325340 prefixEnd_5325340 := by exact prefixLift 5325340
  have htrace : WordTrace (prefixWord ++ tailWord_5325340) baseStart_5325340 baseEnd_5325340 := by
    simpa [prefixWord, tailWord_5325340, baseEnd_5325340] using wordTrace_append hprefix tailTrace_5325340
  have hstable : (prefixWord ++ tailWord_5325340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5325340).length < 2 ^ (prefixWord ++ tailWord_5325340).sum := by decide
  have hdescent : baseEnd_5325340 < baseStart_5325340 := by decide
  rcases family_descends (prefixWord ++ tailWord_5325340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5325343 : List Nat := [1, 1, 2, 4, 1, 1, 1, 2, 2, 3, 5]
def baseStart_5325343 : Nat := 118140960795 + 5325343 * 2 ^ 59
def prefixEnd_5325343 : Nat := 4983230072969 + 3 ^ 40 * 5325343 * 2
def baseEnd_5325343 : Nat := 2734460609056263304721699

theorem tailTrace_5325343 : CollatzResearch.WordTrace tailWord_5325343 prefixEnd_5325343 2734460609056263304721699 := by
  unfold tailWord_5325343
  simp only [CollatzResearch.WordTrace]
  refine ⟨194231215946199282020820683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129487477297466188013880455 194231215946199282020820683)
  ·
    refine ⟨291346823919298923031231025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194231215946199282020820683 291346823919298923031231025)
    ·
      refine ⟨218510117939474192273423269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 291346823919298923031231025 218510117939474192273423269)
      ·
        refine ⟨40970647113651411051266863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 218510117939474192273423269 40970647113651411051266863)
        ·
          refine ⟨61455970670477116576900295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40970647113651411051266863 61455970670477116576900295)
          ·
            refine ⟨92183956005715674865350443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61455970670477116576900295 92183956005715674865350443)
            ·
              refine ⟨138275934008573512298025665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92183956005715674865350443 138275934008573512298025665)
              ·
                refine ⟨103706950506430134223519249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 138275934008573512298025665 103706950506430134223519249)
                ·
                  refine ⟨77780212879822600667639437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 103706950506430134223519249 77780212879822600667639437)
                  ·
                    refine ⟨29167579829933475250364789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 77780212879822600667639437 29167579829933475250364789)
                    ·
                      refine ⟨2734460609056263304721699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29167579829933475250364789 2734460609056263304721699)
                      ·
                        rfl

theorem cell23_5325343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_5325343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5325343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5325343 prefixEnd_5325343 := by exact prefixLift 5325343
  have htrace : WordTrace (prefixWord ++ tailWord_5325343) baseStart_5325343 baseEnd_5325343 := by
    simpa [prefixWord, tailWord_5325343, baseEnd_5325343] using wordTrace_append hprefix tailTrace_5325343
  have hstable : (prefixWord ++ tailWord_5325343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5325343).length < 2 ^ (prefixWord ++ tailWord_5325343).sum := by decide
  have hdescent : baseEnd_5325343 < baseStart_5325343 := by decide
  rcases family_descends (prefixWord ++ tailWord_5325343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5325360 : List Nat := [2, 1, 1, 1, 2, 3, 3, 1, 4, 2, 3]
def baseStart_5325360 : Nat := 118140960795 + 5325360 * 2 ^ 59
def prefixEnd_5325360 : Nat := 4983230072969 + 3 ^ 40 * 5325360 * 2
def baseEnd_5325360 : Nat := 2734469338227389738209121

theorem tailTrace_5325360 : CollatzResearch.WordTrace tailWord_5325360 prefixEnd_5325360 2734469338227389738209121 := by
  unfold tailWord_5325360
  simp only [CollatzResearch.WordTrace]
  refine ⟨97115917993568846962094767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129487890658091795949459689 97115917993568846962094767)
  ·
    refine ⟨145673876990353270443142151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97115917993568846962094767 145673876990353270443142151)
    ·
      refine ⟨218510815485529905664713227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145673876990353270443142151 218510815485529905664713227)
      ·
        refine ⟨327766223228294858497069841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218510815485529905664713227 327766223228294858497069841)
        ·
          refine ⟨245824667421221143872802381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 327766223228294858497069841 245824667421221143872802381)
          ·
            refine ⟨92184250282957928952300893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 245824667421221143872802381 92184250282957928952300893)
            ·
              refine ⟨34569093856109223357112835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92184250282957928952300893 34569093856109223357112835)
              ·
                refine ⟨51853640784163835035669253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34569093856109223357112835 51853640784163835035669253)
                ·
                  refine ⟨9722557647030719069187985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51853640784163835035669253 9722557647030719069187985)
                  ·
                    refine ⟨7291918235273039301890989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9722557647030719069187985 7291918235273039301890989)
                    ·
                      refine ⟨2734469338227389738209121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7291918235273039301890989 2734469338227389738209121)
                      ·
                        rfl

theorem cell23_5325360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 1, 4, 2, 3].length) (baseStart_5325360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5325360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5325360 prefixEnd_5325360 := by exact prefixLift 5325360
  have htrace : WordTrace (prefixWord ++ tailWord_5325360) baseStart_5325360 baseEnd_5325360 := by
    simpa [prefixWord, tailWord_5325360, baseEnd_5325360] using wordTrace_append hprefix tailTrace_5325360
  have hstable : (prefixWord ++ tailWord_5325360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5325360).length < 2 ^ (prefixWord ++ tailWord_5325360).sum := by decide
  have hdescent : baseEnd_5325360 < baseStart_5325360 := by decide
  rcases family_descends (prefixWord ++ tailWord_5325360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5325363 : List Nat := [1, 1, 1, 2, 4, 2, 1, 3, 8]
def baseStart_5325363 : Nat := 118140960795 + 5325363 * 2 ^ 59
def prefixEnd_5325363 : Nat := 4983230072969 + 3 ^ 40 * 5325363 * 2
def baseEnd_5325363 : Nat := 303830097629928136274623

theorem tailTrace_5325363 : CollatzResearch.WordTrace tailWord_5325363 prefixEnd_5325363 303830097629928136274623 := by
  unfold tailWord_5325363
  simp only [CollatzResearch.WordTrace]
  refine ⟨194231945406126825436548743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129487963604084550291032495 194231945406126825436548743)
  ·
    refine ⟨291347918109190238154823115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194231945406126825436548743 291347918109190238154823115)
    ·
      refine ⟨437021877163785357232234673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 291347918109190238154823115 437021877163785357232234673)
      ·
        refine ⟨327766407872839017924176005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 437021877163785357232234673 327766407872839017924176005)
        ·
          refine ⟨61456201476157315860783001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 327766407872839017924176005 61456201476157315860783001)
          ·
            refine ⟨46092151107117986895587251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61456201476157315860783001 46092151107117986895587251)
            ·
              refine ⟨69138226660676980343380877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46092151107117986895587251 69138226660676980343380877)
              ·
                refine ⟨25926834997753867628767829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69138226660676980343380877 25926834997753867628767829)
                ·
                  refine ⟨303830097629928136274623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25926834997753867628767829 303830097629928136274623)
                  ·
                    rfl

theorem cell23_5325363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 3, 8].length) (baseStart_5325363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5325363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5325363 prefixEnd_5325363 := by exact prefixLift 5325363
  have htrace : WordTrace (prefixWord ++ tailWord_5325363) baseStart_5325363 baseEnd_5325363 := by
    simpa [prefixWord, tailWord_5325363, baseEnd_5325363] using wordTrace_append hprefix tailTrace_5325363
  have hstable : (prefixWord ++ tailWord_5325363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5325363).length < 2 ^ (prefixWord ++ tailWord_5325363).sum := by decide
  have hdescent : baseEnd_5325363 < baseStart_5325363 := by decide
  rcases family_descends (prefixWord ++ tailWord_5325363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5325364 : List Nat := [2, 5, 1, 3, 1, 1, 1, 1, 1, 2, 5]
def baseStart_5325364 : Nat := 118140960795 + 5325364 * 2 ^ 59
def prefixEnd_5325364 : Nat := 4983230072969 + 3 ^ 40 * 5325364 * 2
def baseEnd_5325364 : Nat := 2734471392150007722559103

theorem tailTrace_5325364 : CollatzResearch.WordTrace tailWord_5325364 prefixEnd_5325364 2734471392150007722559103 := by
  unfold tailWord_5325364
  simp only [CollatzResearch.WordTrace]
  refine ⟨97115990939561601303667573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129487987919415468404890097 97115990939561601303667573)
  ·
    refine ⟨9104624150583900122218835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 97115990939561601303667573 9104624150583900122218835)
    ·
      refine ⟨13656936225875850183328253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9104624150583900122218835 13656936225875850183328253)
      ·
        refine ⟨5121351084703443818748095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13656936225875850183328253 5121351084703443818748095)
        ·
          refine ⟨7682026627055165728122143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5121351084703443818748095 7682026627055165728122143)
          ·
            refine ⟨11523039940582748592183215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7682026627055165728122143 11523039940582748592183215)
            ·
              refine ⟨17284559910874122888274823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11523039940582748592183215 17284559910874122888274823)
              ·
                refine ⟨25926839866311184332412235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17284559910874122888274823 25926839866311184332412235)
                ·
                  refine ⟨38890259799466776498618353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25926839866311184332412235 38890259799466776498618353)
                  ·
                    refine ⟨29167694849600082373963765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38890259799466776498618353 29167694849600082373963765)
                    ·
                      refine ⟨2734471392150007722559103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29167694849600082373963765 2734471392150007722559103)
                      ·
                        rfl

theorem cell23_5325364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_5325364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5325364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5325364 prefixEnd_5325364 := by exact prefixLift 5325364
  have htrace : WordTrace (prefixWord ++ tailWord_5325364) baseStart_5325364 baseEnd_5325364 := by
    simpa [prefixWord, tailWord_5325364, baseEnd_5325364] using wordTrace_append hprefix tailTrace_5325364
  have hstable : (prefixWord ++ tailWord_5325364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5325364).length < 2 ^ (prefixWord ++ tailWord_5325364).sum := by decide
  have hdescent : baseEnd_5325364 < baseStart_5325364 := by decide
  rcases family_descends (prefixWord ++ tailWord_5325364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5325390 : List Nat := [4, 1, 1, 1, 1, 2, 2, 1, 2, 5, 3]
def baseStart_5325390 : Nat := 118140960795 + 5325390 * 2 ^ 59
def prefixEnd_5325390 : Nat := 4983230072969 + 3 ^ 40 * 5325390 * 2
def baseEnd_5325390 : Nat := 2734484742647024620833983

theorem tailTrace_5325390 : CollatzResearch.WordTrace tailWord_5325390 prefixEnd_5325390 2734484742647024620833983 := by
  unfold tailWord_5325390
  simp only [CollatzResearch.WordTrace]
  refine ⟨24279116272128626130972703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129488620118019339365187749 24279116272128626130972703)
  ·
    refine ⟨36418674408192939196459055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24279116272128626130972703 36418674408192939196459055)
    ·
      refine ⟨54628011612289408794688583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36418674408192939196459055 54628011612289408794688583)
      ·
        refine ⟨81942017418434113192032875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54628011612289408794688583 81942017418434113192032875)
        ·
          refine ⟨122913026127651169788049313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81942017418434113192032875 122913026127651169788049313)
          ·
            refine ⟨92184769595738377341036985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122913026127651169788049313 92184769595738377341036985)
            ·
              refine ⟨69138577196803783005777739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92184769595738377341036985 69138577196803783005777739)
              ·
                refine ⟨103707865795205674508666609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69138577196803783005777739 103707865795205674508666609)
                ·
                  refine ⟨77780899346404255881499957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 103707865795205674508666609 77780899346404255881499957)
                  ·
                    refine ⟨7291959313725398988890621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 77780899346404255881499957 7291959313725398988890621)
                    ·
                      refine ⟨2734484742647024620833983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7291959313725398988890621 2734484742647024620833983)
                      ·
                        rfl

theorem cell23_5325390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 2, 5, 3].length) (baseStart_5325390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5325390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5325390 prefixEnd_5325390 := by exact prefixLift 5325390
  have htrace : WordTrace (prefixWord ++ tailWord_5325390) baseStart_5325390 baseEnd_5325390 := by
    simpa [prefixWord, tailWord_5325390, baseEnd_5325390] using wordTrace_append hprefix tailTrace_5325390
  have hstable : (prefixWord ++ tailWord_5325390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5325390).length < 2 ^ (prefixWord ++ tailWord_5325390).sum := by decide
  have hdescent : baseEnd_5325390 < baseStart_5325390 := by decide
  rcases family_descends (prefixWord ++ tailWord_5325390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5325440 : List Nat := [2, 1, 1, 2, 1, 5, 1, 3, 1, 6]
def baseStart_5325440 : Nat := 118140960795 + 5325440 * 2 ^ 59
def prefixEnd_5325440 : Nat := 4983230072969 + 3 ^ 40 * 5325440 * 2
def baseEnd_5325440 : Nat := 911503472226583141736251

theorem tailTrace_5325440 : CollatzResearch.WordTrace tailWord_5325440 prefixEnd_5325440 911503472226583141736251 := by
  unfold tailWord_5325440
  simp only [CollatzResearch.WordTrace]
  refine ⟨97117376913423933793550887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129489835884565245058067849 97117376913423933793550887)
  ·
    refine ⟨145676065370135900690326331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97117376913423933793550887 145676065370135900690326331)
    ·
      refine ⟨218514098055203851035489497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145676065370135900690326331 218514098055203851035489497)
      ·
        refine ⟨163885573541402888276617123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 218514098055203851035489497 163885573541402888276617123)
        ·
          refine ⟨245828360312104332414925685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163885573541402888276617123 245828360312104332414925685)
          ·
            refine ⟨23046408779259781163899283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 245828360312104332414925685 23046408779259781163899283)
            ·
              refine ⟨34569613168889671745848925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23046408779259781163899283 34569613168889671745848925)
              ·
                refine ⟨12963604938333626904693347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34569613168889671745848925 12963604938333626904693347)
                ·
                  refine ⟨19445407407500440357040021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12963604938333626904693347 19445407407500440357040021)
                  ·
                    refine ⟨911503472226583141736251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19445407407500440357040021 911503472226583141736251)
                    ·
                      rfl

theorem cell23_5325440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 3, 1, 6].length) (baseStart_5325440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5325440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5325440 prefixEnd_5325440 := by exact prefixLift 5325440
  have htrace : WordTrace (prefixWord ++ tailWord_5325440) baseStart_5325440 baseEnd_5325440 := by
    simpa [prefixWord, tailWord_5325440, baseEnd_5325440] using wordTrace_append hprefix tailTrace_5325440
  have hstable : (prefixWord ++ tailWord_5325440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5325440).length < 2 ^ (prefixWord ++ tailWord_5325440).sum := by decide
  have hdescent : baseEnd_5325440 < baseStart_5325440 := by decide
  rcases family_descends (prefixWord ++ tailWord_5325440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5325447 : List Nat := [1, 1, 4, 2, 1, 2, 2, 4, 1, 1, 4]
def baseStart_5325447 : Nat := 118140960795 + 5325447 * 2 ^ 59
def prefixEnd_5325447 : Nat := 4983230072969 + 3 ^ 40 * 5325447 * 2
def baseEnd_5325447 : Nat := 2734514011044330897821221

theorem tailTrace_5325447 : CollatzResearch.WordTrace tailWord_5325447 prefixEnd_5325447 2734514011044330897821221 := by
  unfold tailWord_5325447
  simp only [CollatzResearch.WordTrace]
  refine ⟨194235009137822507782606595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129490006091881671855071063 194235009137822507782606595)
  ·
    refine ⟨291352513706733761673909893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194235009137822507782606595 291352513706733761673909893)
    ·
      refine ⟨54628596320012580313858105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 291352513706733761673909893 54628596320012580313858105)
      ·
        refine ⟨40971447240009435235393579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54628596320012580313858105 40971447240009435235393579)
        ·
          refine ⟨61457170860014152853090369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40971447240009435235393579 61457170860014152853090369)
          ·
            refine ⟨46092878145010614639817777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61457170860014152853090369 46092878145010614639817777)
            ·
              refine ⟨34569658608757960979863333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46092878145010614639817777 34569658608757960979863333)
              ·
                refine ⟨6481810989142117683724375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34569658608757960979863333 6481810989142117683724375)
                ·
                  refine ⟨9722716483713176525586563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6481810989142117683724375 9722716483713176525586563)
                  ·
                    refine ⟨14584074725569764788379845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9722716483713176525586563 14584074725569764788379845)
                    ·
                      refine ⟨2734514011044330897821221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14584074725569764788379845 2734514011044330897821221)
                      ·
                        rfl

theorem cell23_5325447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 4, 1, 1, 4].length) (baseStart_5325447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5325447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5325447 prefixEnd_5325447 := by exact prefixLift 5325447
  have htrace : WordTrace (prefixWord ++ tailWord_5325447) baseStart_5325447 baseEnd_5325447 := by
    simpa [prefixWord, tailWord_5325447, baseEnd_5325447] using wordTrace_append hprefix tailTrace_5325447
  have hstable : (prefixWord ++ tailWord_5325447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5325447).length < 2 ^ (prefixWord ++ tailWord_5325447).sum := by decide
  have hdescent : baseEnd_5325447 < baseStart_5325447 := by decide
  rcases family_descends (prefixWord ++ tailWord_5325447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5325458 : List Nat := [3, 2, 3, 1, 2, 2, 2, 3, 1, 1, 3]
def baseStart_5325458 : Nat := 118140960795 + 5325458 * 2 ^ 59
def prefixEnd_5325458 : Nat := 4983230072969 + 3 ^ 40 * 5325458 * 2
def baseEnd_5325458 : Nat := 2734519659331530354783671

theorem tailTrace_5325458 : CollatzResearch.WordTrace tailWord_5325458 prefixEnd_5325458 2734519659331530354783671 := by
  unfold tailWord_5325458
  simp only [CollatzResearch.WordTrace]
  refine ⟨48558852585195664165314257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129490273560521771107504685 48558852585195664165314257)
  ·
    refine ⟨36419139438896748123985693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48558852585195664165314257 36419139438896748123985693)
    ·
      refine ⟨13657177289586280546494635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36419139438896748123985693 13657177289586280546494635)
      ·
        refine ⟨20485765934379420819741953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13657177289586280546494635 20485765934379420819741953)
        ·
          refine ⟨15364324450784565614806465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20485765934379420819741953 15364324450784565614806465)
          ·
            refine ⟨11523243338088424211104849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15364324450784565614806465 11523243338088424211104849)
            ·
              refine ⟨8642432503566318158328637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11523243338088424211104849 8642432503566318158328637)
              ·
                refine ⟨3240912188837369309373239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8642432503566318158328637 3240912188837369309373239)
                ·
                  refine ⟨4861368283256053964059859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3240912188837369309373239 4861368283256053964059859)
                  ·
                    refine ⟨7292052424884080946089789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4861368283256053964059859 7292052424884080946089789)
                    ·
                      refine ⟨2734519659331530354783671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7292052424884080946089789 2734519659331530354783671)
                      ·
                        rfl

theorem cell23_5325458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 3, 1, 1, 3].length) (baseStart_5325458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5325458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5325458 prefixEnd_5325458 := by exact prefixLift 5325458
  have htrace : WordTrace (prefixWord ++ tailWord_5325458) baseStart_5325458 baseEnd_5325458 := by
    simpa [prefixWord, tailWord_5325458, baseEnd_5325458] using wordTrace_append hprefix tailTrace_5325458
  have hstable : (prefixWord ++ tailWord_5325458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5325458).length < 2 ^ (prefixWord ++ tailWord_5325458).sum := by decide
  have hdescent : baseEnd_5325458 < baseStart_5325458 := by decide
  rcases family_descends (prefixWord ++ tailWord_5325458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5325464 : List Nat := [2, 1, 2, 4, 1, 1, 1, 2, 5, 2, 2]
def baseStart_5325464 : Nat := 118140960795 + 5325464 * 2 ^ 59
def prefixEnd_5325464 : Nat := 4983230072969 + 3 ^ 40 * 5325464 * 2
def baseEnd_5325464 : Nat := 2734522740215457331308643

theorem tailTrace_5325464 : CollatzResearch.WordTrace tailWord_5325464 prefixEnd_5325464 2734522740215457331308643 := by
  unfold tailWord_5325464
  simp only [CollatzResearch.WordTrace]
  refine ⟨97117814589380459842987723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129490419452507279790650297 97117814589380459842987723)
  ·
    refine ⟨145676721884070689764481585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97117814589380459842987723 145676721884070689764481585)
    ·
      refine ⟨109257541413053017323361189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145676721884070689764481585 109257541413053017323361189)
      ·
        refine ⟨20485789014947440748130223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 109257541413053017323361189 20485789014947440748130223)
        ·
          refine ⟨30728683522421161122195335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20485789014947440748130223 30728683522421161122195335)
          ·
            refine ⟨46093025283631741683293003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30728683522421161122195335 46093025283631741683293003)
            ·
              refine ⟨69139537925447612524939505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46093025283631741683293003 69139537925447612524939505)
              ·
                refine ⟨51854653444085709393704629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69139537925447612524939505 51854653444085709393704629)
                ·
                  refine ⟨4861373760383035255659809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51854653444085709393704629 4861373760383035255659809)
                  ·
                    refine ⟨3646030320287276441744857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4861373760383035255659809 3646030320287276441744857)
                    ·
                      refine ⟨2734522740215457331308643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3646030320287276441744857 2734522740215457331308643)
                      ·
                        rfl

theorem cell23_5325464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 2, 5, 2, 2].length) (baseStart_5325464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5325464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5325464 prefixEnd_5325464 := by exact prefixLift 5325464
  have htrace : WordTrace (prefixWord ++ tailWord_5325464) baseStart_5325464 baseEnd_5325464 := by
    simpa [prefixWord, tailWord_5325464, baseEnd_5325464] using wordTrace_append hprefix tailTrace_5325464
  have hstable : (prefixWord ++ tailWord_5325464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5325464).length < 2 ^ (prefixWord ++ tailWord_5325464).sum := by decide
  have hdescent : baseEnd_5325464 < baseStart_5325464 := by decide
  rcases family_descends (prefixWord ++ tailWord_5325464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5325514 : List Nat := [3, 1, 2, 1, 4, 1, 1, 2, 4, 1, 3]
def baseStart_5325514 : Nat := 118140960795 + 5325514 * 2 ^ 59
def prefixEnd_5325514 : Nat := 4983230072969 + 3 ^ 40 * 5325514 * 2
def baseEnd_5325514 : Nat := 2734548414248182135683413

theorem tailTrace_5325514 : CollatzResearch.WordTrace tailWord_5325514 prefixEnd_5325514 2734548414248182135683413 := by
  unfold tailWord_5325514
  simp only [CollatzResearch.WordTrace]
  refine ⟨48559363207144944556323899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129491635219053185483530397 48559363207144944556323899)
  ·
    refine ⟨72839044810717416834485849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48559363207144944556323899 72839044810717416834485849)
    ·
      refine ⟨54629283608038062625864387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72839044810717416834485849 54629283608038062625864387)
      ·
        refine ⟨81943925412057093938796581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54629283608038062625864387 81943925412057093938796581)
        ·
          refine ⟨15364486014760705113524359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81943925412057093938796581 15364486014760705113524359)
          ·
            refine ⟨23046729022141057670286539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15364486014760705113524359 23046729022141057670286539)
            ·
              refine ⟨34570093533211586505429809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23046729022141057670286539 34570093533211586505429809)
              ·
                refine ⟨25927570149908689879072357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34570093533211586505429809 25927570149908689879072357)
                ·
                  refine ⟨4861419403107879352326067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25927570149908689879072357 4861419403107879352326067)
                  ·
                    refine ⟨7292129104661819028489101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4861419403107879352326067 7292129104661819028489101)
                    ·
                      refine ⟨2734548414248182135683413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7292129104661819028489101 2734548414248182135683413)
                      ·
                        rfl

theorem cell23_5325514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 2, 4, 1, 3].length) (baseStart_5325514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5325514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5325514 prefixEnd_5325514 := by exact prefixLift 5325514
  have htrace : WordTrace (prefixWord ++ tailWord_5325514) baseStart_5325514 baseEnd_5325514 := by
    simpa [prefixWord, tailWord_5325514, baseEnd_5325514] using wordTrace_append hprefix tailTrace_5325514
  have hstable : (prefixWord ++ tailWord_5325514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5325514).length < 2 ^ (prefixWord ++ tailWord_5325514).sum := by decide
  have hdescent : baseEnd_5325514 < baseStart_5325514 := by decide
  rcases family_descends (prefixWord ++ tailWord_5325514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5325532 : List Nat := [2, 2, 5, 1, 1, 2, 3, 2, 1, 2, 2]
def baseStart_5325532 : Nat := 118140960795 + 5325532 * 2 ^ 59
def prefixEnd_5325532 : Nat := 4983230072969 + 3 ^ 40 * 5325532 * 2
def baseEnd_5325532 : Nat := 2734557656899963065258331

theorem tailTrace_5325532 : CollatzResearch.WordTrace tailWord_5325532 prefixEnd_5325532 2734557656899963065258331 := by
  unfold tailWord_5325532
  simp only [CollatzResearch.WordTrace]
  refine ⟨97119054671257283649725425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129492072895009711532967233 97119054671257283649725425)
  ·
    refine ⟨72839291003442962737294069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97119054671257283649725425 72839291003442962737294069)
    ·
      refine ⟨6828683531572777756621319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 72839291003442962737294069 6828683531572777756621319)
      ·
        refine ⟨10243025297359166634931979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6828683531572777756621319 10243025297359166634931979)
        ·
          refine ⟨15364537946038749952397969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10243025297359166634931979 15364537946038749952397969)
          ·
            refine ⟨11523403459529062464298477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15364537946038749952397969 11523403459529062464298477)
            ·
              refine ⟨4321276297323398424111929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11523403459529062464298477 4321276297323398424111929)
              ·
                refine ⟨3240957222992548818083947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4321276297323398424111929 3240957222992548818083947)
                ·
                  refine ⟨4861435834488823227125921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3240957222992548818083947 4861435834488823227125921)
                  ·
                    refine ⟨3646076875866617420344441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4861435834488823227125921 3646076875866617420344441)
                    ·
                      refine ⟨2734557656899963065258331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3646076875866617420344441 2734557656899963065258331)
                      ·
                        rfl

theorem cell23_5325532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 3, 2, 1, 2, 2].length) (baseStart_5325532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5325532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5325532 prefixEnd_5325532 := by exact prefixLift 5325532
  have htrace : WordTrace (prefixWord ++ tailWord_5325532) baseStart_5325532 baseEnd_5325532 := by
    simpa [prefixWord, tailWord_5325532, baseEnd_5325532] using wordTrace_append hprefix tailTrace_5325532
  have hstable : (prefixWord ++ tailWord_5325532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5325532).length < 2 ^ (prefixWord ++ tailWord_5325532).sum := by decide
  have hdescent : baseEnd_5325532 < baseStart_5325532 := by decide
  rcases family_descends (prefixWord ++ tailWord_5325532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5325560 : List Nat := [2, 1, 2, 1, 1, 2, 4, 1, 9]
def baseStart_5325560 : Nat := 118140960795 + 5325560 * 2 ^ 59
def prefixEnd_5325560 : Nat := 4983230072969 + 3 ^ 40 * 5325560 * 2
def baseEnd_5325560 : Nat := 303841337150920995078689

theorem tailTrace_5325560 : CollatzResearch.WordTrace tailWord_5325560 prefixEnd_5325560 303841337150920995078689 := by
  unfold tailWord_5325560
  simp only [CollatzResearch.WordTrace]
  refine ⟨97119565293206564040735067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129492753724275418720980089 97119565293206564040735067)
  ·
    refine ⟨145679347939809846061102601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97119565293206564040735067 145679347939809846061102601)
    ·
      refine ⟨109259510954857384545826951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145679347939809846061102601 109259510954857384545826951)
      ·
        refine ⟨163889266432286076818740427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109259510954857384545826951 163889266432286076818740427)
        ·
          refine ⟨245833899648429115228110641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163889266432286076818740427 245833899648429115228110641)
          ·
            refine ⟨184375424736321836421082981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 245833899648429115228110641 184375424736321836421082981)
            ·
              refine ⟨34570392138060344328953059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 184375424736321836421082981 34570392138060344328953059)
              ·
                refine ⟨51855588207090516493429589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34570392138060344328953059 51855588207090516493429589)
                ·
                  refine ⟨303841337150920995078689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 51855588207090516493429589 303841337150920995078689)
                  ·
                    rfl

theorem cell23_5325560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 1, 9].length) (baseStart_5325560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5325560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5325560 prefixEnd_5325560 := by exact prefixLift 5325560
  have htrace : WordTrace (prefixWord ++ tailWord_5325560) baseStart_5325560 baseEnd_5325560 := by
    simpa [prefixWord, tailWord_5325560, baseEnd_5325560] using wordTrace_append hprefix tailTrace_5325560
  have hstable : (prefixWord ++ tailWord_5325560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5325560).length < 2 ^ (prefixWord ++ tailWord_5325560).sum := by decide
  have hdescent : baseEnd_5325560 < baseStart_5325560 := by decide
  rcases family_descends (prefixWord ++ tailWord_5325560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5325587 : List Nat := [1, 1, 1, 2, 1, 3, 4, 2, 2, 3, 3]
def baseStart_5325587 : Nat := 118140960795 + 5325587 * 2 ^ 59
def prefixEnd_5325587 : Nat := 4983230072969 + 3 ^ 40 * 5325587 * 2
def baseEnd_5325587 : Nat := 2734585898335960350070577

theorem tailTrace_5325587 : CollatzResearch.WordTrace tailWord_5325587 prefixEnd_5325587 2734585898335960350070577 := by
  unfold tailWord_5325587
  simp only [CollatzResearch.WordTrace]
  refine ⟨194240115357315311692703015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129493410238210207795135343 194240115357315311692703015)
  ·
    refine ⟨291360173035972967539054523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194240115357315311692703015 291360173035972967539054523)
    ·
      refine ⟨437040259553959451308581785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 291360173035972967539054523 437040259553959451308581785)
      ·
        refine ⟨327780194665469588481436339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 437040259553959451308581785 327780194665469588481436339)
        ·
          refine ⟨491670291998204382722154509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 327780194665469588481436339 491670291998204382722154509)
          ·
            refine ⟨184376359499326643520807941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 491670291998204382722154509 184376359499326643520807941)
            ·
              refine ⟨34570567406123745660151489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 184376359499326643520807941 34570567406123745660151489)
              ·
                refine ⟨25927925554592809245113617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34570567406123745660151489 25927925554592809245113617)
                ·
                  refine ⟨19445944165944606933835213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25927925554592809245113617 19445944165944606933835213)
                  ·
                    refine ⟨7292229062229227600188205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19445944165944606933835213 7292229062229227600188205)
                    ·
                      refine ⟨2734585898335960350070577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7292229062229227600188205 2734585898335960350070577)
                      ·
                        rfl

theorem cell23_5325587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 2, 2, 3, 3].length) (baseStart_5325587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5325587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5325587 prefixEnd_5325587 := by exact prefixLift 5325587
  have htrace : WordTrace (prefixWord ++ tailWord_5325587) baseStart_5325587 baseEnd_5325587 := by
    simpa [prefixWord, tailWord_5325587, baseEnd_5325587] using wordTrace_append hprefix tailTrace_5325587
  have hstable : (prefixWord ++ tailWord_5325587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5325587).length < 2 ^ (prefixWord ++ tailWord_5325587).sum := by decide
  have hdescent : baseEnd_5325587 < baseStart_5325587 := by decide
  rcases family_descends (prefixWord ++ tailWord_5325587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5325594 : List Nat := [3, 1, 1, 3, 2, 1, 3, 4, 5]
def baseStart_5325594 : Nat := 118140960795 + 5325594 * 2 ^ 59
def prefixEnd_5325594 : Nat := 4983230072969 + 3 ^ 40 * 5325594 * 2
def baseEnd_5325594 : Nat := 303843276966726869187005

theorem tailTrace_5325594 : CollatzResearch.WordTrace tailWord_5325594 prefixEnd_5325594 303843276966726869187005 := by
  unfold tailWord_5325594
  simp only [CollatzResearch.WordTrace]
  refine ⟨48560092667072487972051959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129493580445526634592138557 48560092667072487972051959)
  ·
    refine ⟨72840139000608731958077939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48560092667072487972051959 72840139000608731958077939)
    ·
      refine ⟨109260208500913097937116909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72840139000608731958077939 109260208500913097937116909)
      ·
        refine ⟨40972578187842411726418841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109260208500913097937116909 40972578187842411726418841)
        ·
          refine ⟨30729433640881808794814131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40972578187842411726418841 30729433640881808794814131)
          ·
            refine ⟨46094150461322713192221197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30729433640881808794814131 46094150461322713192221197)
            ·
              refine ⟨17285306422996017447082949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46094150461322713192221197 17285306422996017447082949)
              ·
                refine ⟨3240994954311753271328053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17285306422996017447082949 3240994954311753271328053)
                ·
                  refine ⟨303843276966726869187005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3240994954311753271328053 303843276966726869187005)
                  ·
                    rfl

theorem cell23_5325594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 4, 5].length) (baseStart_5325594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5325594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5325594 prefixEnd_5325594 := by exact prefixLift 5325594
  have htrace : WordTrace (prefixWord ++ tailWord_5325594) baseStart_5325594 baseEnd_5325594 := by
    simpa [prefixWord, tailWord_5325594, baseEnd_5325594] using wordTrace_append hprefix tailTrace_5325594
  have hstable : (prefixWord ++ tailWord_5325594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5325594).length < 2 ^ (prefixWord ++ tailWord_5325594).sum := by decide
  have hdescent : baseEnd_5325594 < baseStart_5325594 := by decide
  rcases family_descends (prefixWord ++ tailWord_5325594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5325747 : List Nat := [1, 1, 1, 2, 3, 1, 2, 2, 3, 1, 6]
def baseStart_5325747 : Nat := 118140960795 + 5325747 * 2 ^ 59
def prefixEnd_5325747 : Nat := 4983230072969 + 3 ^ 40 * 5325747 * 2
def baseEnd_5325747 : Nat := 2734668055240679724069841

theorem tailTrace_5325747 : CollatzResearch.WordTrace tailWord_5325747 prefixEnd_5325747 2734668055240679724069841 := by
  unfold tailWord_5325747
  simp only [CollatzResearch.WordTrace]
  refine ⟨194245951036735659018527495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129497300691157106012351663 194245951036735659018527495)
  ·
    refine ⟨291368926555103488527791243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194245951036735659018527495 291368926555103488527791243)
    ·
      refine ⟨437053389832655232791686865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 291368926555103488527791243 437053389832655232791686865)
      ·
        refine ⟨327790042374491424593765149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 437053389832655232791686865 327790042374491424593765149)
        ·
          refine ⟨122921265890434284222661931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 327790042374491424593765149 122921265890434284222661931)
          ·
            refine ⟨184381898835651426333992897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122921265890434284222661931 184381898835651426333992897)
            ·
              refine ⟨138286424126738569750494673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 184381898835651426333992897 138286424126738569750494673)
              ·
                refine ⟨103714818095053927312871005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 138286424126738569750494673 103714818095053927312871005)
                ·
                  refine ⟨38893056785645222742326627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 103714818095053927312871005 38893056785645222742326627)
                  ·
                    refine ⟨58339585178467834113489941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38893056785645222742326627 58339585178467834113489941)
                    ·
                      refine ⟨2734668055240679724069841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58339585178467834113489941 2734668055240679724069841)
                      ·
                        rfl

theorem cell23_5325747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 3, 1, 6].length) (baseStart_5325747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5325747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5325747 prefixEnd_5325747 := by exact prefixLift 5325747
  have htrace : WordTrace (prefixWord ++ tailWord_5325747) baseStart_5325747 baseEnd_5325747 := by
    simpa [prefixWord, tailWord_5325747, baseEnd_5325747] using wordTrace_append hprefix tailTrace_5325747
  have hstable : (prefixWord ++ tailWord_5325747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5325747).length < 2 ^ (prefixWord ++ tailWord_5325747).sum := by decide
  have hdescent : baseEnd_5325747 < baseStart_5325747 := by decide
  rcases family_descends (prefixWord ++ tailWord_5325747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5325757 : List Nat := [1, 4, 1, 2, 15]
def baseStart_5325757 : Nat := 118140960795 + 5325757 * 2 ^ 59
def prefixEnd_5325757 : Nat := 4983230072969 + 3 ^ 40 * 5325757 * 2
def baseEnd_5325757 : Nat := 3751266378665603134355

theorem tailTrace_5325757 : CollatzResearch.WordTrace tailWord_5325757 prefixEnd_5325757 3751266378665603134355 := by
  unfold tailWord_5325757
  simp only [CollatzResearch.WordTrace]
  refine ⟨194246315766699430726391525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129497543844466287150927683 194246315766699430726391525)
  ·
    refine ⟨36421184206256143261198411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 194246315766699430726391525 36421184206256143261198411)
    ·
      refine ⟨54631776309384214891797617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36421184206256143261198411 54631776309384214891797617)
      ·
        refine ⟨40973832232038161168848213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54631776309384214891797617 40973832232038161168848213)
        ·
          refine ⟨3751266378665603134355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 15 40973832232038161168848213 3751266378665603134355)
          ·
            rfl

theorem cell23_5325757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 15].length) (baseStart_5325757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5325757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5325757 prefixEnd_5325757 := by exact prefixLift 5325757
  have htrace : WordTrace (prefixWord ++ tailWord_5325757) baseStart_5325757 baseEnd_5325757 := by
    simpa [prefixWord, tailWord_5325757, baseEnd_5325757] using wordTrace_append hprefix tailTrace_5325757
  have hstable : (prefixWord ++ tailWord_5325757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5325757).length < 2 ^ (prefixWord ++ tailWord_5325757).sum := by decide
  have hdescent : baseEnd_5325757 < baseStart_5325757 := by decide
  rcases family_descends (prefixWord ++ tailWord_5325757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5325774 : List Nat := [4, 1, 1, 1, 2, 3, 3, 8]
def baseStart_5325774 : Nat := 118140960795 + 5325774 * 2 ^ 59
def prefixEnd_5325774 : Nat := 4983230072969 + 3 ^ 40 * 5325774 * 2
def baseEnd_5325774 : Nat := 101284515526605596978971

theorem tailTrace_5325774 : CollatzResearch.WordTrace tailWord_5325774 prefixEnd_5325774 101284515526605596978971 := by
  unfold tailWord_5325774
  simp only [CollatzResearch.WordTrace]
  refine ⟨24280866975954730328720047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129497957205091895086506917 24280866975954730328720047)
  ·
    refine ⟨36421300463932095493080071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24280866975954730328720047 36421300463932095493080071)
    ·
      refine ⟨54631950695898143239620107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36421300463932095493080071 54631950695898143239620107)
      ·
        refine ⟨81947926043847214859430161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54631950695898143239620107 81947926043847214859430161)
        ·
          refine ⟨61460944532885411144572621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81947926043847214859430161 61460944532885411144572621)
          ·
            refine ⟨23047854199832029179214733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61460944532885411144572621 23047854199832029179214733)
            ·
              refine ⟨8642945324937010942205525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23047854199832029179214733 8642945324937010942205525)
              ·
                refine ⟨101284515526605596978971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8642945324937010942205525 101284515526605596978971)
                ·
                  rfl

theorem cell23_5325774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 8].length) (baseStart_5325774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5325774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5325774 prefixEnd_5325774 := by exact prefixLift 5325774
  have htrace : WordTrace (prefixWord ++ tailWord_5325774) baseStart_5325774 baseEnd_5325774 := by
    simpa [prefixWord, tailWord_5325774, baseEnd_5325774] using wordTrace_append hprefix tailTrace_5325774
  have hstable : (prefixWord ++ tailWord_5325774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5325774).length < 2 ^ (prefixWord ++ tailWord_5325774).sum := by decide
  have hdescent : baseEnd_5325774 < baseStart_5325774 := by decide
  rcases family_descends (prefixWord ++ tailWord_5325774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5325778 : List Nat := [3, 2, 2, 3, 1, 1, 2, 3, 2, 4]
def baseStart_5325778 : Nat := 118140960795 + 5325778 * 2 ^ 59
def prefixEnd_5325778 : Nat := 4983230072969 + 3 ^ 40 * 5325778 * 2
def baseEnd_5325778 : Nat := 911561324380323034260733

theorem tailTrace_5325778 : CollatzResearch.WordTrace tailWord_5325778 prefixEnd_5325778 911561324380323034260733 := by
  unfold tailWord_5325778
  simp only [CollatzResearch.WordTrace]
  refine ⟨48561770424905837828226497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129498054466415567541937325 48561770424905837828226497)
  ·
    refine ⟨36421327818679378371169873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48561770424905837828226497 36421327818679378371169873)
    ·
      refine ⟨27315995864009533778377405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36421327818679378371169873 27315995864009533778377405)
      ·
        refine ⟨10243498449003575166891527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27315995864009533778377405 10243498449003575166891527)
        ·
          refine ⟨15365247673505362750337291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10243498449003575166891527 15365247673505362750337291)
          ·
            refine ⟨23047871510258044125505937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15365247673505362750337291 23047871510258044125505937)
            ·
              refine ⟨17285903632693533094129453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23047871510258044125505937 17285903632693533094129453)
              ·
                refine ⟨6482213862260074910298545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17285903632693533094129453 6482213862260074910298545)
                ·
                  refine ⟨4861660396695056182723909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6482213862260074910298545 4861660396695056182723909)
                  ·
                    refine ⟨911561324380323034260733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4861660396695056182723909 911561324380323034260733)
                    ·
                      rfl

theorem cell23_5325778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 3, 2, 4].length) (baseStart_5325778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5325778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5325778 prefixEnd_5325778 := by exact prefixLift 5325778
  have htrace : WordTrace (prefixWord ++ tailWord_5325778) baseStart_5325778 baseEnd_5325778 := by
    simpa [prefixWord, tailWord_5325778, baseEnd_5325778] using wordTrace_append hprefix tailTrace_5325778
  have hstable : (prefixWord ++ tailWord_5325778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5325778).length < 2 ^ (prefixWord ++ tailWord_5325778).sum := by decide
  have hdescent : baseEnd_5325778 < baseStart_5325778 := by decide
  rcases family_descends (prefixWord ++ tailWord_5325778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5325791 : List Nat := [1, 1, 2, 3, 5, 1, 3, 7]
def baseStart_5325791 : Nat := 118140960795 + 5325791 * 2 ^ 59
def prefixEnd_5325791 : Nat := 4983230072969 + 3 ^ 40 * 5325791 * 2
def baseEnd_5325791 : Nat := 101284838829239909330357

theorem tailTrace_5325791 : CollatzResearch.WordTrace tailWord_5325791 prefixEnd_5325791 101284838829239909330357 := by
  unfold tailWord_5325791
  simp only [CollatzResearch.WordTrace]
  refine ⟨194247555848576254533129227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129498370565717503022086151 194247555848576254533129227)
  ·
    refine ⟨291371333772864381799693841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194247555848576254533129227 291371333772864381799693841)
    ·
      refine ⟨218528500329648286349770381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 291371333772864381799693841 218528500329648286349770381)
      ·
        refine ⟨81948187623618107381163893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 218528500329648286349770381 81948187623618107381163893)
        ·
          refine ⟨7682642589714197566984115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 81948187623618107381163893 7682642589714197566984115)
          ·
            refine ⟨11523963884571296350476173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7682642589714197566984115 11523963884571296350476173)
            ·
              refine ⟨4321486456714236131428565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11523963884571296350476173 4321486456714236131428565)
              ·
                refine ⟨101284838829239909330357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4321486456714236131428565 101284838829239909330357)
                ·
                  rfl

theorem cell23_5325791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 3, 7].length) (baseStart_5325791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5325791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5325791 prefixEnd_5325791 := by exact prefixLift 5325791
  have htrace : WordTrace (prefixWord ++ tailWord_5325791) baseStart_5325791 baseEnd_5325791 := by
    simpa [prefixWord, tailWord_5325791, baseEnd_5325791] using wordTrace_append hprefix tailTrace_5325791
  have hstable : (prefixWord ++ tailWord_5325791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5325791).length < 2 ^ (prefixWord ++ tailWord_5325791).sum := by decide
  have hdescent : baseEnd_5325791 < baseStart_5325791 := by decide
  rcases family_descends (prefixWord ++ tailWord_5325791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5325802 : List Nat := [3, 1, 3, 1, 2, 3, 2, 3, 1, 2, 2]
def baseStart_5325802 : Nat := 118140960795 + 5325802 * 2 ^ 59
def prefixEnd_5325802 : Nat := 4983230072969 + 3 ^ 40 * 5325802 * 2
def baseEnd_5325802 : Nat := 2734696296676677008882089

theorem tailTrace_5325802 : CollatzResearch.WordTrace tailWord_5325802 prefixEnd_5325802 2734696296676677008882089 := by
  unfold tailWord_5325802
  simp only [CollatzResearch.WordTrace]
  refine ⟨48561989262884100852944915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129498638034357602274519773 48561989262884100852944915)
  ·
    refine ⟨72842983894326151279417373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48561989262884100852944915 72842983894326151279417373)
    ·
      refine ⟨27316118960372306729781515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72842983894326151279417373 27316118960372306729781515)
      ·
        refine ⟨40974178440558460094672273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27316118960372306729781515 40974178440558460094672273)
        ·
          refine ⟨30730633830418845071004205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40974178440558460094672273 30730633830418845071004205)
          ·
            refine ⟨11523987686407066901626577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30730633830418845071004205 11523987686407066901626577)
            ·
              refine ⟨8642990764805300176219933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11523987686407066901626577 8642990764805300176219933)
              ·
                refine ⟨3241121536801987566082475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8642990764805300176219933 3241121536801987566082475)
                ·
                  refine ⟨4861682305202981349123713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3241121536801987566082475 4861682305202981349123713)
                  ·
                    refine ⟨3646261728902236011842785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4861682305202981349123713 3646261728902236011842785)
                    ·
                      refine ⟨2734696296676677008882089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3646261728902236011842785 2734696296676677008882089)
                      ·
                        rfl

theorem cell23_5325802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 3, 1, 2, 2].length) (baseStart_5325802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5325802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5325802 prefixEnd_5325802 := by exact prefixLift 5325802
  have htrace : WordTrace (prefixWord ++ tailWord_5325802) baseStart_5325802 baseEnd_5325802 := by
    simpa [prefixWord, tailWord_5325802, baseEnd_5325802] using wordTrace_append hprefix tailTrace_5325802
  have hstable : (prefixWord ++ tailWord_5325802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5325802).length < 2 ^ (prefixWord ++ tailWord_5325802).sum := by decide
  have hdescent : baseEnd_5325802 < baseStart_5325802 := by decide
  rcases family_descends (prefixWord ++ tailWord_5325802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5325835 : List Nat := [1, 1, 1, 1, 6, 3, 3, 1, 2, 1, 3]
def baseStart_5325835 : Nat := 118140960795 + 5325835 * 2 ^ 59
def prefixEnd_5325835 : Nat := 4983230072969 + 3 ^ 40 * 5325835 * 2
def baseEnd_5325835 : Nat := 2734713241538275379769437

theorem tailTrace_5325835 : CollatzResearch.WordTrace tailWord_5325835 prefixEnd_5325835 2734713241538275379769437 := by
  unfold tailWord_5325835
  simp only [CollatzResearch.WordTrace]
  refine ⟨194249160660416850047730959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129499440440277900031820639 194249160660416850047730959)
  ·
    refine ⟨291373740990625275071596439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194249160660416850047730959 291373740990625275071596439)
    ·
      refine ⟨437060611485937912607394659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 291373740990625275071596439 437060611485937912607394659)
      ·
        refine ⟨655590917228906868911091989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 437060611485937912607394659 655590917228906868911091989)
        ·
          refine ⟨30730824245105009480207437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 655590917228906868911091989 30730824245105009480207437)
          ·
            refine ⟨11524059091914378555077789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30730824245105009480207437 11524059091914378555077789)
            ·
              refine ⟨4321522159467891958154171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11524059091914378555077789 4321522159467891958154171)
              ·
                refine ⟨6482283239201837937231257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4321522159467891958154171 6482283239201837937231257)
                ·
                  refine ⟨4861712429401378452923443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6482283239201837937231257 4861712429401378452923443)
                  ·
                    refine ⟨7292568644102067679385165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4861712429401378452923443 7292568644102067679385165)
                    ·
                      refine ⟨2734713241538275379769437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7292568644102067679385165 2734713241538275379769437)
                      ·
                        rfl

theorem cell23_5325835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 3, 1, 2, 1, 3].length) (baseStart_5325835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5325835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5325835 prefixEnd_5325835 := by exact prefixLift 5325835
  have htrace : WordTrace (prefixWord ++ tailWord_5325835) baseStart_5325835 baseEnd_5325835 := by
    simpa [prefixWord, tailWord_5325835, baseEnd_5325835] using wordTrace_append hprefix tailTrace_5325835
  have hstable : (prefixWord ++ tailWord_5325835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5325835).length < 2 ^ (prefixWord ++ tailWord_5325835).sum := by decide
  have hdescent : baseEnd_5325835 < baseStart_5325835 := by decide
  rcases family_descends (prefixWord ++ tailWord_5325835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5325842 : List Nat := [3, 2, 5, 1, 1, 2, 2, 7]
def baseStart_5325842 : Nat := 118140960795 + 5325842 * 2 ^ 59
def prefixEnd_5325842 : Nat := 4983230072969 + 3 ^ 40 * 5325842 * 2
def baseEnd_5325842 : Nat := 101285808737142846384515

theorem tailTrace_5325842 : CollatzResearch.WordTrace tailWord_5325842 prefixEnd_5325842 101285808737142846384515 := by
  unfold tailWord_5325842
  simp only [CollatzResearch.WordTrace]
  refine ⟨48562353992847872560808945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129499610647594326828823853 48562353992847872560808945)
  ·
    refine ⟨36421765494635904420606709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48562353992847872560808945 36421765494635904420606709)
    ·
      refine ⟨3414540515122116039431879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 36421765494635904420606709 3414540515122116039431879)
      ·
        refine ⟨5121810772683174059147819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3414540515122116039431879 5121810772683174059147819)
        ·
          refine ⟨7682716159024761088721729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5121810772683174059147819 7682716159024761088721729)
          ·
            refine ⟨5762037119268570816541297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7682716159024761088721729 5762037119268570816541297)
            ·
              refine ⟨4321527839451428112405973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5762037119268570816541297 4321527839451428112405973)
              ·
                refine ⟨101285808737142846384515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4321527839451428112405973 101285808737142846384515)
                ·
                  rfl

theorem cell23_5325842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 2, 7].length) (baseStart_5325842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5325842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5325842 prefixEnd_5325842 := by exact prefixLift 5325842
  have htrace : WordTrace (prefixWord ++ tailWord_5325842) baseStart_5325842 baseEnd_5325842 := by
    simpa [prefixWord, tailWord_5325842, baseEnd_5325842] using wordTrace_append hprefix tailTrace_5325842
  have hstable : (prefixWord ++ tailWord_5325842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5325842).length < 2 ^ (prefixWord ++ tailWord_5325842).sum := by decide
  have hdescent : baseEnd_5325842 < baseStart_5325842 := by decide
  rcases family_descends (prefixWord ++ tailWord_5325842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5325845 : List Nat := [1, 3, 2, 1, 4, 2, 2, 2, 1, 3, 2]
def baseStart_5325845 : Nat := 118140960795 + 5325845 * 2 ^ 59
def prefixEnd_5325845 : Nat := 4983230072969 + 3 ^ 40 * 5325845 * 2
def baseEnd_5325845 : Nat := 2734718376344820340644391

theorem tailTrace_5325845 : CollatzResearch.WordTrace tailWord_5325845 prefixEnd_5325845 2734718376344820340644391 := by
  unfold tailWord_5325845
  simp only [CollatzResearch.WordTrace]
  refine ⟨194249525390380621755594989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129499683593587081170396659 194249525390380621755594989)
  ·
    refine ⟨72843572021392733158348121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 194249525390380621755594989 72843572021392733158348121)
    ·
      refine ⟨54632679016044549868761091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72843572021392733158348121 54632679016044549868761091)
      ·
        refine ⟨81949018524066824803141637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54632679016044549868761091 81949018524066824803141637)
        ·
          refine ⟨15365440973262529650589057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81949018524066824803141637 15365440973262529650589057)
          ·
            refine ⟨11524080729946897237941793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15365440973262529650589057 11524080729946897237941793)
            ·
              refine ⟨8643060547460172928456345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11524080729946897237941793 8643060547460172928456345)
              ·
                refine ⟨6482295410595129696342259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8643060547460172928456345 6482295410595129696342259)
                ·
                  refine ⟨9723443115892694544513389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6482295410595129696342259 9723443115892694544513389)
                  ·
                    refine ⟨3646291168459760454192521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9723443115892694544513389 3646291168459760454192521)
                    ·
                      refine ⟨2734718376344820340644391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3646291168459760454192521 2734718376344820340644391)
                      ·
                        rfl

theorem cell23_5325845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 2, 1, 3, 2].length) (baseStart_5325845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5325845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5325845 prefixEnd_5325845 := by exact prefixLift 5325845
  have htrace : WordTrace (prefixWord ++ tailWord_5325845) baseStart_5325845 baseEnd_5325845 := by
    simpa [prefixWord, tailWord_5325845, baseEnd_5325845] using wordTrace_append hprefix tailTrace_5325845
  have hstable : (prefixWord ++ tailWord_5325845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5325845).length < 2 ^ (prefixWord ++ tailWord_5325845).sum := by decide
  have hdescent : baseEnd_5325845 < baseStart_5325845 := by decide
  rcases family_descends (prefixWord ++ tailWord_5325845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5325874 : List Nat := [3, 2, 1, 1, 2, 2, 1, 1, 1, 2, 7]
def baseStart_5325874 : Nat := 118140960795 + 5325874 * 2 ^ 59
def prefixEnd_5325874 : Nat := 4983230072969 + 3 ^ 40 * 5325874 * 2
def baseEnd_5325874 : Nat := 2734733267283800727181757

theorem tailTrace_5325874 : CollatzResearch.WordTrace tailWord_5325874 prefixEnd_5325874 2734733267283800727181757 := by
  unfold tailWord_5325874
  simp only [CollatzResearch.WordTrace]
  refine ⟨48562645776818889927100169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129500388738183706472267117 48562645776818889927100169)
  ·
    refine ⟨36421984332614167445325127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48562645776818889927100169 36421984332614167445325127)
    ·
      refine ⟨54632976498921251167987691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36421984332614167445325127 54632976498921251167987691)
      ·
        refine ⟨81949464748381876751981537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54632976498921251167987691 81949464748381876751981537)
        ·
          refine ⟨61462098561286407563986153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81949464748381876751981537 61462098561286407563986153)
          ·
            refine ⟨46096573920964805672989615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61462098561286407563986153 46096573920964805672989615)
            ·
              refine ⟨69144860881447208509484423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46096573920964805672989615 69144860881447208509484423)
              ·
                refine ⟨103717291322170812764226635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69144860881447208509484423 103717291322170812764226635)
                ·
                  refine ⟨155575936983256219146339953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 103717291322170812764226635 155575936983256219146339953)
                  ·
                    refine ⟨116681952737442164359754965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 155575936983256219146339953 116681952737442164359754965)
                    ·
                      refine ⟨2734733267283800727181757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 116681952737442164359754965 2734733267283800727181757)
                      ·
                        rfl

theorem cell23_5325874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 1, 2, 7].length) (baseStart_5325874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5325874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5325874 prefixEnd_5325874 := by exact prefixLift 5325874
  have htrace : WordTrace (prefixWord ++ tailWord_5325874) baseStart_5325874 baseEnd_5325874 := by
    simpa [prefixWord, tailWord_5325874, baseEnd_5325874] using wordTrace_append hprefix tailTrace_5325874
  have hstable : (prefixWord ++ tailWord_5325874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5325874).length < 2 ^ (prefixWord ++ tailWord_5325874).sum := by decide
  have hdescent : baseEnd_5325874 < baseStart_5325874 := by decide
  rcases family_descends (prefixWord ++ tailWord_5325874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5325881 : List Nat := [1, 2, 1, 5, 2, 1, 3, 1, 7]
def baseStart_5325881 : Nat := 118140960795 + 5325881 * 2 ^ 59
def prefixEnd_5325881 : Nat := 4983230072969 + 3 ^ 40 * 5325881 * 2
def baseEnd_5325881 : Nat := 303859651294264688866025

theorem tailTrace_5325881 : CollatzResearch.WordTrace tailWord_5325881 prefixEnd_5325881 303859651294264688866025 := by
  unfold tailWord_5325881
  simp only [CollatzResearch.WordTrace]
  refine ⟨194250838418250199903905497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129500558945500133269270331 194250838418250199903905497)
  ·
    refine ⟨145688128813687649927929123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194250838418250199903905497 145688128813687649927929123)
    ·
      refine ⟨218532193220531474891893685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145688128813687649927929123 218532193220531474891893685)
      ·
        refine ⟨20487393114424825771115033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 218532193220531474891893685 20487393114424825771115033)
        ·
          refine ⟨15365544835818619328336275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20487393114424825771115033 15365544835818619328336275)
          ·
            refine ⟨23048317253727928992504413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15365544835818619328336275 23048317253727928992504413)
            ·
              refine ⟨8643118970147973372189155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23048317253727928992504413 8643118970147973372189155)
              ·
                refine ⟨12964678455221960058283733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8643118970147973372189155 12964678455221960058283733)
                ·
                  refine ⟨303859651294264688866025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12964678455221960058283733 303859651294264688866025)
                  ·
                    rfl

theorem cell23_5325881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 1, 7].length) (baseStart_5325881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5325881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5325881 prefixEnd_5325881 := by exact prefixLift 5325881
  have htrace : WordTrace (prefixWord ++ tailWord_5325881) baseStart_5325881 baseEnd_5325881 := by
    simpa [prefixWord, tailWord_5325881, baseEnd_5325881] using wordTrace_append hprefix tailTrace_5325881
  have hstable : (prefixWord ++ tailWord_5325881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5325881).length < 2 ^ (prefixWord ++ tailWord_5325881).sum := by decide
  have hdescent : baseEnd_5325881 < baseStart_5325881 := by decide
  rcases family_descends (prefixWord ++ tailWord_5325881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5325931 : List Nat := [1, 1, 1, 1, 2, 2, 1, 1, 5, 6, 2]
def baseStart_5325931 : Nat := 118140960795 + 5325931 * 2 ^ 59
def prefixEnd_5325931 : Nat := 4983230072969 + 3 ^ 40 * 5325931 * 2
def baseEnd_5325931 : Nat := 2734762535681107004168995

theorem tailTrace_5325931 : CollatzResearch.WordTrace tailWord_5325931 prefixEnd_5325931 2734762535681107004168995 := by
  unfold tailWord_5325931
  simp only [CollatzResearch.WordTrace]
  refine ⟨194252662068069058443225647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129501774712046038962150431 194252662068069058443225647)
  ·
    refine ⟨291378993102103587664838471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194252662068069058443225647 291378993102103587664838471)
    ·
      refine ⟨437068489653155381497257707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 291378993102103587664838471 437068489653155381497257707)
      ·
        refine ⟨655602734479733072245886561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 437068489653155381497257707 655602734479733072245886561)
        ·
          refine ⟨491702050859799804184414921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 655602734479733072245886561 491702050859799804184414921)
          ·
            refine ⟨368776538144849853138311191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 491702050859799804184414921 368776538144849853138311191)
            ·
              refine ⟨553164807217274779707466787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 368776538144849853138311191 553164807217274779707466787)
              ·
                refine ⟨829747210825912169561200181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 553164807217274779707466787 829747210825912169561200181)
                ·
                  refine ⟨77788801014929265896362517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 829747210825912169561200181 77788801014929265896362517)
                  ·
                    refine ⟨3646350047574809338891993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 77788801014929265896362517 3646350047574809338891993)
                    ·
                      refine ⟨2734762535681107004168995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3646350047574809338891993 2734762535681107004168995)
                      ·
                        rfl

theorem cell23_5325931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 5, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 5, 6, 2].length) (baseStart_5325931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5325931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5325931 prefixEnd_5325931 := by exact prefixLift 5325931
  have htrace : WordTrace (prefixWord ++ tailWord_5325931) baseStart_5325931 baseEnd_5325931 := by
    simpa [prefixWord, tailWord_5325931, baseEnd_5325931] using wordTrace_append hprefix tailTrace_5325931
  have hstable : (prefixWord ++ tailWord_5325931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5325931).length < 2 ^ (prefixWord ++ tailWord_5325931).sum := by decide
  have hdescent : baseEnd_5325931 < baseStart_5325931 := by decide
  rcases family_descends (prefixWord ++ tailWord_5325931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5325948 : List Nat := [2, 2, 2, 1, 1, 3, 3, 1, 2, 4, 2]
def baseStart_5325948 : Nat := 118140960795 + 5325948 * 2 ^ 59
def prefixEnd_5325948 : Nat := 4983230072969 + 3 ^ 40 * 5325948 * 2
def baseEnd_5325948 : Nat := 2734771264852233437656417

theorem tailTrace_5325948 : CollatzResearch.WordTrace tailWord_5325948 prefixEnd_5325948 2734771264852233437656417 := by
  unfold tailWord_5325948
  simp only [CollatzResearch.WordTrace]
  refine ⟨97126641054503735173297249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129502188072671646897729665 97126641054503735173297249)
  ·
    refine ⟨72844980790877801379972937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97126641054503735173297249 72844980790877801379972937)
    ·
      refine ⟨54633735593158351034979703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72844980790877801379972937 54633735593158351034979703)
      ·
        refine ⟨81950603389737526552469555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54633735593158351034979703 81950603389737526552469555)
        ·
          refine ⟨122925905084606289828704333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81950603389737526552469555 122925905084606289828704333)
          ·
            refine ⟨46097214406727358685764125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 122925905084606289828704333 46097214406727358685764125)
            ·
              refine ⟨17286455402522759507161547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46097214406727358685764125 17286455402522759507161547)
              ·
                refine ⟨25929683103784139260742321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17286455402522759507161547 25929683103784139260742321)
                ·
                  refine ⟨19447262327838104445556741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25929683103784139260742321 19447262327838104445556741)
                  ·
                    refine ⟨3646361686469644583541889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19447262327838104445556741 3646361686469644583541889)
                    ·
                      refine ⟨2734771264852233437656417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3646361686469644583541889 2734771264852233437656417)
                      ·
                        rfl

theorem cell23_5325948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 1, 2, 4, 2].length) (baseStart_5325948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5325948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5325948 prefixEnd_5325948 := by exact prefixLift 5325948
  have htrace : WordTrace (prefixWord ++ tailWord_5325948) baseStart_5325948 baseEnd_5325948 := by
    simpa [prefixWord, tailWord_5325948, baseEnd_5325948] using wordTrace_append hprefix tailTrace_5325948
  have hstable : (prefixWord ++ tailWord_5325948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5325948).length < 2 ^ (prefixWord ++ tailWord_5325948).sum := by decide
  have hdescent : baseEnd_5325948 < baseStart_5325948 := by decide
  rcases family_descends (prefixWord ++ tailWord_5325948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5325975 : List Nat := [1, 1, 3, 3, 3, 1, 1, 5, 1, 4]
def baseStart_5325975 : Nat := 118140960795 + 5325975 * 2 ^ 59
def prefixEnd_5325975 : Nat := 4983230072969 + 3 ^ 40 * 5325975 * 2
def baseEnd_5325975 : Nat := 911595042943301610672931

theorem tailTrace_5325975 : CollatzResearch.WordTrace tailWord_5325975 prefixEnd_5325975 911595042943301610672931 := by
  unfold tailWord_5325975
  simp only [CollatzResearch.WordTrace]
  refine ⟨194254266879909653957827379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129502844586606435971884919 194254266879909653957827379)
  ·
    refine ⟨291381400319864480936741069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194254266879909653957827379 291381400319864480936741069)
    ·
      refine ⟨109268025119949180351277901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 291381400319864480936741069 109268025119949180351277901)
      ·
        refine ⟨40975509419980942631729213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109268025119949180351277901 40975509419980942631729213)
        ·
          refine ⟨15365816032492853486898455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40975509419980942631729213 15365816032492853486898455)
          ·
            refine ⟨23048724048739280230347683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15365816032492853486898455 23048724048739280230347683)
            ·
              refine ⟨34573086073108920345521525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23048724048739280230347683 34573086073108920345521525)
              ·
                refine ⟨3241226819353961282392643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34573086073108920345521525 3241226819353961282392643)
                ·
                  refine ⟨4861840229030941923588965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3241226819353961282392643 4861840229030941923588965)
                  ·
                    refine ⟨911595042943301610672931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4861840229030941923588965 911595042943301610672931)
                    ·
                      rfl

theorem cell23_5325975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 5, 1, 4].length) (baseStart_5325975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5325975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5325975 prefixEnd_5325975 := by exact prefixLift 5325975
  have htrace : WordTrace (prefixWord ++ tailWord_5325975) baseStart_5325975 baseEnd_5325975 := by
    simpa [prefixWord, tailWord_5325975, baseEnd_5325975] using wordTrace_append hprefix tailTrace_5325975
  have hstable : (prefixWord ++ tailWord_5325975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5325975).length < 2 ^ (prefixWord ++ tailWord_5325975).sum := by decide
  have hdescent : baseEnd_5325975 < baseStart_5325975 := by decide
  rcases family_descends (prefixWord ++ tailWord_5325975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5325988 : List Nat := [2, 3, 1, 2, 3, 1, 3, 2, 6]
def baseStart_5325988 : Nat := 118140960795 + 5325988 * 2 ^ 59
def prefixEnd_5325988 : Nat := 4983230072969 + 3 ^ 40 * 5325988 * 2
def baseEnd_5325988 : Nat := 303865756008712586795137

theorem tailTrace_5325988 : CollatzResearch.WordTrace tailWord_5325988 prefixEnd_5325988 303865756008712586795137 := by
  unfold tailWord_5325988
  simp only [CollatzResearch.WordTrace]
  refine ⟨97127370514431278589025309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129503160685908371452033745 97127370514431278589025309)
  ·
    refine ⟨36422763942911729470884491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97127370514431278589025309 36422763942911729470884491)
    ·
      refine ⟨54634145914367594206326737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36422763942911729470884491 54634145914367594206326737)
      ·
        refine ⟨40975609435775695654745053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54634145914367594206326737 40975609435775695654745053)
        ·
          refine ⟨15365853538415885870529395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40975609435775695654745053 15365853538415885870529395)
          ·
            refine ⟨23048780307623828805794093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15365853538415885870529395 23048780307623828805794093)
            ·
              refine ⟨8643292615358935802172785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23048780307623828805794093 8643292615358935802172785)
              ·
                refine ⟨6482469461519201851629589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8643292615358935802172785 6482469461519201851629589)
                ·
                  refine ⟨303865756008712586795137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6482469461519201851629589 303865756008712586795137)
                  ·
                    rfl

theorem cell23_5325988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 2, 6].length) (baseStart_5325988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5325988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5325988 prefixEnd_5325988 := by exact prefixLift 5325988
  have htrace : WordTrace (prefixWord ++ tailWord_5325988) baseStart_5325988 baseEnd_5325988 := by
    simpa [prefixWord, tailWord_5325988, baseEnd_5325988] using wordTrace_append hprefix tailTrace_5325988
  have hstable : (prefixWord ++ tailWord_5325988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5325988).length < 2 ^ (prefixWord ++ tailWord_5325988).sum := by decide
  have hdescent : baseEnd_5325988 < baseStart_5325988 := by decide
  rcases family_descends (prefixWord ++ tailWord_5325988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5326008 : List Nat := [2, 1, 2, 1, 2, 1, 2, 1, 6, 3, 2]
def baseStart_5326008 : Nat := 118140960795 + 5326008 * 2 ^ 59
def prefixEnd_5326008 : Nat := 4983230072969 + 3 ^ 40 * 5326008 * 2
def baseEnd_5326008 : Nat := 2734802073691503202906141

theorem tailTrace_5326008 : CollatzResearch.WordTrace tailWord_5326008 prefixEnd_5326008 2734802073691503202906141 := by
  unfold tailWord_5326008
  simp only [CollatzResearch.WordTrace]
  refine ⟨97127735244395050296889339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129503646992526733729185785 97127735244395050296889339)
  ·
    refine ⟨145691602866592575445334009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97127735244395050296889339 145691602866592575445334009)
    ·
      refine ⟨109268702149944431584000507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145691602866592575445334009 109268702149944431584000507)
      ·
        refine ⟨163903053224916647376000761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109268702149944431584000507 163903053224916647376000761)
        ·
          refine ⟨122927289918687485532000571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163903053224916647376000761 122927289918687485532000571)
          ·
            refine ⟨184390934878031228298000857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122927289918687485532000571 184390934878031228298000857)
            ·
              refine ⟨138293201158523421223500643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 184390934878031228298000857 138293201158523421223500643)
              ·
                refine ⟨207439801737785131835250965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 138293201158523421223500643 207439801737785131835250965)
                ·
                  refine ⟨9723740706458678054777389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 207439801737785131835250965 9723740706458678054777389)
                  ·
                    refine ⟨3646402764922004270541521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9723740706458678054777389 3646402764922004270541521)
                    ·
                      refine ⟨2734802073691503202906141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3646402764922004270541521 2734802073691503202906141)
                      ·
                        rfl

theorem cell23_5326008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 6, 3, 2].length) (baseStart_5326008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5326008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5326008 prefixEnd_5326008 := by exact prefixLift 5326008
  have htrace : WordTrace (prefixWord ++ tailWord_5326008) baseStart_5326008 baseEnd_5326008 := by
    simpa [prefixWord, tailWord_5326008, baseEnd_5326008] using wordTrace_append hprefix tailTrace_5326008
  have hstable : (prefixWord ++ tailWord_5326008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5326008).length < 2 ^ (prefixWord ++ tailWord_5326008).sum := by decide
  have hdescent : baseEnd_5326008 < baseStart_5326008 := by decide
  rcases family_descends (prefixWord ++ tailWord_5326008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5326048 : List Nat := [2, 1, 1, 3, 1, 4, 2, 1, 4, 4]
def baseStart_5326048 : Nat := 118140960795 + 5326048 * 2 ^ 59
def prefixEnd_5326048 : Nat := 4983230072969 + 3 ^ 40 * 5326048 * 2
def baseEnd_5326048 : Nat := 911607537639227682135319

theorem tailTrace_5326048 : CollatzResearch.WordTrace tailWord_5326048 prefixEnd_5326048 911607537639227682135319 := by
  unfold tailWord_5326048
  simp only [CollatzResearch.WordTrace]
  refine ⟨97128464704322593712617399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129504619605763458283489865 97128464704322593712617399)
  ·
    refine ⟨145692697056483890568926099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97128464704322593712617399 145692697056483890568926099)
    ·
      refine ⟨218539045584725835853389149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145692697056483890568926099 218539045584725835853389149)
      ·
        refine ⟨81952142094272188445020931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 218539045584725835853389149 81952142094272188445020931)
        ·
          refine ⟨122928213141408282667531397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81952142094272188445020931 122928213141408282667531397)
          ·
            refine ⟨23049039964014053000162137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 122928213141408282667531397 23049039964014053000162137)
            ·
              refine ⟨17286779973010539750121603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23049039964014053000162137 17286779973010539750121603)
              ·
                refine ⟨25930169959515809625182405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17286779973010539750121603 25930169959515809625182405)
                ·
                  refine ⟨4861906867409214304721701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25930169959515809625182405 4861906867409214304721701)
                  ·
                    refine ⟨911607537639227682135319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4861906867409214304721701 911607537639227682135319)
                    ·
                      rfl

theorem cell23_5326048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 1, 4, 4].length) (baseStart_5326048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5326048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5326048 prefixEnd_5326048 := by exact prefixLift 5326048
  have htrace : WordTrace (prefixWord ++ tailWord_5326048) baseStart_5326048 baseEnd_5326048 := by
    simpa [prefixWord, tailWord_5326048, baseEnd_5326048] using wordTrace_append hprefix tailTrace_5326048
  have hstable : (prefixWord ++ tailWord_5326048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5326048).length < 2 ^ (prefixWord ++ tailWord_5326048).sum := by decide
  have hdescent : baseEnd_5326048 < baseStart_5326048 := by decide
  rcases family_descends (prefixWord ++ tailWord_5326048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5326049 : List Nat := [1, 2, 3, 1, 3, 3, 3, 2, 1, 1, 3]
def baseStart_5326049 : Nat := 118140960795 + 5326049 * 2 ^ 59
def prefixEnd_5326049 : Nat := 4983230072969 + 3 ^ 40 * 5326049 * 2
def baseEnd_5326049 : Nat := 2734823126398337542493453

theorem tailTrace_5326049 : CollatzResearch.WordTrace tailWord_5326049 prefixEnd_5326049 2734823126398337542493453 := by
  unfold tailWord_5326049
  simp only [CollatzResearch.WordTrace]
  refine ⟨194256965881641564596021201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129504643921094376397347467 194256965881641564596021201)
  ·
    refine ⟨145692724411231173447015901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194256965881641564596021201 145692724411231173447015901)
    ·
      refine ⟨54634771654211690042630963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145692724411231173447015901 54634771654211690042630963)
      ·
        refine ⟨81952157481317535063946445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54634771654211690042630963 81952157481317535063946445)
        ·
          refine ⟨30732059055494075648979917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81952157481317535063946445 30732059055494075648979917)
          ·
            refine ⟨11524522145810278368367469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30732059055494075648979917 11524522145810278368367469)
            ·
              refine ⟨4321695804678854388137801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11524522145810278368367469 4321695804678854388137801)
              ·
                refine ⟨3241271853509140791103351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4321695804678854388137801 3241271853509140791103351)
                ·
                  refine ⟨4861907780263711186655027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3241271853509140791103351 4861907780263711186655027)
                  ·
                    refine ⟨7292861670395566779982541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4861907780263711186655027 7292861670395566779982541)
                    ·
                      refine ⟨2734823126398337542493453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7292861670395566779982541 2734823126398337542493453)
                      ·
                        rfl

theorem cell23_5326049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 3, 2, 1, 1, 3].length) (baseStart_5326049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5326049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5326049 prefixEnd_5326049 := by exact prefixLift 5326049
  have htrace : WordTrace (prefixWord ++ tailWord_5326049) baseStart_5326049 baseEnd_5326049 := by
    simpa [prefixWord, tailWord_5326049, baseEnd_5326049] using wordTrace_append hprefix tailTrace_5326049
  have hstable : (prefixWord ++ tailWord_5326049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5326049).length < 2 ^ (prefixWord ++ tailWord_5326049).sum := by decide
  have hdescent : baseEnd_5326049 < baseStart_5326049 := by decide
  rcases family_descends (prefixWord ++ tailWord_5326049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5326058 : List Nat := [3, 1, 3, 1, 1, 3, 2, 2, 1, 1, 5]
def baseStart_5326058 : Nat := 118140960795 + 5326058 * 2 ^ 59
def prefixEnd_5326058 : Nat := 4983230072969 + 3 ^ 40 * 5326058 * 2
def baseEnd_5326058 : Nat := 2734827747724228007280911

theorem tailTrace_5326058 : CollatzResearch.WordTrace tailWord_5326058 prefixEnd_5326058 2734827747724228007280911 := by
  unfold tailWord_5326058
  simp only [CollatzResearch.WordTrace]
  refine ⟨48564323534652239783274707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129504862759072639422065885 48564323534652239783274707)
  ·
    refine ⟨72846485301978359674912061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48564323534652239783274707 72846485301978359674912061)
    ·
      refine ⟨27317431988241884878092023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72846485301978359674912061 27317431988241884878092023)
      ·
        refine ⟨40976147982362827317138035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27317431988241884878092023 40976147982362827317138035)
        ·
          refine ⟨61464221973544240975707053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40976147982362827317138035 61464221973544240975707053)
          ·
            refine ⟨23049083240079090365890145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61464221973544240975707053 23049083240079090365890145)
            ·
              refine ⟨17286812430059317774417609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23049083240079090365890145 17286812430059317774417609)
              ·
                refine ⟨12965109322544488330813207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17286812430059317774417609 12965109322544488330813207)
                ·
                  refine ⟨19447663983816732496219811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12965109322544488330813207 19447663983816732496219811)
                  ·
                    refine ⟨29171495975725098744329717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19447663983816732496219811 29171495975725098744329717)
                    ·
                      refine ⟨2734827747724228007280911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29171495975725098744329717 2734827747724228007280911)
                      ·
                        rfl

theorem cell23_5326058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 2, 1, 1, 5].length) (baseStart_5326058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5326058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5326058 prefixEnd_5326058 := by exact prefixLift 5326058
  have htrace : WordTrace (prefixWord ++ tailWord_5326058) baseStart_5326058 baseEnd_5326058 := by
    simpa [prefixWord, tailWord_5326058, baseEnd_5326058] using wordTrace_append hprefix tailTrace_5326058
  have hstable : (prefixWord ++ tailWord_5326058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5326058).length < 2 ^ (prefixWord ++ tailWord_5326058).sum := by decide
  have hdescent : baseEnd_5326058 < baseStart_5326058 := by decide
  rcases family_descends (prefixWord ++ tailWord_5326058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5326078 : List Nat := [4, 2, 2, 1, 1, 2, 2, 9]
def baseStart_5326078 : Nat := 118140960795 + 5326078 * 2 ^ 59
def prefixEnd_5326078 : Nat := 4983230072969 + 3 ^ 40 * 5326078 * 2
def baseEnd_5326078 : Nat := 101290296938419182556697

theorem tailTrace_5326078 : CollatzResearch.WordTrace tailWord_5326078 prefixEnd_5326078 101290296938419182556697 := by
  unfold tailWord_5326078
  simp only [CollatzResearch.WordTrace]
  refine ⟨24282252949817062818603361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129505349065691001699217925 24282252949817062818603361)
  ·
    refine ⟨18211689712362797113952521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24282252949817062818603361 18211689712362797113952521)
    ·
      refine ⟨13658767284272097835464391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18211689712362797113952521 13658767284272097835464391)
      ·
        refine ⟨20488150926408146753196587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13658767284272097835464391 20488150926408146753196587)
        ·
          refine ⟨30732226389612220129794881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20488150926408146753196587 30732226389612220129794881)
          ·
            refine ⟨23049169792209165097346161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30732226389612220129794881 23049169792209165097346161)
            ·
              refine ⟨17286877344156873823009621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23049169792209165097346161 17286877344156873823009621)
              ·
                refine ⟨101290296938419182556697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17286877344156873823009621 101290296938419182556697)
                ·
                  rfl

theorem cell23_5326078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 9].length) (baseStart_5326078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5326078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5326078 prefixEnd_5326078 := by exact prefixLift 5326078
  have htrace : WordTrace (prefixWord ++ tailWord_5326078) baseStart_5326078 baseEnd_5326078 := by
    simpa [prefixWord, tailWord_5326078, baseEnd_5326078] using wordTrace_append hprefix tailTrace_5326078
  have hstable : (prefixWord ++ tailWord_5326078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5326078).length < 2 ^ (prefixWord ++ tailWord_5326078).sum := by decide
  have hdescent : baseEnd_5326078 < baseStart_5326078 := by decide
  rcases family_descends (prefixWord ++ tailWord_5326078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5326092 : List Nat := [2, 2, 1, 2, 2, 4, 3, 1, 1, 2, 3]
def baseStart_5326092 : Nat := 118140960795 + 5326092 * 2 ^ 59
def prefixEnd_5326092 : Nat := 4983230072969 + 3 ^ 40 * 5326092 * 2
def baseEnd_5326092 : Nat := 2734845206066480874255755

theorem tailTrace_5326092 : CollatzResearch.WordTrace tailWord_5326092 prefixEnd_5326092 2734845206066480874255755 := by
  unfold tailWord_5326092
  simp only [CollatzResearch.WordTrace]
  refine ⟨97129267110242891469918265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129505689480323855293224353 97129267110242891469918265)
  ·
    refine ⟨72846950332682168602438699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97129267110242891469918265 72846950332682168602438699)
    ·
      refine ⟨109270425499023252903658049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72846950332682168602438699 109270425499023252903658049)
      ·
        refine ⟨81952819124267439677743537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109270425499023252903658049 81952819124267439677743537)
        ·
          refine ⟨61464614343200579758307653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81952819124267439677743537 61464614343200579758307653)
          ·
            refine ⟨11524615189350108704682685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61464614343200579758307653 11524615189350108704682685)
            ·
              refine ⟨4321730696006290764256007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11524615189350108704682685 4321730696006290764256007)
              ·
                refine ⟨6482596044009436146384011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4321730696006290764256007 6482596044009436146384011)
                ·
                  refine ⟨9723894066014154219576017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6482596044009436146384011 9723894066014154219576017)
                  ·
                    refine ⟨7292920549510615664682013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9723894066014154219576017 7292920549510615664682013)
                    ·
                      refine ⟨2734845206066480874255755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7292920549510615664682013 2734845206066480874255755)
                      ·
                        rfl

theorem cell23_5326092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 3, 1, 1, 2, 3].length) (baseStart_5326092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5326092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5326092 prefixEnd_5326092 := by exact prefixLift 5326092
  have htrace : WordTrace (prefixWord ++ tailWord_5326092) baseStart_5326092 baseEnd_5326092 := by
    simpa [prefixWord, tailWord_5326092, baseEnd_5326092] using wordTrace_append hprefix tailTrace_5326092
  have hstable : (prefixWord ++ tailWord_5326092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5326092).length < 2 ^ (prefixWord ++ tailWord_5326092).sum := by decide
  have hdescent : baseEnd_5326092 < baseStart_5326092 := by decide
  rcases family_descends (prefixWord ++ tailWord_5326092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5326106 : List Nat := [3, 1, 1, 3, 3, 1, 4, 2, 1, 2, 2]
def baseStart_5326106 : Nat := 118140960795 + 5326106 * 2 ^ 59
def prefixEnd_5326106 : Nat := 4983230072969 + 3 ^ 40 * 5326106 * 2
def baseEnd_5326106 : Nat := 2734852394795643819480691

theorem tailTrace_5326106 : CollatzResearch.WordTrace tailWord_5326106 prefixEnd_5326106 2734852394795643819480691 := by
  unfold tailWord_5326106
  simp only [CollatzResearch.WordTrace]
  refine ⟨48564761210608765832711543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129506029894956708887230781 48564761210608765832711543)
  ·
    refine ⟨72847141815913148749067315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48564761210608765832711543 72847141815913148749067315)
    ·
      refine ⟨109270712723869723123600973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72847141815913148749067315 109270712723869723123600973)
      ·
        refine ⟨40976517271451146171350365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109270712723869723123600973 40976517271451146171350365)
        ·
          refine ⟨15366193976794179814256387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40976517271451146171350365 15366193976794179814256387)
          ·
            refine ⟨23049290965191269721384581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15366193976794179814256387 23049290965191269721384581)
            ·
              refine ⟨4321742055973363072759609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23049290965191269721384581 4321742055973363072759609)
              ·
                refine ⟨3241306541980022304569707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4321742055973363072759609 3241306541980022304569707)
                ·
                  refine ⟨4861959812970033456854561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3241306541980022304569707 4861959812970033456854561)
                  ·
                    refine ⟨3646469859727525092640921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4861959812970033456854561 3646469859727525092640921)
                    ·
                      refine ⟨2734852394795643819480691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3646469859727525092640921 2734852394795643819480691)
                      ·
                        rfl

theorem cell23_5326106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 4, 2, 1, 2, 2].length) (baseStart_5326106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5326106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5326106 prefixEnd_5326106 := by exact prefixLift 5326106
  have htrace : WordTrace (prefixWord ++ tailWord_5326106) baseStart_5326106 baseEnd_5326106 := by
    simpa [prefixWord, tailWord_5326106, baseEnd_5326106] using wordTrace_append hprefix tailTrace_5326106
  have hstable : (prefixWord ++ tailWord_5326106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5326106).length < 2 ^ (prefixWord ++ tailWord_5326106).sum := by decide
  have hdescent : baseEnd_5326106 < baseStart_5326106 := by decide
  rcases family_descends (prefixWord ++ tailWord_5326106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5326115 : List Nat := [1, 1, 1, 4, 2, 3, 1, 2, 3, 3, 2]
def baseStart_5326115 : Nat := 118140960795 + 5326115 * 2 ^ 59
def prefixEnd_5326115 : Nat := 4983230072969 + 3 ^ 40 * 5326115 * 2
def baseEnd_5326115 : Nat := 2734857016121534284268149

theorem tailTrace_5326115 : CollatzResearch.WordTrace tailWord_5326115 prefixEnd_5326115 2734857016121534284268149 := by
  unfold tailWord_5326115
  simp only [CollatzResearch.WordTrace]
  refine ⟨194259373099402457867923799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129506248732934971911949199 194259373099402457867923799)
  ·
    refine ⟨291389059649103686801885699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194259373099402457867923799 291389059649103686801885699)
    ·
      refine ⟨437083589473655530202828549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 291389059649103686801885699 437083589473655530202828549)
      ·
        refine ⟨81953173026310411913030353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 437083589473655530202828549 81953173026310411913030353)
        ·
          refine ⟨61464879769732808934772765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81953173026310411913030353 61464879769732808934772765)
          ·
            refine ⟨23049329913649803350539787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61464879769732808934772765 23049329913649803350539787)
            ·
              refine ⟨34573994870474705025809681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23049329913649803350539787 34573994870474705025809681)
              ·
                refine ⟨25930496152856028769357261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34573994870474705025809681 25930496152856028769357261)
                ·
                  refine ⟨9723936057321010788508973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25930496152856028769357261 9723936057321010788508973)
                  ·
                    refine ⟨3646476021495379045690865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9723936057321010788508973 3646476021495379045690865)
                    ·
                      refine ⟨2734857016121534284268149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3646476021495379045690865 2734857016121534284268149)
                      ·
                        rfl

theorem cell23_5326115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 2, 3, 3, 2].length) (baseStart_5326115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5326115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5326115 prefixEnd_5326115 := by exact prefixLift 5326115
  have htrace : WordTrace (prefixWord ++ tailWord_5326115) baseStart_5326115 baseEnd_5326115 := by
    simpa [prefixWord, tailWord_5326115, baseEnd_5326115] using wordTrace_append hprefix tailTrace_5326115
  have hstable : (prefixWord ++ tailWord_5326115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5326115).length < 2 ^ (prefixWord ++ tailWord_5326115).sum := by decide
  have hdescent : baseEnd_5326115 < baseStart_5326115 := by decide
  rcases family_descends (prefixWord ++ tailWord_5326115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5326122 : List Nat := [3, 1, 4, 2, 1, 2, 2, 1, 1, 3, 3]
def baseStart_5326122 : Nat := 118140960795 + 5326122 * 2 ^ 59
def prefixEnd_5326122 : Nat := 4983230072969 + 3 ^ 40 * 5326122 * 2
def baseEnd_5326122 : Nat := 2734860610486115756880617

theorem tailTrace_5326122 : CollatzResearch.WordTrace tailWord_5326122 prefixEnd_5326122 2734860610486115756880617 := by
  unfold tailWord_5326122
  simp only [CollatzResearch.WordTrace]
  refine ⟨48564907102594274515857155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129506418940251398708952413 48564907102594274515857155)
  ·
    refine ⟨72847360653891411773785733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48564907102594274515857155 72847360653891411773785733)
    ·
      refine ⟨13658880122604639707584825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72847360653891411773785733 13658880122604639707584825)
      ·
        refine ⟨10244160091953479780688619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13658880122604639707584825 10244160091953479780688619)
        ·
          refine ⟨15366240137930219671032929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10244160091953479780688619 15366240137930219671032929)
          ·
            refine ⟨11524680103447664753274697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15366240137930219671032929 11524680103447664753274697)
            ·
              refine ⟨8643510077585748564956023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11524680103447664753274697 8643510077585748564956023)
              ·
                refine ⟨12965265116378622847434035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8643510077585748564956023 12965265116378622847434035)
                ·
                  refine ⟨19447897674567934271151053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12965265116378622847434035 19447897674567934271151053)
                  ·
                    refine ⟨7292961627962975351681645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19447897674567934271151053 7292961627962975351681645)
                    ·
                      refine ⟨2734860610486115756880617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7292961627962975351681645 2734860610486115756880617)
                      ·
                        rfl

theorem cell23_5326122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_5326122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5326122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5326122 prefixEnd_5326122 := by exact prefixLift 5326122
  have htrace : WordTrace (prefixWord ++ tailWord_5326122) baseStart_5326122 baseEnd_5326122 := by
    simpa [prefixWord, tailWord_5326122, baseEnd_5326122] using wordTrace_append hprefix tailTrace_5326122
  have hstable : (prefixWord ++ tailWord_5326122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5326122).length < 2 ^ (prefixWord ++ tailWord_5326122).sum := by decide
  have hdescent : baseEnd_5326122 < baseStart_5326122 := by decide
  rcases family_descends (prefixWord ++ tailWord_5326122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5326132 : List Nat := [2, 5, 1, 1, 1, 1, 1, 3, 3, 3, 2]
def baseStart_5326132 : Nat := 118140960795 + 5326132 * 2 ^ 59
def prefixEnd_5326132 : Nat := 4983230072969 + 3 ^ 40 * 5326132 * 2
def baseEnd_5326132 : Nat := 2734865745292660717755571

theorem tailTrace_5326132 : CollatzResearch.WordTrace tailWord_5326132 prefixEnd_5326132 2734865745292660717755571 := by
  unfold tailWord_5326132
  simp only [CollatzResearch.WordTrace]
  refine ⟨97129996570170434885646325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129506662093560579847528433 97129996570170434885646325)
  ·
    refine ⟨9105937178453478270529343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 97129996570170434885646325 9105937178453478270529343)
    ·
      refine ⟨13658905767680217405794015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9105937178453478270529343 13658905767680217405794015)
      ·
        refine ⟨20488358651520326108691023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13658905767680217405794015 20488358651520326108691023)
        ·
          refine ⟨30732537977280489163036535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20488358651520326108691023 30732537977280489163036535)
          ·
            refine ⟨46098806965920733744554803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30732537977280489163036535 46098806965920733744554803)
            ·
              refine ⟨69148210448881100616832205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46098806965920733744554803 69148210448881100616832205)
              ·
                refine ⟨25930578918330412731312077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69148210448881100616832205 25930578918330412731312077)
                ·
                  refine ⟨9723967094373904774242029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25930578918330412731312077 9723967094373904774242029)
                  ·
                    refine ⟨3646487660390214290340761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9723967094373904774242029 3646487660390214290340761)
                    ·
                      refine ⟨2734865745292660717755571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3646487660390214290340761 2734865745292660717755571)
                      ·
                        rfl

theorem cell23_5326132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 3, 3, 3, 2].length) (baseStart_5326132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5326132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5326132 prefixEnd_5326132 := by exact prefixLift 5326132
  have htrace : WordTrace (prefixWord ++ tailWord_5326132) baseStart_5326132 baseEnd_5326132 := by
    simpa [prefixWord, tailWord_5326132, baseEnd_5326132] using wordTrace_append hprefix tailTrace_5326132
  have hstable : (prefixWord ++ tailWord_5326132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5326132).length < 2 ^ (prefixWord ++ tailWord_5326132).sum := by decide
  have hdescent : baseEnd_5326132 < baseStart_5326132 := by decide
  rcases family_descends (prefixWord ++ tailWord_5326132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5326158 : List Nat := [4, 1, 1, 1, 1, 1, 3, 1, 4, 2, 4]
def baseStart_5326158 : Nat := 118140960795 + 5326158 * 2 ^ 59
def prefixEnd_5326158 : Nat := 4983230072969 + 3 ^ 40 * 5326158 * 2
def baseEnd_5326158 : Nat := 2734879095789677616030451

theorem tailTrace_5326158 : CollatzResearch.WordTrace tailWord_5326158 prefixEnd_5326158 2734879095789677616030451 := by
  unfold tailWord_5326158
  simp only [CollatzResearch.WordTrace]
  refine ⟨24282617679780834526467391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129507294292164450807826085 24282617679780834526467391)
  ·
    refine ⟨36423926519671251789701087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24282617679780834526467391 36423926519671251789701087)
    ·
      refine ⟨54635889779506877684551631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36423926519671251789701087 54635889779506877684551631)
      ·
        refine ⟨81953834669260316526827447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54635889779506877684551631 81953834669260316526827447)
        ·
          refine ⟨122930752003890474790241171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81953834669260316526827447 122930752003890474790241171)
          ·
            refine ⟨184396128005835712185361757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122930752003890474790241171 184396128005835712185361757)
            ·
              refine ⟨69148548002188392069510659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 184396128005835712185361757 69148548002188392069510659)
              ·
                refine ⟨103722822003282588104265989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69148548002188392069510659 103722822003282588104265989)
                ·
                  refine ⟨19448029125615485269549873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 103722822003282588104265989 19448029125615485269549873)
                  ·
                    refine ⟨14586021844211613952162405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19448029125615485269549873 14586021844211613952162405)
                    ·
                      refine ⟨2734879095789677616030451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14586021844211613952162405 2734879095789677616030451)
                      ·
                        rfl

theorem cell23_5326158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 4, 2, 4].length) (baseStart_5326158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5326158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5326158 prefixEnd_5326158 := by exact prefixLift 5326158
  have htrace : WordTrace (prefixWord ++ tailWord_5326158) baseStart_5326158 baseEnd_5326158 := by
    simpa [prefixWord, tailWord_5326158, baseEnd_5326158] using wordTrace_append hprefix tailTrace_5326158
  have hstable : (prefixWord ++ tailWord_5326158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5326158).length < 2 ^ (prefixWord ++ tailWord_5326158).sum := by decide
  have hdescent : baseEnd_5326158 < baseStart_5326158 := by decide
  rcases family_descends (prefixWord ++ tailWord_5326158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5326168 : List Nat := [2, 1, 2, 2, 1, 1, 6, 1, 7]
def baseStart_5326168 : Nat := 118140960795 + 5326168 * 2 ^ 59
def prefixEnd_5326168 : Nat := 4983230072969 + 3 ^ 40 * 5326168 * 2
def baseEnd_5326168 : Nat := 303876025621802508545045

theorem tailTrace_5326168 : CollatzResearch.WordTrace tailWord_5326168 prefixEnd_5326168 303876025621802508545045 := by
  unfold tailWord_5326168
  simp only [CollatzResearch.WordTrace]
  refine ⟨97130653084105223959801579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129507537445473631946402105 97130653084105223959801579)
  ·
    refine ⟨145695979626157835939702369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97130653084105223959801579 145695979626157835939702369)
    ·
      refine ⟨109271984719618376954776777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145695979626157835939702369 109271984719618376954776777)
      ·
        refine ⟨81953988539713782716082583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109271984719618376954776777 81953988539713782716082583)
        ·
          refine ⟨122930982809570674074123875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81953988539713782716082583 122930982809570674074123875)
          ·
            refine ⟨184396474214356011111185813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122930982809570674074123875 184396474214356011111185813)
            ·
              refine ⟨8643584728797938020836835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 184396474214356011111185813 8643584728797938020836835)
              ·
                refine ⟨12965377093196907031255253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8643584728797938020836835 12965377093196907031255253)
                ·
                  refine ⟨303876025621802508545045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12965377093196907031255253 303876025621802508545045)
                  ·
                    rfl

theorem cell23_5326168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 1, 7].length) (baseStart_5326168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5326168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5326168 prefixEnd_5326168 := by exact prefixLift 5326168
  have htrace : WordTrace (prefixWord ++ tailWord_5326168) baseStart_5326168 baseEnd_5326168 := by
    simpa [prefixWord, tailWord_5326168, baseEnd_5326168] using wordTrace_append hprefix tailTrace_5326168
  have hstable : (prefixWord ++ tailWord_5326168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5326168).length < 2 ^ (prefixWord ++ tailWord_5326168).sum := by decide
  have hdescent : baseEnd_5326168 < baseStart_5326168 := by decide
  rcases family_descends (prefixWord ++ tailWord_5326168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5326173 : List Nat := [1, 4, 5, 1, 2, 1, 1, 1, 1, 3, 3]
def baseStart_5326173 : Nat := 118140960795 + 5326173 * 2 ^ 59
def prefixEnd_5326173 : Nat := 4983230072969 + 3 ^ 40 * 5326173 * 2
def baseEnd_5326173 : Nat := 2734886797999495057342883

theorem tailTrace_5326173 : CollatzResearch.WordTrace tailWord_5326173 prefixEnd_5326173 2734886797999495057342883 := by
  unfold tailWord_5326173
  simp only [CollatzResearch.WordTrace]
  refine ⟨194261488533192333773535173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129507659022128222515690115 194261488533192333773535173)
  ·
    refine ⟨36424029099973562582537845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 194261488533192333773535173 36424029099973562582537845)
    ·
      refine ⟨3414752728122521492112923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 36424029099973562582537845 3414752728122521492112923)
      ·
        refine ⟨5122129092183782238169385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3414752728122521492112923 5122129092183782238169385)
        ·
          refine ⟨3841596819137836678627039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5122129092183782238169385 3841596819137836678627039)
          ·
            refine ⟨5762395228706755017940559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3841596819137836678627039 5762395228706755017940559)
            ·
              refine ⟨8643592843060132526910839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5762395228706755017940559 8643592843060132526910839)
              ·
                refine ⟨12965389264590198790366259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8643592843060132526910839 12965389264590198790366259)
                ·
                  refine ⟨19448083896885298185549389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12965389264590198790366259 19448083896885298185549389)
                  ·
                    refine ⟨7293031461331986819581021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19448083896885298185549389 7293031461331986819581021)
                    ·
                      refine ⟨2734886797999495057342883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7293031461331986819581021 2734886797999495057342883)
                      ·
                        rfl

theorem cell23_5326173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_5326173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5326173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5326173 prefixEnd_5326173 := by exact prefixLift 5326173
  have htrace : WordTrace (prefixWord ++ tailWord_5326173) baseStart_5326173 baseEnd_5326173 := by
    simpa [prefixWord, tailWord_5326173, baseEnd_5326173] using wordTrace_append hprefix tailTrace_5326173
  have hstable : (prefixWord ++ tailWord_5326173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5326173).length < 2 ^ (prefixWord ++ tailWord_5326173).sum := by decide
  have hdescent : baseEnd_5326173 < baseStart_5326173 := by decide
  rcases family_descends (prefixWord ++ tailWord_5326173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5326215 : List Nat := [1, 1, 4, 2, 2, 3, 1, 2, 2, 5]
def baseStart_5326215 : Nat := 118140960795 + 5326215 * 2 ^ 59
def prefixEnd_5326215 : Nat := 4983230072969 + 3 ^ 40 * 5326215 * 2
def baseEnd_5326215 : Nat := 911636121395661297672563

theorem tailTrace_5326215 : CollatzResearch.WordTrace tailWord_5326215 prefixEnd_5326215 911636121395661297672563 := by
  unfold tailWord_5326215
  simp only [CollatzResearch.WordTrace]
  refine ⟨194263020399040174946564099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129508680266026783297709399 194263020399040174946564099)
  ·
    refine ⟨291394530598560262419846149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194263020399040174946564099 291394530598560262419846149)
    ·
      refine ⟨54636474487230049203721153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 291394530598560262419846149 54636474487230049203721153)
      ·
        refine ⟨40977355865422536902790865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54636474487230049203721153 40977355865422536902790865)
        ·
          refine ⟨30733016899066902677093149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40977355865422536902790865 30733016899066902677093149)
          ·
            refine ⟨11524881337150088503909931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30733016899066902677093149 11524881337150088503909931)
            ·
              refine ⟨17287322005725132755864897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11524881337150088503909931 17287322005725132755864897)
              ·
                refine ⟨12965491504293849566898673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17287322005725132755864897 12965491504293849566898673)
                ·
                  refine ⟨9724118628220387175174005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12965491504293849566898673 9724118628220387175174005)
                  ·
                    refine ⟨911636121395661297672563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9724118628220387175174005 911636121395661297672563)
                    ·
                      rfl

theorem cell23_5326215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 2, 2, 5].length) (baseStart_5326215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5326215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5326215 prefixEnd_5326215 := by exact prefixLift 5326215
  have htrace : WordTrace (prefixWord ++ tailWord_5326215) baseStart_5326215 baseEnd_5326215 := by
    simpa [prefixWord, tailWord_5326215, baseEnd_5326215] using wordTrace_append hprefix tailTrace_5326215
  have hstable : (prefixWord ++ tailWord_5326215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5326215).length < 2 ^ (prefixWord ++ tailWord_5326215).sum := by decide
  have hdescent : baseEnd_5326215 < baseStart_5326215 := by decide
  rcases family_descends (prefixWord ++ tailWord_5326215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5326258 : List Nat := [3, 2, 1, 1, 1, 1, 2, 4, 8]
def baseStart_5326258 : Nat := 118140960795 + 5326258 * 2 ^ 59
def prefixEnd_5326258 : Nat := 4983230072969 + 3 ^ 40 * 5326258 * 2
def baseEnd_5326258 : Nat := 303881160428347469419999

theorem tailTrace_5326258 : CollatzResearch.WordTrace tailWord_5326258 prefixEnd_5326258 303881160428347469419999 := by
  unfold tailWord_5326258
  simp only [CollatzResearch.WordTrace]
  refine ⟨48566147184471098322594857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129509725825256262193586285 48566147184471098322594857)
  ·
    refine ⟨36424610388353323741946143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48566147184471098322594857 36424610388353323741946143)
    ·
      refine ⟨54636915582529985612919215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36424610388353323741946143 54636915582529985612919215)
      ·
        refine ⟨81955373373794978419378823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54636915582529985612919215 81955373373794978419378823)
        ·
          refine ⟨122933060060692467629068235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81955373373794978419378823 122933060060692467629068235)
          ·
            refine ⟨184399590091038701443602353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122933060060692467629068235 184399590091038701443602353)
            ·
              refine ⟨138299692568279026082701765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 184399590091038701443602353 138299692568279026082701765)
              ·
                refine ⟨25931192356552317390506581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 138299692568279026082701765 25931192356552317390506581)
                ·
                  refine ⟨303881160428347469419999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25931192356552317390506581 303881160428347469419999)
                  ·
                    rfl

theorem cell23_5326258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 4, 8].length) (baseStart_5326258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5326258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5326258 prefixEnd_5326258 := by exact prefixLift 5326258
  have htrace : WordTrace (prefixWord ++ tailWord_5326258) baseStart_5326258 baseEnd_5326258 := by
    simpa [prefixWord, tailWord_5326258, baseEnd_5326258] using wordTrace_append hprefix tailTrace_5326258
  have hstable : (prefixWord ++ tailWord_5326258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5326258).length < 2 ^ (prefixWord ++ tailWord_5326258).sum := by decide
  have hdescent : baseEnd_5326258 < baseStart_5326258 := by decide
  rcases family_descends (prefixWord ++ tailWord_5326258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5326305 : List Nat := [1, 2, 3, 1, 2, 3, 2, 1, 3, 5]
def baseStart_5326305 : Nat := 118140960795 + 5326305 * 2 ^ 59
def prefixEnd_5326305 : Nat := 4983230072969 + 3 ^ 40 * 5326305 * 2
def baseEnd_5326305 : Nat := 911651525815296180297425

theorem tailTrace_5326305 : CollatzResearch.WordTrace tailWord_5326305 prefixEnd_5326305 911651525815296180297425 := by
  unfold tailWord_5326305
  simp only [CollatzResearch.WordTrace]
  refine ⟨194266302968714120317340369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129510868645809413544893579 194266302968714120317340369)
  ·
    refine ⟨145699727226535590238005277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194266302968714120317340369 145699727226535590238005277)
    ·
      refine ⟨54637397709950846339251979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145699727226535590238005277 54637397709950846339251979)
      ·
        refine ⟨81956096564926269508877969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54637397709950846339251979 81956096564926269508877969)
        ·
          refine ⟨61467072423694702131658477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81956096564926269508877969 61467072423694702131658477)
          ·
            refine ⟨23050152158885513299371929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61467072423694702131658477 23050152158885513299371929)
            ·
              refine ⟨17287614119164134974528947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23050152158885513299371929 17287614119164134974528947)
              ·
                refine ⟨25931421178746202461793421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17287614119164134974528947 25931421178746202461793421)
                ·
                  refine ⟨9724282942029825923172533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25931421178746202461793421 9724282942029825923172533)
                  ·
                    refine ⟨911651525815296180297425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9724282942029825923172533 911651525815296180297425)
                    ·
                      rfl

theorem cell23_5326305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 1, 3, 5].length) (baseStart_5326305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5326305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5326305 prefixEnd_5326305 := by exact prefixLift 5326305
  have htrace : WordTrace (prefixWord ++ tailWord_5326305) baseStart_5326305 baseEnd_5326305 := by
    simpa [prefixWord, tailWord_5326305, baseEnd_5326305] using wordTrace_append hprefix tailTrace_5326305
  have hstable : (prefixWord ++ tailWord_5326305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5326305).length < 2 ^ (prefixWord ++ tailWord_5326305).sum := by decide
  have hdescent : baseEnd_5326305 < baseStart_5326305 := by decide
  rcases family_descends (prefixWord ++ tailWord_5326305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5326312 : List Nat := [2, 1, 4, 1, 1, 2, 3, 1, 1, 5, 2]
def baseStart_5326312 : Nat := 118140960795 + 5326312 * 2 ^ 59
def prefixEnd_5326312 : Nat := 4983230072969 + 3 ^ 40 * 5326312 * 2
def baseEnd_5326312 : Nat := 2734958171810470013504743

theorem tailTrace_5326312 : CollatzResearch.WordTrace tailWord_5326312 prefixEnd_5326312 2734958171810470013504743 := by
  unfold tailWord_5326312
  simp only [CollatzResearch.WordTrace]
  refine ⟨97133279139844380256422595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129511038853125840341896793 97133279139844380256422595)
  ·
    refine ⟨145699918709766570384633893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97133279139844380256422595 145699918709766570384633893)
    ·
      refine ⟨27318734758081231947118855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 145699918709766570384633893 27318734758081231947118855)
      ·
        refine ⟨40978102137121847920678283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27318734758081231947118855 40978102137121847920678283)
        ·
          refine ⟨61467153205682771881017425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40978102137121847920678283 61467153205682771881017425)
          ·
            refine ⟨46100364904262078910763069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61467153205682771881017425 46100364904262078910763069)
            ·
              refine ⟨17287636839098279591536151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46100364904262078910763069 17287636839098279591536151)
              ·
                refine ⟨25931455258647419387304227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17287636839098279591536151 25931455258647419387304227)
                ·
                  refine ⟨38897182887971129080956341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25931455258647419387304227 38897182887971129080956341)
                  ·
                    refine ⟨3646610895747293351339657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38897182887971129080956341 3646610895747293351339657)
                    ·
                      refine ⟨2734958171810470013504743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3646610895747293351339657 2734958171810470013504743)
                      ·
                        rfl

theorem cell23_5326312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 1, 1, 5, 2].length) (baseStart_5326312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5326312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5326312 prefixEnd_5326312 := by exact prefixLift 5326312
  have htrace : WordTrace (prefixWord ++ tailWord_5326312) baseStart_5326312 baseEnd_5326312 := by
    simpa [prefixWord, tailWord_5326312, baseEnd_5326312] using wordTrace_append hprefix tailTrace_5326312
  have hstable : (prefixWord ++ tailWord_5326312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5326312).length < 2 ^ (prefixWord ++ tailWord_5326312).sum := by decide
  have hdescent : baseEnd_5326312 < baseStart_5326312 := by decide
  rcases family_descends (prefixWord ++ tailWord_5326312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5326319 : List Nat := [1, 1, 2, 1, 4, 1, 3, 5, 1, 1, 3]
def baseStart_5326319 : Nat := 118140960795 + 5326319 * 2 ^ 59
def prefixEnd_5326319 : Nat := 4983230072969 + 3 ^ 40 * 5326319 * 2
def baseEnd_5326319 : Nat := 2734961766175051486117211

theorem tailTrace_5326319 : CollatzResearch.WordTrace tailWord_5326319 prefixEnd_5326319 2734961766175051486117211 := by
  unfold tailWord_5326319
  simp only [CollatzResearch.WordTrace]
  refine ⟨194266813590663400708350011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129511209060442267138900007 194266813590663400708350011)
  ·
    refine ⟨291400220385995101062525017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194266813590663400708350011 291400220385995101062525017)
    ·
      refine ⟨218550165289496325796893763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 291400220385995101062525017 218550165289496325796893763)
      ·
        refine ⟨327825247934244488695340645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218550165289496325796893763 327825247934244488695340645)
        ·
          refine ⟨61467233987670841630376371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 327825247934244488695340645 61467233987670841630376371)
          ·
            refine ⟨92200850981506262445564557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61467233987670841630376371 92200850981506262445564557)
            ·
              refine ⟨34575319118064848417086709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92200850981506262445564557 34575319118064848417086709)
              ·
                refine ⟨3241436167318579539101879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34575319118064848417086709 3241436167318579539101879)
                ·
                  refine ⟨4862154250977869308652819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3241436167318579539101879 4862154250977869308652819)
                  ·
                    refine ⟨7293231376466803962979229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4862154250977869308652819 7293231376466803962979229)
                    ·
                      refine ⟨2734961766175051486117211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7293231376466803962979229 2734961766175051486117211)
                      ·
                        rfl

theorem cell23_5326319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 5, 1, 1, 3].length) (baseStart_5326319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5326319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5326319 prefixEnd_5326319 := by exact prefixLift 5326319
  have htrace : WordTrace (prefixWord ++ tailWord_5326319) baseStart_5326319 baseEnd_5326319 := by
    simpa [prefixWord, tailWord_5326319, baseEnd_5326319] using wordTrace_append hprefix tailTrace_5326319
  have hstable : (prefixWord ++ tailWord_5326319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5326319).length < 2 ^ (prefixWord ++ tailWord_5326319).sum := by decide
  have hdescent : baseEnd_5326319 < baseStart_5326319 := by decide
  rcases family_descends (prefixWord ++ tailWord_5326319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5326345 : List Nat := [1, 2, 1, 1, 3, 1, 5, 2, 1, 1, 5]
def baseStart_5326345 : Nat := 118140960795 + 5326345 * 2 ^ 59
def prefixEnd_5326345 : Nat := 4983230072969 + 3 ^ 40 * 5326345 * 2
def baseEnd_5326345 : Nat := 2734975116672068384392091

theorem tailTrace_5326345 : CollatzResearch.WordTrace tailWord_5326345 prefixEnd_5326345 2734975116672068384392091 := by
  unfold tailWord_5326345
  simp only [CollatzResearch.WordTrace]
  refine ⟨194267761888569207148796489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129511841259046138099197659 194267761888569207148796489)
  ·
    refine ⟨145700821416426905361597367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194267761888569207148796489 145700821416426905361597367)
    ·
      refine ⟨218551232124640358042396051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145700821416426905361597367 218551232124640358042396051)
      ·
        refine ⟨327826848186960537063594077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218551232124640358042396051 327826848186960537063594077)
        ·
          refine ⟨122935068070110201398847779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 327826848186960537063594077 122935068070110201398847779)
          ·
            refine ⟨184402602105165302098271669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122935068070110201398847779 184402602105165302098271669)
            ·
              refine ⟨17287743947359247071712969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 184402602105165302098271669 17287743947359247071712969)
              ·
                refine ⟨12965807960519435303784727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17287743947359247071712969 12965807960519435303784727)
                ·
                  refine ⟨19448711940779152955677091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12965807960519435303784727 19448711940779152955677091)
                  ·
                    refine ⟨29173067911168729433515637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19448711940779152955677091 29173067911168729433515637)
                    ·
                      refine ⟨2734975116672068384392091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29173067911168729433515637 2734975116672068384392091)
                      ·
                        rfl

theorem cell23_5326345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 2, 1, 1, 5].length) (baseStart_5326345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5326345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5326345 prefixEnd_5326345 := by exact prefixLift 5326345
  have htrace : WordTrace (prefixWord ++ tailWord_5326345) baseStart_5326345 baseEnd_5326345 := by
    simpa [prefixWord, tailWord_5326345, baseEnd_5326345] using wordTrace_append hprefix tailTrace_5326345
  have hstable : (prefixWord ++ tailWord_5326345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5326345).length < 2 ^ (prefixWord ++ tailWord_5326345).sum := by decide
  have hdescent : baseEnd_5326345 < baseStart_5326345 := by decide
  rcases family_descends (prefixWord ++ tailWord_5326345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5326355 : List Nat := [1, 1, 1, 2, 1, 7, 1, 1, 1, 1, 6]
def baseStart_5326355 : Nat := 118140960795 + 5326355 * 2 ^ 59
def prefixEnd_5326355 : Nat := 4983230072969 + 3 ^ 40 * 5326355 * 2
def baseEnd_5326355 : Nat := 2734980251478613345267045

theorem tailTrace_5326355 : CollatzResearch.WordTrace tailWord_5326355 prefixEnd_5326355 2734980251478613345267045 := by
  unfold tailWord_5326355
  simp only [CollatzResearch.WordTrace]
  refine ⟨194268126618532978856660519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129512084412355319237773679 194268126618532978856660519)
  ·
    refine ⟨291402189927799468284990779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194268126618532978856660519 291402189927799468284990779)
    ·
      refine ⟨437103284891699202427486169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 291402189927799468284990779 437103284891699202427486169)
      ·
        refine ⟨327827463668774401820614627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 437103284891699202427486169 327827463668774401820614627)
        ·
          refine ⟨491741195503161602730921941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 327827463668774401820614627 491741195503161602730921941)
          ·
            refine ⟨11525184269605350064005983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 491741195503161602730921941 11525184269605350064005983)
            ·
              refine ⟨17287776404408025096008975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11525184269605350064005983 17287776404408025096008975)
              ·
                refine ⟨25931664606612037644013463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17287776404408025096008975 25931664606612037644013463)
                ·
                  refine ⟨38897496909918056466020195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25931664606612037644013463 38897496909918056466020195)
                  ·
                    refine ⟨58346245364877084699030293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38897496909918056466020195 58346245364877084699030293)
                    ·
                      refine ⟨2734980251478613345267045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58346245364877084699030293 2734980251478613345267045)
                      ·
                        rfl

theorem cell23_5326355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 1, 1, 1, 6].length) (baseStart_5326355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5326355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5326355 prefixEnd_5326355 := by exact prefixLift 5326355
  have htrace : WordTrace (prefixWord ++ tailWord_5326355) baseStart_5326355 baseEnd_5326355 := by
    simpa [prefixWord, tailWord_5326355, baseEnd_5326355] using wordTrace_append hprefix tailTrace_5326355
  have hstable : (prefixWord ++ tailWord_5326355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5326355).length < 2 ^ (prefixWord ++ tailWord_5326355).sum := by decide
  have hdescent : baseEnd_5326355 < baseStart_5326355 := by decide
  rcases family_descends (prefixWord ++ tailWord_5326355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5326356 : List Nat := [2, 4, 3, 1, 2, 1, 2, 2, 1, 5]
def baseStart_5326356 : Nat := 118140960795 + 5326356 * 2 ^ 59
def prefixEnd_5326356 : Nat := 4983230072969 + 3 ^ 40 * 5326356 * 2
def baseEnd_5326356 : Nat := 911660254986422613784847

theorem tailTrace_5326356 : CollatzResearch.WordTrace tailWord_5326356 prefixEnd_5326356 911660254986422613784847 := by
  unfold tailWord_5326356
  simp only [CollatzResearch.WordTrace]
  refine ⟨97134081545764678013723461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129512108727686237351631281 97134081545764678013723461)
  ·
    refine ⟨18212640289830877127573149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97134081545764678013723461 18212640289830877127573149)
    ·
      refine ⟨6829740108686578922839931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18212640289830877127573149 6829740108686578922839931)
      ·
        refine ⟨10244610163029868384259897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6829740108686578922839931 10244610163029868384259897)
        ·
          refine ⟨7683457622272401288194923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10244610163029868384259897 7683457622272401288194923)
          ·
            refine ⟨11525186433408601932292385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7683457622272401288194923 11525186433408601932292385)
            ·
              refine ⟨8643889825056451449219289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11525186433408601932292385 8643889825056451449219289)
              ·
                refine ⟨6482917368792338586914467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8643889825056451449219289 6482917368792338586914467)
                ·
                  refine ⟨9724376053188507880371701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6482917368792338586914467 9724376053188507880371701)
                  ·
                    refine ⟨911660254986422613784847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9724376053188507880371701 911660254986422613784847)
                    ·
                      rfl

theorem cell23_5326356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_5326356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5326356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5326356 prefixEnd_5326356 := by exact prefixLift 5326356
  have htrace : WordTrace (prefixWord ++ tailWord_5326356) baseStart_5326356 baseEnd_5326356 := by
    simpa [prefixWord, tailWord_5326356, baseEnd_5326356] using wordTrace_append hprefix tailTrace_5326356
  have hstable : (prefixWord ++ tailWord_5326356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5326356).length < 2 ^ (prefixWord ++ tailWord_5326356).sum := by decide
  have hdescent : baseEnd_5326356 < baseStart_5326356 := by decide
  rcases family_descends (prefixWord ++ tailWord_5326356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5326365 : List Nat := [1, 4, 2, 2, 1, 1, 3, 9]
def baseStart_5326365 : Nat := 118140960795 + 5326365 * 2 ^ 59
def prefixEnd_5326365 : Nat := 4983230072969 + 3 ^ 40 * 5326365 * 2
def baseEnd_5326365 : Nat := 101295755047598455783037

theorem tailTrace_5326365 : CollatzResearch.WordTrace tailWord_5326365 prefixEnd_5326365 101295755047598455783037 := by
  unfold tailWord_5326365
  simp only [CollatzResearch.WordTrace]
  refine ⟨194268491348496750564524549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129512327565664500376349699 194268491348496750564524549)
  ·
    refine ⟨36425342127843140730848353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 194268491348496750564524549 36425342127843140730848353)
    ·
      refine ⟨27319006595882355548136265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36425342127843140730848353 27319006595882355548136265)
      ·
        refine ⟨20489254946911766661102199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27319006595882355548136265 20489254946911766661102199)
        ·
          refine ⟨30733882420367649991653299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20489254946911766661102199 30733882420367649991653299)
          ·
            refine ⟨46100823630551474987479949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30733882420367649991653299 46100823630551474987479949)
            ·
              refine ⟨17287808861456803120304981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46100823630551474987479949 17287808861456803120304981)
              ·
                refine ⟨101295755047598455783037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17287808861456803120304981 101295755047598455783037)
                ·
                  rfl

theorem cell23_5326365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 9].length) (baseStart_5326365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5326365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5326365 prefixEnd_5326365 := by exact prefixLift 5326365
  have htrace : WordTrace (prefixWord ++ tailWord_5326365) baseStart_5326365 baseEnd_5326365 := by
    simpa [prefixWord, tailWord_5326365, baseEnd_5326365] using wordTrace_append hprefix tailTrace_5326365
  have hstable : (prefixWord ++ tailWord_5326365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5326365).length < 2 ^ (prefixWord ++ tailWord_5326365).sum := by decide
  have hdescent : baseEnd_5326365 < baseStart_5326365 := by decide
  rcases family_descends (prefixWord ++ tailWord_5326365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5326382 : List Nat := [4, 1, 3, 1, 2, 3, 9]
def baseStart_5326382 : Nat := 118140960795 + 5326382 * 2 ^ 59
def prefixEnd_5326382 : Nat := 4983230072969 + 3 ^ 40 * 5326382 * 2
def baseEnd_5326382 : Nat := 33765359450077589378141

theorem tailTrace_5326382 : CollatzResearch.WordTrace tailWord_5326382 prefixEnd_5326382 33765359450077589378141 := by
  unfold tailWord_5326382
  simp only [CollatzResearch.WordTrace]
  refine ⟨24283638923679395308486675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129512740926290108311928933 24283638923679395308486675)
  ·
    refine ⟨36425458385519092962730013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24283638923679395308486675 36425458385519092962730013)
    ·
      refine ⟨13659546894569659861023755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36425458385519092962730013 13659546894569659861023755)
      ·
        refine ⟨20489320341854489791535633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13659546894569659861023755 20489320341854489791535633)
        ·
          refine ⟨15366990256390867343651725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20489320341854489791535633 15366990256390867343651725)
          ·
            refine ⟨5762621346146575253869397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15366990256390867343651725 5762621346146575253869397)
            ·
              refine ⟨33765359450077589378141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5762621346146575253869397 33765359450077589378141)
              ·
                rfl

theorem cell23_5326382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 9].length) (baseStart_5326382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5326382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5326382 prefixEnd_5326382 := by exact prefixLift 5326382
  have htrace : WordTrace (prefixWord ++ tailWord_5326382) baseStart_5326382 baseEnd_5326382 := by
    simpa [prefixWord, tailWord_5326382, baseEnd_5326382] using wordTrace_append hprefix tailTrace_5326382
  have hstable : (prefixWord ++ tailWord_5326382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5326382).length < 2 ^ (prefixWord ++ tailWord_5326382).sum := by decide
  have hdescent : baseEnd_5326382 < baseStart_5326382 := by decide
  rcases family_descends (prefixWord ++ tailWord_5326382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5326413 : List Nat := [1, 6, 1, 1, 3, 2, 1, 2, 1, 2, 3]
def baseStart_5326413 : Nat := 118140960795 + 5326413 * 2 ^ 59
def prefixEnd_5326413 : Nat := 4983230072969 + 3 ^ 40 * 5326413 * 2
def baseEnd_5326413 : Nat := 2735010033356574118341779

theorem tailTrace_5326413 : CollatzResearch.WordTrace tailWord_5326413 prefixEnd_5326413 2735010033356574118341779 := by
  unfold tailWord_5326413
  simp only [CollatzResearch.WordTrace]
  refine ⟨194270242052322854762271893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129513494701548569841514595 194270242052322854762271893)
  ·
    refine ⟨9106417596202633816981495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 194270242052322854762271893 9106417596202633816981495)
    ·
      refine ⟨13659626394303950725472243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9106417596202633816981495 13659626394303950725472243)
      ·
        refine ⟨20489439591455926088208365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13659626394303950725472243 20489439591455926088208365)
        ·
          refine ⟨7683539846795972283078137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20489439591455926088208365 7683539846795972283078137)
          ·
            refine ⟨5762654885096979212308603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7683539846795972283078137 5762654885096979212308603)
            ·
              refine ⟨8643982327645468818462905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5762654885096979212308603 8643982327645468818462905)
              ·
                refine ⟨6482986745734101613847179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8643982327645468818462905 6482986745734101613847179)
                ·
                  refine ⟨9724480118601152420770769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6482986745734101613847179 9724480118601152420770769)
                  ·
                    refine ⟨7293360088950864315578077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9724480118601152420770769 7293360088950864315578077)
                    ·
                      refine ⟨2735010033356574118341779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7293360088950864315578077 2735010033356574118341779)
                      ·
                        rfl

theorem cell23_5326413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 2, 1, 2, 3].length) (baseStart_5326413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5326413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5326413 prefixEnd_5326413 := by exact prefixLift 5326413
  have htrace : WordTrace (prefixWord ++ tailWord_5326413) baseStart_5326413 baseEnd_5326413 := by
    simpa [prefixWord, tailWord_5326413, baseEnd_5326413] using wordTrace_append hprefix tailTrace_5326413
  have hstable : (prefixWord ++ tailWord_5326413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5326413).length < 2 ^ (prefixWord ++ tailWord_5326413).sum := by decide
  have hdescent : baseEnd_5326413 < baseStart_5326413 := by decide
  rcases family_descends (prefixWord ++ tailWord_5326413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5326449 : List Nat := [1, 2, 2, 2, 1, 1, 1, 5, 4, 2, 2]
def baseStart_5326449 : Nat := 118140960795 + 5326449 * 2 ^ 59
def prefixEnd_5326449 : Nat := 4983230072969 + 3 ^ 40 * 5326449 * 2
def baseEnd_5326449 : Nat := 2735028518660135977491613

theorem tailTrace_5326449 : CollatzResearch.WordTrace tailWord_5326449 prefixEnd_5326449 2735028518660135977491613 := by
  unfold tailWord_5326449
  simp only [CollatzResearch.WordTrace]
  refine ⟨194271555080192432910582401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129514370053461621940388267 194271555080192432910582401)
  ·
    refine ⟨145703666310144324682936801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194271555080192432910582401 145703666310144324682936801)
    ·
      refine ⟨109277749732608243512202601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145703666310144324682936801 109277749732608243512202601)
      ·
        refine ⟨81958312299456182634151951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109277749732608243512202601 81958312299456182634151951)
        ·
          refine ⟨122937468449184273951227927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81958312299456182634151951 122937468449184273951227927)
          ·
            refine ⟨184406202673776410926841891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122937468449184273951227927 184406202673776410926841891)
            ·
              refine ⟨276609304010664616390262837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 184406202673776410926841891 276609304010664616390262837)
              ·
                refine ⟨25932122250999807786587141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 276609304010664616390262837 25932122250999807786587141)
                ·
                  refine ⟨4862272922062463959985089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25932122250999807786587141 4862272922062463959985089)
                  ·
                    refine ⟨3646704691546847969988817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4862272922062463959985089 3646704691546847969988817)
                    ·
                      refine ⟨2735028518660135977491613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3646704691546847969988817 2735028518660135977491613)
                      ·
                        rfl

theorem cell23_5326449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 5, 4, 2, 2].length) (baseStart_5326449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5326449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5326449 prefixEnd_5326449 := by exact prefixLift 5326449
  have htrace : WordTrace (prefixWord ++ tailWord_5326449) baseStart_5326449 baseEnd_5326449 := by
    simpa [prefixWord, tailWord_5326449, baseEnd_5326449] using wordTrace_append hprefix tailTrace_5326449
  have hstable : (prefixWord ++ tailWord_5326449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5326449).length < 2 ^ (prefixWord ++ tailWord_5326449).sum := by decide
  have hdescent : baseEnd_5326449 < baseStart_5326449 := by decide
  rcases family_descends (prefixWord ++ tailWord_5326449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5326455 : List Nat := [1, 1, 3, 1, 1, 3, 1, 5, 7]
def baseStart_5326455 : Nat := 118140960795 + 5326455 * 2 ^ 59
def prefixEnd_5326455 : Nat := 4983230072969 + 3 ^ 40 * 5326455 * 2
def baseEnd_5326455 : Nat := 303892399949340328224065

theorem tailTrace_5326455 : CollatzResearch.WordTrace tailWord_5326455 prefixEnd_5326455 303892399949340328224065 := by
  unfold tailWord_5326455
  simp only [CollatzResearch.WordTrace]
  refine ⟨194271773918170695935300819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129514515945447130623533879 194271773918170695935300819)
  ·
    refine ⟨291407660877256043902951229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194271773918170695935300819 291407660877256043902951229)
    ·
      refine ⟨109277872828971016463606711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 291407660877256043902951229 109277872828971016463606711)
      ·
        refine ⟨163916809243456524695410067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109277872828971016463606711 163916809243456524695410067)
        ·
          refine ⟨245875213865184787043115101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163916809243456524695410067 245875213865184787043115101)
          ·
            refine ⟨92203205199444295141168163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 245875213865184787043115101 92203205199444295141168163)
            ·
              refine ⟨138304807799166442711752245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92203205199444295141168163 138304807799166442711752245)
              ·
                refine ⟨12966075731171854004226773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 138304807799166442711752245 12966075731171854004226773)
                ·
                  refine ⟨303892399949340328224065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12966075731171854004226773 303892399949340328224065)
                  ·
                    rfl

theorem cell23_5326455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 5, 7].length) (baseStart_5326455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5326455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5326455 prefixEnd_5326455 := by exact prefixLift 5326455
  have htrace : WordTrace (prefixWord ++ tailWord_5326455) baseStart_5326455 baseEnd_5326455 := by
    simpa [prefixWord, tailWord_5326455, baseEnd_5326455] using wordTrace_append hprefix tailTrace_5326455
  have hstable : (prefixWord ++ tailWord_5326455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5326455).length < 2 ^ (prefixWord ++ tailWord_5326455).sum := by decide
  have hdescent : baseEnd_5326455 < baseStart_5326455 := by decide
  rcases family_descends (prefixWord ++ tailWord_5326455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5326522 : List Nat := [3, 1, 1, 1, 2, 4, 1, 2, 1, 3, 4]
def baseStart_5326522 : Nat := 118140960795 + 5326522 * 2 ^ 59
def prefixEnd_5326522 : Nat := 4983230072969 + 3 ^ 40 * 5326522 * 2
def baseEnd_5326522 : Nat := 2735066002747914191878777

theorem tailTrace_5326522 : CollatzResearch.WordTrace tailWord_5326522 prefixEnd_5326522 2735066002747914191878777 := by
  unfold tailWord_5326522
  simp only [CollatzResearch.WordTrace]
  refine ⟨48568554402231991594497455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129516145072618644251993213 48568554402231991594497455)
  ·
    refine ⟨72852831603347987391746183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48568554402231991594497455 72852831603347987391746183)
    ·
      refine ⟨109279247405021981087619275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72852831603347987391746183 109279247405021981087619275)
      ·
        refine ⟨163918871107532971631428913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109279247405021981087619275 163918871107532971631428913)
        ·
          refine ⟨122939153330649728723571685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163918871107532971631428913 122939153330649728723571685)
          ·
            refine ⟨23051091249496824135669691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 122939153330649728723571685 23051091249496824135669691)
            ·
              refine ⟨34576636874245236203504537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23051091249496824135669691 34576636874245236203504537)
              ·
                refine ⟨25932477655683927152628403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34576636874245236203504537 25932477655683927152628403)
                ·
                  refine ⟨38898716483525890728942605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25932477655683927152628403 38898716483525890728942605)
                  ·
                    refine ⟨14587018681322209023353477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38898716483525890728942605 14587018681322209023353477)
                    ·
                      refine ⟨2735066002747914191878777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14587018681322209023353477 2735066002747914191878777)
                      ·
                        rfl

theorem cell23_5326522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 2, 1, 3, 4].length) (baseStart_5326522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5326522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5326522 prefixEnd_5326522 := by exact prefixLift 5326522
  have htrace : WordTrace (prefixWord ++ tailWord_5326522) baseStart_5326522 baseEnd_5326522 := by
    simpa [prefixWord, tailWord_5326522, baseEnd_5326522] using wordTrace_append hprefix tailTrace_5326522
  have hstable : (prefixWord ++ tailWord_5326522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5326522).length < 2 ^ (prefixWord ++ tailWord_5326522).sum := by decide
  have hdescent : baseEnd_5326522 < baseStart_5326522 := by decide
  rcases family_descends (prefixWord ++ tailWord_5326522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5326532 : List Nat := [2, 3, 3, 1, 1, 1, 1, 1, 2, 8]
def baseStart_5326532 : Nat := 118140960795 + 5326532 * 2 ^ 59
def prefixEnd_5326532 : Nat := 4983230072969 + 3 ^ 40 * 5326532 * 2
def baseEnd_5326532 : Nat := 911690379184819717584577

theorem tailTrace_5326532 : CollatzResearch.WordTrace tailWord_5326532 prefixEnd_5326532 911690379184819717584577 := by
  unfold tailWord_5326532
  simp only [CollatzResearch.WordTrace]
  refine ⟨97137291169445869042926925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129516388225927825390569233 97137291169445869042926925)
  ·
    refine ⟨36426484188542200891097597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97137291169445869042926925 36426484188542200891097597)
    ·
      refine ⟨13659931570703325334161599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36426484188542200891097597 13659931570703325334161599)
      ·
        refine ⟨20489897356054988001242399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13659931570703325334161599 20489897356054988001242399)
        ·
          refine ⟨30734846034082482001863599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20489897356054988001242399 30734846034082482001863599)
          ·
            refine ⟨46102269051123723002795399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30734846034082482001863599 46102269051123723002795399)
            ·
              refine ⟨69153403576685584504193099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46102269051123723002795399 69153403576685584504193099)
              ·
                refine ⟨103730105365028376756289649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69153403576685584504193099 103730105365028376756289649)
                ·
                  refine ⟨77797579023771282567217237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 103730105365028376756289649 77797579023771282567217237)
                  ·
                    refine ⟨911690379184819717584577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 77797579023771282567217237 911690379184819717584577)
                    ·
                      rfl

theorem cell23_5326532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_5326532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5326532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5326532 prefixEnd_5326532 := by exact prefixLift 5326532
  have htrace : WordTrace (prefixWord ++ tailWord_5326532) baseStart_5326532 baseEnd_5326532 := by
    simpa [prefixWord, tailWord_5326532, baseEnd_5326532] using wordTrace_append hprefix tailTrace_5326532
  have hstable : (prefixWord ++ tailWord_5326532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5326532).length < 2 ^ (prefixWord ++ tailWord_5326532).sum := by decide
  have hdescent : baseEnd_5326532 < baseStart_5326532 := by decide
  rcases family_descends (prefixWord ++ tailWord_5326532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5326559 : List Nat := [1, 1, 2, 3, 2, 2, 3, 2, 2, 2, 3]
def baseStart_5326559 : Nat := 118140960795 + 5326559 * 2 ^ 59
def prefixEnd_5326559 : Nat := 4983230072969 + 3 ^ 40 * 5326559 * 2
def baseEnd_5326559 : Nat := 2735085001532130547116107

theorem tailTrace_5326559 : CollatzResearch.WordTrace tailWord_5326559 prefixEnd_5326559 2735085001532130547116107 := by
  unfold tailWord_5326559
  simp only [CollatzResearch.WordTrace]
  refine ⟨194275567109793921697086731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129517044739862614464724487 194275567109793921697086731)
  ·
    refine ⟨291413350664690882545630097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194275567109793921697086731 291413350664690882545630097)
    ·
      refine ⟨218560012998518161909222573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 291413350664690882545630097 218560012998518161909222573)
      ·
        refine ⟨81960004874444310715958465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 218560012998518161909222573 81960004874444310715958465)
        ·
          refine ⟨61470003655833233036968849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81960004874444310715958465 61470003655833233036968849)
          ·
            refine ⟨46102502741874924777726637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61470003655833233036968849 46102502741874924777726637)
            ·
              refine ⟨17288438528203096791647489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46102502741874924777726637 17288438528203096791647489)
              ·
                refine ⟨12966328896152322593735617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17288438528203096791647489 12966328896152322593735617)
                ·
                  refine ⟨9724746672114241945301713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12966328896152322593735617 9724746672114241945301713)
                  ·
                    refine ⟨7293560004085681458976285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9724746672114241945301713 7293560004085681458976285)
                    ·
                      refine ⟨2735085001532130547116107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7293560004085681458976285 2735085001532130547116107)
                      ·
                        rfl

theorem cell23_5326559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 2, 2, 2, 3].length) (baseStart_5326559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5326559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5326559 prefixEnd_5326559 := by exact prefixLift 5326559
  have htrace : WordTrace (prefixWord ++ tailWord_5326559) baseStart_5326559 baseEnd_5326559 := by
    simpa [prefixWord, tailWord_5326559, baseEnd_5326559] using wordTrace_append hprefix tailTrace_5326559
  have hstable : (prefixWord ++ tailWord_5326559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5326559).length < 2 ^ (prefixWord ++ tailWord_5326559).sum := by decide
  have hdescent : baseEnd_5326559 < baseStart_5326559 := by decide
  rcases family_descends (prefixWord ++ tailWord_5326559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5326579 : List Nat := [1, 1, 1, 2, 2, 3, 6, 1, 6]
def baseStart_5326579 : Nat := 118140960795 + 5326579 * 2 ^ 59
def prefixEnd_5326579 : Nat := 4983230072969 + 3 ^ 40 * 5326579 * 2
def baseEnd_5326579 : Nat := 303899474571691163207335

theorem tailTrace_5326579 : CollatzResearch.WordTrace tailWord_5326579 prefixEnd_5326579 303899474571691163207335 := by
  unfold tailWord_5326579
  simp only [CollatzResearch.WordTrace]
  refine ⟨194276296569721465112814791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129517531046480976741876527 194276296569721465112814791)
  ·
    refine ⟨291414444854582197669222187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194276296569721465112814791 291414444854582197669222187)
    ·
      refine ⟨437121667281873296503833281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 291414444854582197669222187 437121667281873296503833281)
      ·
        refine ⟨327841250461404972377874961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 437121667281873296503833281 327841250461404972377874961)
        ·
          refine ⟨245880937846053729283406221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 327841250461404972377874961 245880937846053729283406221)
          ·
            refine ⟨92205351692270148481277333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 245880937846053729283406221 92205351692270148481277333)
            ·
              refine ⟨4322125860575163210059875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 92205351692270148481277333 4322125860575163210059875)
              ·
                refine ⟨6483188790862744815089813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4322125860575163210059875 6483188790862744815089813)
                ·
                  refine ⟨303899474571691163207335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6483188790862744815089813 303899474571691163207335)
                  ·
                    rfl

theorem cell23_5326579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 6, 1, 6].length) (baseStart_5326579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5326579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5326579 prefixEnd_5326579 := by exact prefixLift 5326579
  have htrace : WordTrace (prefixWord ++ tailWord_5326579) baseStart_5326579 baseEnd_5326579 := by
    simpa [prefixWord, tailWord_5326579, baseEnd_5326579] using wordTrace_append hprefix tailTrace_5326579
  have hstable : (prefixWord ++ tailWord_5326579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5326579).length < 2 ^ (prefixWord ++ tailWord_5326579).sum := by decide
  have hdescent : baseEnd_5326579 < baseStart_5326579 := by decide
  rcases family_descends (prefixWord ++ tailWord_5326579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5326592 : List Nat := [2, 1, 1, 2, 1, 1, 2, 5, 3, 5]
def baseStart_5326592 : Nat := 118140960795 + 5326592 * 2 ^ 59
def prefixEnd_5326592 : Nat := 4983230072969 + 3 ^ 40 * 5326592 * 2
def baseEnd_5326592 : Nat := 911700648797909639334485

theorem tailTrace_5326592 : CollatzResearch.WordTrace tailWord_5326592 prefixEnd_5326592 911700648797909639334485 := by
  unfold tailWord_5326592
  simp only [CollatzResearch.WordTrace]
  refine ⟨97138385359337184166519015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129517847145782912222025353 97138385359337184166519015)
  ·
    refine ⟨145707578039005776249778523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97138385359337184166519015 145707578039005776249778523)
    ·
      refine ⟨218561367058508664374667785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145707578039005776249778523 218561367058508664374667785)
      ·
        refine ⟨163921025293881498281000839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 218561367058508664374667785 163921025293881498281000839)
        ·
          refine ⟨245881537940822247421501259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163921025293881498281000839 245881537940822247421501259)
          ·
            refine ⟨368822306911233371132251889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 245881537940822247421501259 368822306911233371132251889)
            ·
              refine ⟨276616730183425028349188917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 368822306911233371132251889 276616730183425028349188917)
              ·
                refine ⟨25932818454696096407736461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 276616730183425028349188917 25932818454696096407736461)
                ·
                  refine ⟨9724806920511036152901173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25932818454696096407736461 9724806920511036152901173)
                  ·
                    refine ⟨911700648797909639334485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9724806920511036152901173 911700648797909639334485)
                    ·
                      rfl

theorem cell23_5326592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 5, 3, 5].length) (baseStart_5326592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5326592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5326592 prefixEnd_5326592 := by exact prefixLift 5326592
  have htrace : WordTrace (prefixWord ++ tailWord_5326592) baseStart_5326592 baseEnd_5326592 := by
    simpa [prefixWord, tailWord_5326592, baseEnd_5326592] using wordTrace_append hprefix tailTrace_5326592
  have hstable : (prefixWord ++ tailWord_5326592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5326592).length < 2 ^ (prefixWord ++ tailWord_5326592).sum := by decide
  have hdescent : baseEnd_5326592 < baseStart_5326592 := by decide
  rcases family_descends (prefixWord ++ tailWord_5326592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5326616 : List Nat := [2, 1, 2, 3, 1, 1, 4, 2, 2, 3, 2]
def baseStart_5326616 : Nat := 118140960795 + 5326616 * 2 ^ 59
def prefixEnd_5326616 : Nat := 4983230072969 + 3 ^ 40 * 5326616 * 2
def baseEnd_5326616 : Nat := 2735114269929436824103345

theorem tailTrace_5326616 : CollatzResearch.WordTrace tailWord_5326616 prefixEnd_5326616 2735114269929436824103345 := by
  unfold tailWord_5326616
  simp only [CollatzResearch.WordTrace]
  refine ⟨97138823035293710215955851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129518430713724946954607801 97138823035293710215955851)
  ·
    refine ⟨145708234552940565323933777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97138823035293710215955851 145708234552940565323933777)
    ·
      refine ⟨109281175914705423992950333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145708234552940565323933777 109281175914705423992950333)
      ·
        refine ⟨40980440968014533997356375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109281175914705423992950333 40980440968014533997356375)
        ·
          refine ⟨61470661452021800996034563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40980440968014533997356375 61470661452021800996034563)
          ·
            refine ⟨92205992178032701494051845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61470661452021800996034563 92205992178032701494051845)
            ·
              refine ⟨17288623533381131530134721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 92205992178032701494051845 17288623533381131530134721)
              ·
                refine ⟨12966467650035848647601041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17288623533381131530134721 12966467650035848647601041)
                ·
                  refine ⟨9724850737526886485700781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12966467650035848647601041 9724850737526886485700781)
                  ·
                    refine ⟨3646819026572582432137793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9724850737526886485700781 3646819026572582432137793)
                    ·
                      refine ⟨2735114269929436824103345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3646819026572582432137793 2735114269929436824103345)
                      ·
                        rfl

theorem cell23_5326616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 2, 2, 3, 2].length) (baseStart_5326616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5326616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5326616 prefixEnd_5326616 := by exact prefixLift 5326616
  have htrace : WordTrace (prefixWord ++ tailWord_5326616) baseStart_5326616 baseEnd_5326616 := by
    simpa [prefixWord, tailWord_5326616, baseEnd_5326616] using wordTrace_append hprefix tailTrace_5326616
  have hstable : (prefixWord ++ tailWord_5326616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5326616).length < 2 ^ (prefixWord ++ tailWord_5326616).sum := by decide
  have hdescent : baseEnd_5326616 < baseStart_5326616 := by decide
  rcases family_descends (prefixWord ++ tailWord_5326616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5326623 : List Nat := [1, 1, 2, 4, 2, 1, 3, 4, 1, 1, 3]
def baseStart_5326623 : Nat := 118140960795 + 5326623 * 2 ^ 59
def prefixEnd_5326623 : Nat := 4983230072969 + 3 ^ 40 * 5326623 * 2
def baseEnd_5326623 : Nat := 2735117864294018296715813

theorem tailTrace_5326623 : CollatzResearch.WordTrace tailWord_5326623 prefixEnd_5326623 2735117864294018296715813 := by
  unfold tailWord_5326623
  simp only [CollatzResearch.WordTrace]
  refine ⟨194277901381562060627416523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129518600921041373751611015 194277901381562060627416523)
  ·
    refine ⟨291416852072343090941124785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194277901381562060627416523 291416852072343090941124785)
    ·
      refine ⟨218562639054257318205843589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 291416852072343090941124785 218562639054257318205843589)
      ·
        refine ⟨40980494822673247163595673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 218562639054257318205843589 40980494822673247163595673)
        ·
          refine ⟨30735371117004935372696755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40980494822673247163595673 30735371117004935372696755)
          ·
            refine ⟨46103056675507403059045133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30735371117004935372696755 46103056675507403059045133)
            ·
              refine ⟨17288646253315276147141925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46103056675507403059045133 17288646253315276147141925)
              ·
                refine ⟨3241621172496614277589111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17288646253315276147141925 3241621172496614277589111)
                ·
                  refine ⟨4862431758744921416383667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3241621172496614277589111 4862431758744921416383667)
                  ·
                    refine ⟨7293647638117382124575501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4862431758744921416383667 7293647638117382124575501)
                    ·
                      refine ⟨2735117864294018296715813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7293647638117382124575501 2735117864294018296715813)
                      ·
                        rfl

theorem cell23_5326623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 4, 1, 1, 3].length) (baseStart_5326623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5326623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5326623 prefixEnd_5326623 := by exact prefixLift 5326623
  have htrace : WordTrace (prefixWord ++ tailWord_5326623) baseStart_5326623 baseEnd_5326623 := by
    simpa [prefixWord, tailWord_5326623, baseEnd_5326623] using wordTrace_append hprefix tailTrace_5326623
  have hstable : (prefixWord ++ tailWord_5326623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5326623).length < 2 ^ (prefixWord ++ tailWord_5326623).sum := by decide
  have hdescent : baseEnd_5326623 < baseStart_5326623 := by decide
  rcases family_descends (prefixWord ++ tailWord_5326623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
