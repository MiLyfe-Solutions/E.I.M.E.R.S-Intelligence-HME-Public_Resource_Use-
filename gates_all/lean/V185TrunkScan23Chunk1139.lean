import V185TrunkScan23Chunk1138

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6746901 : List Nat := [1, 3, 2, 1, 2, 2, 2, 3, 3, 4]
def baseStart_6746901 : Nat := 118140960795 + 6746901 * 2 ^ 59
def prefixEnd_6746901 : Nat := 4983230072969 + 3 ^ 40 * 6746901 * 2
def baseEnd_6746901 : Nat := 1154801047100137484169691

theorem tailTrace_6746901 : CollatzResearch.WordTrace tailWord_6746901 prefixEnd_6746901 1154801047100137484169691 := by
  unfold tailWord_6746901
  simp only [CollatzResearch.WordTrace]
  refine ⟨246079695730137430798296557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164053130486758287198864371 246079695730137430798296557)
  ·
    refine ⟨92279885898801536549361209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 246079695730137430798296557 92279885898801536549361209)
    ·
      refine ⟨69209914424101152412020907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92279885898801536549361209 69209914424101152412020907)
      ·
        refine ⟨103814871636151728618031361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69209914424101152412020907 103814871636151728618031361)
        ·
          refine ⟨77861153727113796463523521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103814871636151728618031361 77861153727113796463523521)
          ·
            refine ⟨58395865295335347347642641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77861153727113796463523521 58395865295335347347642641)
            ·
              refine ⟨43796898971501510510731981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58395865295335347347642641 43796898971501510510731981)
              ·
                refine ⟨16423837114313066441524493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43796898971501510510731981 16423837114313066441524493)
                ·
                  refine ⟨6158938917867399915571685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16423837114313066441524493 6158938917867399915571685)
                  ·
                    refine ⟨1154801047100137484169691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6158938917867399915571685 1154801047100137484169691)
                    ·
                      rfl

theorem cell23_6746901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 3, 3, 4].length) (baseStart_6746901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6746901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6746901 prefixEnd_6746901 := by exact prefixLift 6746901
  have htrace : WordTrace (prefixWord ++ tailWord_6746901) baseStart_6746901 baseEnd_6746901 := by
    simpa [prefixWord, tailWord_6746901, baseEnd_6746901] using wordTrace_append hprefix tailTrace_6746901
  have hstable : (prefixWord ++ tailWord_6746901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6746901).length < 2 ^ (prefixWord ++ tailWord_6746901).sum := by decide
  have hdescent : baseEnd_6746901 < baseStart_6746901 := by decide
  rcases family_descends (prefixWord ++ tailWord_6746901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6746904 : List Nat := [2, 1, 2, 3, 1, 1, 1, 2, 2, 4, 4]
def baseStart_6746904 : Nat := 118140960795 + 6746904 * 2 ^ 59
def prefixEnd_6746904 : Nat := 4983230072969 + 3 ^ 40 * 6746904 * 2
def baseEnd_6746904 : Nat := 3464404681742375940771559

theorem tailTrace_6746904 : CollatzResearch.WordTrace tailWord_6746904 prefixEnd_6746904 3464404681742375940771559 := by
  unfold tailWord_6746904
  simp only [CollatzResearch.WordTrace]
  refine ⟨123039902574563281155327883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164053203432751041540437177 123039902574563281155327883)
  ·
    refine ⟨184559853861844921732991825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123039902574563281155327883 184559853861844921732991825)
    ·
      refine ⟨138419890396383691299743869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184559853861844921732991825 138419890396383691299743869)
      ·
        refine ⟨51907458898643884237403951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138419890396383691299743869 51907458898643884237403951)
        ·
          refine ⟨77861188347965826356105927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51907458898643884237403951 77861188347965826356105927)
          ·
            refine ⟨116791782521948739534158891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77861188347965826356105927 116791782521948739534158891)
            ·
              refine ⟨175187673782923109301238337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116791782521948739534158891 175187673782923109301238337)
              ·
                refine ⟨131390755337192331975928753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 175187673782923109301238337 131390755337192331975928753)
                ·
                  refine ⟨98543066502894248981946565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 131390755337192331975928753 98543066502894248981946565)
                  ·
                    refine ⟨18476824969292671684114981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 98543066502894248981946565 18476824969292671684114981)
                    ·
                      refine ⟨3464404681742375940771559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18476824969292671684114981 3464404681742375940771559)
                      ·
                        rfl

theorem cell23_6746904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 2, 4, 4].length) (baseStart_6746904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6746904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6746904 prefixEnd_6746904 := by exact prefixLift 6746904
  have htrace : WordTrace (prefixWord ++ tailWord_6746904) baseStart_6746904 baseEnd_6746904 := by
    simpa [prefixWord, tailWord_6746904, baseEnd_6746904] using wordTrace_append hprefix tailTrace_6746904
  have hstable : (prefixWord ++ tailWord_6746904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6746904).length < 2 ^ (prefixWord ++ tailWord_6746904).sum := by decide
  have hdescent : baseEnd_6746904 < baseStart_6746904 := by decide
  rcases family_descends (prefixWord ++ tailWord_6746904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6746908 : List Nat := [2, 2, 3, 1, 1, 4, 1, 1, 2, 4, 2]
def baseStart_6746908 : Nat := 118140960795 + 6746908 * 2 ^ 59
def prefixEnd_6746908 : Nat := 4983230072969 + 3 ^ 40 * 6746908 * 2
def baseEnd_6746908 : Nat := 3464406735664993925121541

theorem tailTrace_6746908 : CollatzResearch.WordTrace tailWord_6746908 prefixEnd_6746908 3464406735664993925121541 := by
  unfold tailWord_6746908
  simp only [CollatzResearch.WordTrace]
  refine ⟨123039975520556035496900689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164053300694074713995867585 123039975520556035496900689)
  ·
    refine ⟨92279981640417026622675517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123039975520556035496900689 92279981640417026622675517)
    ·
      refine ⟨34604993115156384983503319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92279981640417026622675517 34604993115156384983503319)
      ·
        refine ⟨51907489672734577475254979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34604993115156384983503319 51907489672734577475254979)
        ·
          refine ⟨77861234509101866212882469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51907489672734577475254979 77861234509101866212882469)
          ·
            refine ⟨14598981470456599914915463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77861234509101866212882469 14598981470456599914915463)
            ·
              refine ⟨21898472205684899872373195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14598981470456599914915463 21898472205684899872373195)
              ·
                refine ⟨32847708308527349808559793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21898472205684899872373195 32847708308527349808559793)
                ·
                  refine ⟨24635781231395512356419845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32847708308527349808559793 24635781231395512356419845)
                  ·
                    refine ⟨4619208980886658566828721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24635781231395512356419845 4619208980886658566828721)
                    ·
                      refine ⟨3464406735664993925121541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4619208980886658566828721 3464406735664993925121541)
                      ·
                        rfl

theorem cell23_6746908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 1, 2, 4, 2].length) (baseStart_6746908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6746908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6746908 prefixEnd_6746908 := by exact prefixLift 6746908
  have htrace : WordTrace (prefixWord ++ tailWord_6746908) baseStart_6746908 baseEnd_6746908 := by
    simpa [prefixWord, tailWord_6746908, baseEnd_6746908] using wordTrace_append hprefix tailTrace_6746908
  have hstable : (prefixWord ++ tailWord_6746908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6746908).length < 2 ^ (prefixWord ++ tailWord_6746908).sum := by decide
  have hdescent : baseEnd_6746908 < baseStart_6746908 := by decide
  rcases family_descends (prefixWord ++ tailWord_6746908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6746922 : List Nat := [3, 1, 4, 3, 2, 1, 1, 1, 2, 5]
def baseStart_6746922 : Nat := 118140960795 + 6746922 * 2 ^ 59
def prefixEnd_6746922 : Nat := 4983230072969 + 3 ^ 40 * 6746922 * 2
def baseEnd_6746922 : Nat := 1154804641464718956782159

theorem tailTrace_6746922 : CollatzResearch.WordTrace tailWord_6746922 prefixEnd_6746922 1154804641464718956782159 := by
  unfold tailWord_6746922
  simp only [CollatzResearch.WordTrace]
  refine ⟨61520115415765337846202755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164053641108707567589874013 61520115415765337846202755)
  ·
    refine ⟨92280173123648006769304133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61520115415765337846202755 92280173123648006769304133)
    ·
      refine ⟨17302532460684001269244525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92280173123648006769304133 17302532460684001269244525)
      ·
        refine ⟨6488449672756500475966697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17302532460684001269244525 6488449672756500475966697)
        ·
          refine ⟨4866337254567375356975023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6488449672756500475966697 4866337254567375356975023)
          ·
            refine ⟨7299505881851063035462535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4866337254567375356975023 7299505881851063035462535)
            ·
              refine ⟨10949258822776594553193803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7299505881851063035462535 10949258822776594553193803)
              ·
                refine ⟨16423888234164891829790705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10949258822776594553193803 16423888234164891829790705)
                ·
                  refine ⟨12317916175623668872343029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16423888234164891829790705 12317916175623668872343029)
                  ·
                    refine ⟨1154804641464718956782159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12317916175623668872343029 1154804641464718956782159)
                    ·
                      rfl

theorem cell23_6746922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 1, 2, 5].length) (baseStart_6746922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6746922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6746922 prefixEnd_6746922 := by exact prefixLift 6746922
  have htrace : WordTrace (prefixWord ++ tailWord_6746922) baseStart_6746922 baseEnd_6746922 := by
    simpa [prefixWord, tailWord_6746922, baseEnd_6746922] using wordTrace_append hprefix tailTrace_6746922
  have hstable : (prefixWord ++ tailWord_6746922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6746922).length < 2 ^ (prefixWord ++ tailWord_6746922).sum := by decide
  have hdescent : baseEnd_6746922 < baseStart_6746922 := by decide
  rcases family_descends (prefixWord ++ tailWord_6746922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6746925 : List Nat := [1, 5, 3, 2, 1, 1, 1, 1, 1, 3, 4]
def baseStart_6746925 : Nat := 118140960795 + 6746925 * 2 ^ 59
def prefixEnd_6746925 : Nat := 4983230072969 + 3 ^ 40 * 6746925 * 2
def baseEnd_6746925 : Nat := 3464415464836120358608963

theorem tailTrace_6746925 : CollatzResearch.WordTrace tailWord_6746925 prefixEnd_6746925 3464415464836120358608963 := by
  unfold tailWord_6746925
  simp only [CollatzResearch.WordTrace]
  refine ⟨246080571082050482897170229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164053714054700321931446819 246080571082050482897170229)
  ·
    refine ⟨23070053538942232771609709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 246080571082050482897170229 23070053538942232771609709)
    ·
      refine ⟨8651270077103337289353641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23070053538942232771609709 8651270077103337289353641)
      ·
        refine ⟨6488452557827502967015231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8651270077103337289353641 6488452557827502967015231)
        ·
          refine ⟨9732678836741254450522847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6488452557827502967015231 9732678836741254450522847)
          ·
            refine ⟨14599018255111881675784271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9732678836741254450522847 14599018255111881675784271)
            ·
              refine ⟨21898527382667822513676407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14599018255111881675784271 21898527382667822513676407)
              ·
                refine ⟨32847791074001733770514611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21898527382667822513676407 32847791074001733770514611)
                ·
                  refine ⟨49271686611002600655771917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32847791074001733770514611 49271686611002600655771917)
                  ·
                    refine ⟨18476882479125975245914469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49271686611002600655771917 18476882479125975245914469)
                    ·
                      refine ⟨3464415464836120358608963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18476882479125975245914469 3464415464836120358608963)
                      ·
                        rfl

theorem cell23_6746925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_6746925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6746925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6746925 prefixEnd_6746925 := by exact prefixLift 6746925
  have htrace : WordTrace (prefixWord ++ tailWord_6746925) baseStart_6746925 baseEnd_6746925 := by
    simpa [prefixWord, tailWord_6746925, baseEnd_6746925] using wordTrace_append hprefix tailTrace_6746925
  have hstable : (prefixWord ++ tailWord_6746925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6746925).length < 2 ^ (prefixWord ++ tailWord_6746925).sum := by decide
  have hdescent : baseEnd_6746925 < baseStart_6746925 := by decide
  rcases family_descends (prefixWord ++ tailWord_6746925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6746954 : List Nat := [3, 1, 2, 1, 1, 1, 2, 2, 2, 1, 7]
def baseStart_6746954 : Nat := 118140960795 + 6746954 * 2 ^ 59
def prefixEnd_6746954 : Nat := 4983230072969 + 3 ^ 40 * 6746954 * 2
def baseEnd_6746954 : Nat := 3464430355775100745146329

theorem tailTrace_6746954 : CollatzResearch.WordTrace tailWord_6746954 prefixEnd_6746954 3464430355775100745146329 := by
  unfold tailWord_6746954
  simp only [CollatzResearch.WordTrace]
  refine ⟨61520407199736355212493979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164054419199296947233317277 61520407199736355212493979)
  ·
    refine ⟨92280610799604532818740969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61520407199736355212493979 92280610799604532818740969)
    ·
      refine ⟨69210458099703399614055727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92280610799604532818740969 69210458099703399614055727)
      ·
        refine ⟨103815687149555099421083591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69210458099703399614055727 103815687149555099421083591)
        ·
          refine ⟨155723530724332649131625387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103815687149555099421083591 155723530724332649131625387)
          ·
            refine ⟨233585296086498973697438081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155723530724332649131625387 233585296086498973697438081)
            ·
              refine ⟨175188972064874230273078561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 233585296086498973697438081 175188972064874230273078561)
              ·
                refine ⟨131391729048655672704808921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 175188972064874230273078561 131391729048655672704808921)
                ·
                  refine ⟨98543796786491754528606691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 131391729048655672704808921 98543796786491754528606691)
                  ·
                    refine ⟨147815695179737631792910037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 98543796786491754528606691 147815695179737631792910037)
                    ·
                      refine ⟨3464430355775100745146329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 147815695179737631792910037 3464430355775100745146329)
                      ·
                        rfl

theorem cell23_6746954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 2, 1, 7].length) (baseStart_6746954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6746954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6746954 prefixEnd_6746954 := by exact prefixLift 6746954
  have htrace : WordTrace (prefixWord ++ tailWord_6746954) baseStart_6746954 baseEnd_6746954 := by
    simpa [prefixWord, tailWord_6746954, baseEnd_6746954] using wordTrace_append hprefix tailTrace_6746954
  have hstable : (prefixWord ++ tailWord_6746954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6746954).length < 2 ^ (prefixWord ++ tailWord_6746954).sum := by decide
  have hdescent : baseEnd_6746954 < baseStart_6746954 := by decide
  rcases family_descends (prefixWord ++ tailWord_6746954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6746981 : List Nat := [1, 3, 1, 3, 1, 1, 2, 3, 3, 1, 4]
def baseStart_6746981 : Nat := 118140960795 + 6746981 * 2 ^ 59
def prefixEnd_6746981 : Nat := 4983230072969 + 3 ^ 40 * 6746981 * 2
def baseEnd_6746981 : Nat := 3464444219752772139508705

theorem tailTrace_6746981 : CollatzResearch.WordTrace tailWord_6746981 prefixEnd_6746981 3464444219752772139508705 := by
  unfold tailWord_6746981
  simp only [CollatzResearch.WordTrace]
  refine ⟨246082613569847604461208797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164055075713231736307472531 246082613569847604461208797)
  ·
    refine ⟨92280980088692851672953299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 246082613569847604461208797 92280980088692851672953299)
    ·
      refine ⟨138421470133039277509429949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92280980088692851672953299 138421470133039277509429949)
      ·
        refine ⟨51908051299889729066036231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138421470133039277509429949 51908051299889729066036231)
        ·
          refine ⟨77862076949834593599054347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51908051299889729066036231 77862076949834593599054347)
          ·
            refine ⟨116793115424751890398581521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77862076949834593599054347 116793115424751890398581521)
            ·
              refine ⟨87594836568563917798936141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116793115424751890398581521 87594836568563917798936141)
              ·
                refine ⟨32848063713211469174601053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87594836568563917798936141 32848063713211469174601053)
                ·
                  refine ⟨12318023892454300940475395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32848063713211469174601053 12318023892454300940475395)
                  ·
                    refine ⟨18477035838681451410713093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12318023892454300940475395 18477035838681451410713093)
                    ·
                      refine ⟨3464444219752772139508705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18477035838681451410713093 3464444219752772139508705)
                      ·
                        rfl

theorem cell23_6746981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 3, 3, 1, 4].length) (baseStart_6746981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6746981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6746981 prefixEnd_6746981 := by exact prefixLift 6746981
  have htrace : WordTrace (prefixWord ++ tailWord_6746981) baseStart_6746981 baseEnd_6746981 := by
    simpa [prefixWord, tailWord_6746981, baseEnd_6746981] using wordTrace_append hprefix tailTrace_6746981
  have hstable : (prefixWord ++ tailWord_6746981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6746981).length < 2 ^ (prefixWord ++ tailWord_6746981).sum := by decide
  have hdescent : baseEnd_6746981 < baseStart_6746981 := by decide
  rcases family_descends (prefixWord ++ tailWord_6746981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6747001 : List Nat := [1, 2, 1, 3, 2, 3, 1, 3, 1, 1, 5]
def baseStart_6747001 : Nat := 118140960795 + 6747001 * 2 ^ 59
def prefixEnd_6747001 : Nat := 4983230072969 + 3 ^ 40 * 6747001 * 2
def baseEnd_6747001 : Nat := 3464454489365862061258613

theorem tailTrace_6747001 : CollatzResearch.WordTrace tailWord_6747001 prefixEnd_6747001 3464454489365862061258613 := by
  unfold tailWord_6747001
  simp only [CollatzResearch.WordTrace]
  refine ⟨246083343029775147876936857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164055562019850098584624571 246083343029775147876936857)
  ·
    refine ⟨184562507272331360907702643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246083343029775147876936857 184562507272331360907702643)
    ·
      refine ⟨276843760908497041361553965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184562507272331360907702643 276843760908497041361553965)
      ·
        refine ⟨103816410340686390510582737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 276843760908497041361553965 103816410340686390510582737)
        ·
          refine ⟨77862307755514792882937053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103816410340686390510582737 77862307755514792882937053)
          ·
            refine ⟨29198365408318047331101395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77862307755514792882937053 29198365408318047331101395)
            ·
              refine ⟨43797548112477070996652093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29198365408318047331101395 43797548112477070996652093)
              ·
                refine ⟨16424080542178901623744535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43797548112477070996652093 16424080542178901623744535)
                ·
                  refine ⟨24636120813268352435616803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16424080542178901623744535 24636120813268352435616803)
                  ·
                    refine ⟨36954181219902528653425205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24636120813268352435616803 36954181219902528653425205)
                    ·
                      refine ⟨3464454489365862061258613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36954181219902528653425205 3464454489365862061258613)
                      ·
                        rfl

theorem cell23_6747001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 3, 1, 1, 5].length) (baseStart_6747001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6747001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6747001 prefixEnd_6747001 := by exact prefixLift 6747001
  have htrace : WordTrace (prefixWord ++ tailWord_6747001) baseStart_6747001 baseEnd_6747001 := by
    simpa [prefixWord, tailWord_6747001, baseEnd_6747001] using wordTrace_append hprefix tailTrace_6747001
  have hstable : (prefixWord ++ tailWord_6747001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6747001).length < 2 ^ (prefixWord ++ tailWord_6747001).sum := by decide
  have hdescent : baseEnd_6747001 < baseStart_6747001 := by decide
  rcases family_descends (prefixWord ++ tailWord_6747001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6747018 : List Nat := [3, 1, 2, 4, 1, 1, 2, 2, 1, 1, 5]
def baseStart_6747018 : Nat := 118140960795 + 6747018 * 2 ^ 59
def prefixEnd_6747018 : Nat := 4983230072969 + 3 ^ 40 * 6747018 * 2
def baseEnd_6747018 : Nat := 3464463218536988494746035

theorem tailTrace_6747018 : CollatzResearch.WordTrace tailWord_6747018 prefixEnd_6747018 3464463218536988494746035 := by
  unfold tailWord_6747018
  simp only [CollatzResearch.WordTrace]
  refine ⟨61520990767678389945076427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164055975380475706520203805 61520990767678389945076427)
  ·
    refine ⟨92281486151517584917614641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61520990767678389945076427 92281486151517584917614641)
    ·
      refine ⟨69211114613638188688210981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92281486151517584917614641 69211114613638188688210981)
      ·
        refine ⟨12977083990057160379039559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69211114613638188688210981 12977083990057160379039559)
        ·
          refine ⟨19465625985085740568559339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12977083990057160379039559 19465625985085740568559339)
          ·
            refine ⟨29198438977628610852839009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19465625985085740568559339 29198438977628610852839009)
            ·
              refine ⟨21898829233221458139629257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29198438977628610852839009 21898829233221458139629257)
              ·
                refine ⟨16424121924916093604721943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21898829233221458139629257 16424121924916093604721943)
                ·
                  refine ⟨24636182887374140407082915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16424121924916093604721943 24636182887374140407082915)
                  ·
                    refine ⟨36954274331061210610624373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24636182887374140407082915 36954274331061210610624373)
                    ·
                      refine ⟨3464463218536988494746035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36954274331061210610624373 3464463218536988494746035)
                      ·
                        rfl

theorem cell23_6747018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_6747018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6747018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6747018 prefixEnd_6747018 := by exact prefixLift 6747018
  have htrace : WordTrace (prefixWord ++ tailWord_6747018) baseStart_6747018 baseEnd_6747018 := by
    simpa [prefixWord, tailWord_6747018, baseEnd_6747018] using wordTrace_append hprefix tailTrace_6747018
  have hstable : (prefixWord ++ tailWord_6747018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6747018).length < 2 ^ (prefixWord ++ tailWord_6747018).sum := by decide
  have hdescent : baseEnd_6747018 < baseStart_6747018 := by decide
  rcases family_descends (prefixWord ++ tailWord_6747018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6747028 : List Nat := [2, 4, 2, 1, 1, 1, 2, 3, 1, 2, 4]
def baseStart_6747028 : Nat := 118140960795 + 6747028 * 2 ^ 59
def prefixEnd_6747028 : Nat := 4983230072969 + 3 ^ 40 * 6747028 * 2
def baseEnd_6747028 : Nat := 3464468353343533455620989

theorem tailTrace_6747028 : CollatzResearch.WordTrace tailWord_6747028 prefixEnd_6747028 3464468353343533455620989 := by
  unfold tailWord_6747028
  simp only [CollatzResearch.WordTrace]
  refine ⟨123042163900338665744084869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164056218533784887658779825 123042163900338665744084869)
  ·
    refine ⟨23070405731313499827015913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123042163900338665744084869 23070405731313499827015913)
    ·
      refine ⟨17302804298485124870261935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23070405731313499827015913 17302804298485124870261935)
      ·
        refine ⟨25954206447727687305392903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17302804298485124870261935 25954206447727687305392903)
        ·
          refine ⟨38931309671591530958089355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25954206447727687305392903 38931309671591530958089355)
          ·
            refine ⟨58396964507387296437134033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38931309671591530958089355 58396964507387296437134033)
            ·
              refine ⟨43797723380540472327850525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58396964507387296437134033 43797723380540472327850525)
              ·
                refine ⟨16424146267702677122943947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43797723380540472327850525 16424146267702677122943947)
                ·
                  refine ⟨24636219401554015684415921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16424146267702677122943947 24636219401554015684415921)
                  ·
                    refine ⟨18477164551165511763311941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24636219401554015684415921 18477164551165511763311941)
                    ·
                      refine ⟨3464468353343533455620989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18477164551165511763311941 3464468353343533455620989)
                      ·
                        rfl

theorem cell23_6747028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_6747028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6747028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6747028 prefixEnd_6747028 := by exact prefixLift 6747028
  have htrace : WordTrace (prefixWord ++ tailWord_6747028) baseStart_6747028 baseEnd_6747028 := by
    simpa [prefixWord, tailWord_6747028, baseEnd_6747028] using wordTrace_append hprefix tailTrace_6747028
  have hstable : (prefixWord ++ tailWord_6747028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6747028).length < 2 ^ (prefixWord ++ tailWord_6747028).sum := by decide
  have hdescent : baseEnd_6747028 < baseStart_6747028 := by decide
  rcases family_descends (prefixWord ++ tailWord_6747028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6747065 : List Nat := [1, 2, 1, 4, 2, 2, 1, 4, 2, 1, 3]
def baseStart_6747065 : Nat := 118140960795 + 6747065 * 2 ^ 59
def prefixEnd_6747065 : Nat := 4983230072969 + 3 ^ 40 * 6747065 * 2
def baseEnd_6747065 : Nat := 3464487352127749810858319

theorem tailTrace_6747065 : CollatzResearch.WordTrace tailWord_6747065 prefixEnd_6747065 3464487352127749810858319 := by
  unfold tailWord_6747065
  simp only [CollatzResearch.WordTrace]
  refine ⟨246085677301543286807266649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164057118201028857871511099 246085677301543286807266649)
  ·
    refine ⟨184564257976157465105449987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246085677301543286807266649 184564257976157465105449987)
    ·
      refine ⟨276846386964236197658174981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184564257976157465105449987 276846386964236197658174981)
      ·
        refine ⟨51908697555794287060907809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 276846386964236197658174981 51908697555794287060907809)
        ·
          refine ⟨38931523166845715295680857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51908697555794287060907809 38931523166845715295680857)
          ·
            refine ⟨29198642375134286471760643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38931523166845715295680857 29198642375134286471760643)
            ·
              refine ⟨43797963562701429707640965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29198642375134286471760643 43797963562701429707640965)
              ·
                refine ⟨8212118168006518070182681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43797963562701429707640965 8212118168006518070182681)
                ·
                  refine ⟨6159088626004888552637011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8212118168006518070182681 6159088626004888552637011)
                  ·
                    refine ⟨9238632939007332828955517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6159088626004888552637011 9238632939007332828955517)
                    ·
                      refine ⟨3464487352127749810858319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9238632939007332828955517 3464487352127749810858319)
                      ·
                        rfl

theorem cell23_6747065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 4, 2, 1, 3].length) (baseStart_6747065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6747065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6747065 prefixEnd_6747065 := by exact prefixLift 6747065
  have htrace : WordTrace (prefixWord ++ tailWord_6747065) baseStart_6747065 baseEnd_6747065 := by
    simpa [prefixWord, tailWord_6747065, baseEnd_6747065] using wordTrace_append hprefix tailTrace_6747065
  have hstable : (prefixWord ++ tailWord_6747065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6747065).length < 2 ^ (prefixWord ++ tailWord_6747065).sum := by decide
  have hdescent : baseEnd_6747065 < baseStart_6747065 := by decide
  rcases family_descends (prefixWord ++ tailWord_6747065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6747105 : List Nat := [1, 2, 3, 1, 2, 1, 1, 4, 4, 2, 2]
def baseStart_6747105 : Nat := 118140960795 + 6747105 * 2 ^ 59
def prefixEnd_6747105 : Nat := 4983230072969 + 3 ^ 40 * 6747105 * 2
def baseEnd_6747105 : Nat := 3464507891353929654358135

theorem tailTrace_6747105 : CollatzResearch.WordTrace tailWord_6747105 prefixEnd_6747105 3464507891353929654358135 := by
  unfold tailWord_6747105
  simp only [CollatzResearch.WordTrace]
  refine ⟨246087136221398373638722769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164058090814265582425815179 246087136221398373638722769)
  ·
    refine ⟨184565352166048780229042077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246087136221398373638722769 184565352166048780229042077)
    ·
      refine ⟨69212007062268292585890779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184565352166048780229042077 69212007062268292585890779)
      ·
        refine ⟨103818010593402438878836169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69212007062268292585890779 103818010593402438878836169)
        ·
          refine ⟨77863507945051829159127127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103818010593402438878836169 77863507945051829159127127)
          ·
            refine ⟨116795261917577743738690691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77863507945051829159127127 116795261917577743738690691)
            ·
              refine ⟨175192892876366615608036037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116795261917577743738690691 175192892876366615608036037)
              ·
                refine ⟨32848667414318740426506757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 175192892876366615608036037 32848667414318740426506757)
                ·
                  refine ⟨6159125140184763829970017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32848667414318740426506757 6159125140184763829970017)
                  ·
                    refine ⟨4619343855138572872477513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6159125140184763829970017 4619343855138572872477513)
                    ·
                      refine ⟨3464507891353929654358135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4619343855138572872477513 3464507891353929654358135)
                      ·
                        rfl

theorem cell23_6747105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 4, 4, 2, 2].length) (baseStart_6747105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6747105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6747105 prefixEnd_6747105 := by exact prefixLift 6747105
  have htrace : WordTrace (prefixWord ++ tailWord_6747105) baseStart_6747105 baseEnd_6747105 := by
    simpa [prefixWord, tailWord_6747105, baseEnd_6747105] using wordTrace_append hprefix tailTrace_6747105
  have hstable : (prefixWord ++ tailWord_6747105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6747105).length < 2 ^ (prefixWord ++ tailWord_6747105).sum := by decide
  have hdescent : baseEnd_6747105 < baseStart_6747105 := by decide
  rcases family_descends (prefixWord ++ tailWord_6747105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6747109 : List Nat := [1, 3, 1, 6, 1, 1, 1, 3, 1, 3, 2]
def baseStart_6747109 : Nat := 118140960795 + 6747109 * 2 ^ 59
def prefixEnd_6747109 : Nat := 4983230072969 + 3 ^ 40 * 6747109 * 2
def baseEnd_6747109 : Nat := 3464509945276547638708117

theorem tailTrace_6747109 : CollatzResearch.WordTrace tailWord_6747109 prefixEnd_6747109 3464509945276547638708117 := by
  unfold tailWord_6747109
  simp only [CollatzResearch.WordTrace]
  refine ⟨246087282113383882321868381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164058188075589254881245587 246087282113383882321868381)
  ·
    refine ⟨92282730792518955870700643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 246087282113383882321868381 92282730792518955870700643)
    ·
      refine ⟨138424096188778433806050965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92282730792518955870700643 138424096188778433806050965)
      ·
        refine ⟨6488629508848989084658639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 138424096188778433806050965 6488629508848989084658639)
        ·
          refine ⟨9732944263273483626987959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6488629508848989084658639 9732944263273483626987959)
          ·
            refine ⟨14599416394910225440481939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9732944263273483626987959 14599416394910225440481939)
            ·
              refine ⟨21899124592365338160722909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14599416394910225440481939 21899124592365338160722909)
              ·
                refine ⟨8212171722137001810271091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21899124592365338160722909 8212171722137001810271091)
                ·
                  refine ⟨12318257583205502715406637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8212171722137001810271091 12318257583205502715406637)
                  ·
                    refine ⟨4619346593702063518277489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12318257583205502715406637 4619346593702063518277489)
                    ·
                      refine ⟨3464509945276547638708117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4619346593702063518277489 3464509945276547638708117)
                      ·
                        rfl

theorem cell23_6747109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_6747109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6747109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6747109 prefixEnd_6747109 := by exact prefixLift 6747109
  have htrace : WordTrace (prefixWord ++ tailWord_6747109) baseStart_6747109 baseEnd_6747109 := by
    simpa [prefixWord, tailWord_6747109, baseEnd_6747109] using wordTrace_append hprefix tailTrace_6747109
  have hstable : (prefixWord ++ tailWord_6747109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6747109).length < 2 ^ (prefixWord ++ tailWord_6747109).sum := by decide
  have hdescent : baseEnd_6747109 < baseStart_6747109 := by decide
  rcases family_descends (prefixWord ++ tailWord_6747109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6747141 : List Nat := [1, 3, 1, 1, 2, 3, 1, 1, 3, 7]
def baseStart_6747141 : Nat := 118140960795 + 6747141 * 2 ^ 59
def prefixEnd_6747141 : Nat := 4983230072969 + 3 ^ 40 * 6747141 * 2
def baseEnd_6747141 : Nat := 1154842125552497171169323

theorem tailTrace_6747141 : CollatzResearch.WordTrace tailWord_6747141 prefixEnd_6747141 1154842125552497171169323 := by
  unfold tailWord_6747141
  simp only [CollatzResearch.WordTrace]
  refine ⟨246088449249267951787033277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164058966166178634524688851 246088449249267951787033277)
  ·
    refine ⟨92283168468475481920137479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 246088449249267951787033277 92283168468475481920137479)
    ·
      refine ⟨138424752702713222880206219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92283168468475481920137479 138424752702713222880206219)
      ·
        refine ⟨207637129054069834320309329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138424752702713222880206219 207637129054069834320309329)
        ·
          refine ⟨155727846790552375740231997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207637129054069834320309329 155727846790552375740231997)
          ·
            refine ⟨58397942546457140902586999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 155727846790552375740231997 58397942546457140902586999)
            ·
              refine ⟨87596913819685711353880499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58397942546457140902586999 87596913819685711353880499)
              ·
                refine ⟨131395370729528567030820749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87596913819685711353880499 131395370729528567030820749)
                ·
                  refine ⟨49273264023573212636557781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 131395370729528567030820749 49273264023573212636557781)
                  ·
                    refine ⟨1154842125552497171169323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49273264023573212636557781 1154842125552497171169323)
                    ·
                      rfl

theorem cell23_6747141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 3, 7].length) (baseStart_6747141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6747141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6747141 prefixEnd_6747141 := by exact prefixLift 6747141
  have htrace : WordTrace (prefixWord ++ tailWord_6747141) baseStart_6747141 baseEnd_6747141 := by
    simpa [prefixWord, tailWord_6747141, baseEnd_6747141] using wordTrace_append hprefix tailTrace_6747141
  have hstable : (prefixWord ++ tailWord_6747141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6747141).length < 2 ^ (prefixWord ++ tailWord_6747141).sum := by decide
  have hdescent : baseEnd_6747141 < baseStart_6747141 := by decide
  rcases family_descends (prefixWord ++ tailWord_6747141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6747175 : List Nat := [1, 1, 7, 1, 1, 1, 1, 1, 4, 5]
def baseStart_6747175 : Nat := 118140960795 + 6747175 * 2 ^ 59
def prefixEnd_6747175 : Nat := 4983230072969 + 3 ^ 40 * 6747175 * 2
def baseEnd_6747175 : Nat := 1154847944999914793494271

theorem tailTrace_6747175 : CollatzResearch.WordTrace tailWord_6747175 prefixEnd_6747175 1154847944999914793494271 := by
  unfold tailWord_6747175
  simp only [CollatzResearch.WordTrace]
  refine ⟨246089689331144775593770979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164059792887429850395847319 246089689331144775593770979)
  ·
    refine ⟨369134533996717163390656469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246089689331144775593770979 369134533996717163390656469)
    ·
      refine ⟨8651590640548058516968511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 369134533996717163390656469 8651590640548058516968511)
      ·
        refine ⟨12977385960822087775452767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8651590640548058516968511 12977385960822087775452767)
        ·
          refine ⟨19466078941233131663179151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12977385960822087775452767 19466078941233131663179151)
          ·
            refine ⟨29199118411849697494768727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19466078941233131663179151 29199118411849697494768727)
            ·
              refine ⟨43798677617774546242153091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29199118411849697494768727 43798677617774546242153091)
              ·
                refine ⟨65698016426661819363229637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43798677617774546242153091 65698016426661819363229637)
                ·
                  refine ⟨12318378079999091130605557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65698016426661819363229637 12318378079999091130605557)
                  ·
                    refine ⟨1154847944999914793494271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12318378079999091130605557 1154847944999914793494271)
                    ·
                      rfl

theorem cell23_6747175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_6747175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6747175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6747175 prefixEnd_6747175 := by exact prefixLift 6747175
  have htrace : WordTrace (prefixWord ++ tailWord_6747175) baseStart_6747175 baseEnd_6747175 := by
    simpa [prefixWord, tailWord_6747175, baseEnd_6747175] using wordTrace_append hprefix tailTrace_6747175
  have hstable : (prefixWord ++ tailWord_6747175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6747175).length < 2 ^ (prefixWord ++ tailWord_6747175).sum := by decide
  have hdescent : baseEnd_6747175 < baseStart_6747175 := by decide
  rcases family_descends (prefixWord ++ tailWord_6747175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6747211 : List Nat := [1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 9]
def baseStart_6747211 : Nat := 118140960795 + 6747211 * 2 ^ 59
def prefixEnd_6747211 : Nat := 4983230072969 + 3 ^ 40 * 6747211 * 2
def baseEnd_6747211 : Nat := 3464562320303306239632647

theorem tailTrace_6747211 : CollatzResearch.WordTrace tailWord_6747211 prefixEnd_6747211 3464562320303306239632647 := by
  unfold tailWord_6747211
  simp only [CollatzResearch.WordTrace]
  refine ⟨246091002359014353742081487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164060668239342902494720991 246091002359014353742081487)
  ·
    refine ⟨369136503538521530613122231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246091002359014353742081487 369136503538521530613122231)
    ·
      refine ⟨553704755307782295919683347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369136503538521530613122231 553704755307782295919683347)
      ·
        refine ⟨830557132961673443879525021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 553704755307782295919683347 830557132961673443879525021)
        ·
          refine ⟨311458924860627541454821883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 830557132961673443879525021 311458924860627541454821883)
          ·
            refine ⟨467188387290941312182232825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 311458924860627541454821883 467188387290941312182232825)
            ·
              refine ⟨350391290468205984136674619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 467188387290941312182232825 350391290468205984136674619)
              ·
                refine ⟨525586935702308976205011929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 350391290468205984136674619 525586935702308976205011929)
                ·
                  refine ⟨394190201776731732153758947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 525586935702308976205011929 394190201776731732153758947)
                  ·
                    refine ⟨591285302665097598230638421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 394190201776731732153758947 591285302665097598230638421)
                    ·
                      refine ⟨3464562320303306239632647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 591285302665097598230638421 3464562320303306239632647)
                      ·
                        rfl

theorem cell23_6747211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 9].length) (baseStart_6747211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6747211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6747211 prefixEnd_6747211 := by exact prefixLift 6747211
  have htrace : WordTrace (prefixWord ++ tailWord_6747211) baseStart_6747211 baseEnd_6747211 := by
    simpa [prefixWord, tailWord_6747211, baseEnd_6747211] using wordTrace_append hprefix tailTrace_6747211
  have hstable : (prefixWord ++ tailWord_6747211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6747211).length < 2 ^ (prefixWord ++ tailWord_6747211).sum := by decide
  have hdescent : baseEnd_6747211 < baseStart_6747211 := by decide
  rcases family_descends (prefixWord ++ tailWord_6747211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6747239 : List Nat := [1, 1, 5, 1, 1, 3, 4, 2, 1, 4]
def baseStart_6747239 : Nat := 118140960795 + 6747239 * 2 ^ 59
def prefixEnd_6747239 : Nat := 4983230072969 + 3 ^ 40 * 6747239 * 2
def baseEnd_6747239 : Nat := 1154858899253877376694173

theorem tailTrace_6747239 : CollatzResearch.WordTrace tailWord_6747239 prefixEnd_6747239 1154858899253877376694173 := by
  unfold tailWord_6747239
  simp only [CollatzResearch.WordTrace]
  refine ⟨246092023602912914524100771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164061349068608609682733847 246092023602912914524100771)
  ·
    refine ⟨369138035404369371786151157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246092023602912914524100771 369138035404369371786151157)
    ·
      refine ⟨34606690819159628604951671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 369138035404369371786151157 34606690819159628604951671)
      ·
        refine ⟨51910036228739442907427507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34606690819159628604951671 51910036228739442907427507)
        ·
          refine ⟨77865054343109164361141261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51910036228739442907427507 77865054343109164361141261)
          ·
            refine ⟨29199395378665936635427973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77865054343109164361141261 29199395378665936635427973)
            ·
              refine ⟨5474886633499863119142745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29199395378665936635427973 5474886633499863119142745)
              ·
                refine ⟨4106164975124897339357059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5474886633499863119142745 4106164975124897339357059)
                ·
                  refine ⟨6159247462687346009035589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4106164975124897339357059 6159247462687346009035589)
                  ·
                    refine ⟨1154858899253877376694173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6159247462687346009035589 1154858899253877376694173)
                    ·
                      rfl

theorem cell23_6747239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 4, 2, 1, 4].length) (baseStart_6747239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6747239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6747239 prefixEnd_6747239 := by exact prefixLift 6747239
  have htrace : WordTrace (prefixWord ++ tailWord_6747239) baseStart_6747239 baseEnd_6747239 := by
    simpa [prefixWord, tailWord_6747239, baseEnd_6747239] using wordTrace_append hprefix tailTrace_6747239
  have hstable : (prefixWord ++ tailWord_6747239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6747239).length < 2 ^ (prefixWord ++ tailWord_6747239).sum := by decide
  have hdescent : baseEnd_6747239 < baseStart_6747239 := by decide
  rcases family_descends (prefixWord ++ tailWord_6747239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6747248 : List Nat := [2, 1, 1, 1, 5, 1, 1, 1, 5, 5]
def baseStart_6747248 : Nat := 118140960795 + 6747248 * 2 ^ 59
def prefixEnd_6747248 : Nat := 4983230072969 + 3 ^ 40 * 6747248 * 2
def baseEnd_6747248 : Nat := 1154860439695840864956659

theorem tailTrace_6747248 : CollatzResearch.WordTrace tailWord_6747248 prefixEnd_6747248 1154860439695840864956659 := by
  unfold tailWord_6747248
  simp only [CollatzResearch.WordTrace]
  refine ⟨123046175929940154530589199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164061567906586872707452265 123046175929940154530589199)
  ·
    refine ⟨184569263894910231795883799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123046175929940154530589199 184569263894910231795883799)
    ·
      refine ⟨276853895842365347693825699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184569263894910231795883799 276853895842365347693825699)
      ·
        refine ⟨415280843763548021540738549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276853895842365347693825699 415280843763548021540738549)
        ·
          refine ⟨38932579102832627019444239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 415280843763548021540738549 38932579102832627019444239)
          ·
            refine ⟨58398868654248940529166359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38932579102832627019444239 58398868654248940529166359)
            ·
              refine ⟨87598302981373410793749539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58398868654248940529166359 87598302981373410793749539)
              ·
                refine ⟨131397454472060116190624309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87598302981373410793749539 131397454472060116190624309)
                ·
                  refine ⟨12318511356755635892871029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 131397454472060116190624309 12318511356755635892871029)
                  ·
                    refine ⟨1154860439695840864956659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12318511356755635892871029 1154860439695840864956659)
                    ·
                      rfl

theorem cell23_6747248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 5, 5].length) (baseStart_6747248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6747248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6747248 prefixEnd_6747248 := by exact prefixLift 6747248
  have htrace : WordTrace (prefixWord ++ tailWord_6747248) baseStart_6747248 baseEnd_6747248 := by
    simpa [prefixWord, tailWord_6747248, baseEnd_6747248] using wordTrace_append hprefix tailTrace_6747248
  have hstable : (prefixWord ++ tailWord_6747248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6747248).length < 2 ^ (prefixWord ++ tailWord_6747248).sum := by decide
  have hdescent : baseEnd_6747248 < baseStart_6747248 := by decide
  rcases family_descends (prefixWord ++ tailWord_6747248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6747255 : List Nat := [1, 1, 3, 1, 1, 4, 2, 2, 1, 5, 2]
def baseStart_6747255 : Nat := 118140960795 + 6747255 * 2 ^ 59
def prefixEnd_6747255 : Nat := 4983230072969 + 3 ^ 40 * 6747255 * 2
def baseEnd_6747255 : Nat := 3464584913452104067482445

theorem tailTrace_6747255 : CollatzResearch.WordTrace tailWord_6747255 prefixEnd_6747255 3464584913452104067482445 := by
  unfold tailWord_6747255
  simp only [CollatzResearch.WordTrace]
  refine ⟨246092607170854949256683219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164061738113903299504455479 246092607170854949256683219)
  ·
    refine ⟨369138910756282423885024829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246092607170854949256683219 369138910756282423885024829)
    ·
      refine ⟨138427091533605908956884311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 369138910756282423885024829 138427091533605908956884311)
      ·
        refine ⟨207640637300408863435326467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138427091533605908956884311 207640637300408863435326467)
        ·
          refine ⟨311460955950613295152989701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207640637300408863435326467 311460955950613295152989701)
          ·
            refine ⟨58398929240739992841185569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 311460955950613295152989701 58398929240739992841185569)
            ·
              refine ⟨43799196930554994630889177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58398929240739992841185569 43799196930554994630889177)
              ·
                refine ⟨32849397697916245973166883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43799196930554994630889177 32849397697916245973166883)
                ·
                  refine ⟨49274096546874368959750325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32849397697916245973166883 49274096546874368959750325)
                  ·
                    refine ⟨4619446551269472089976593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49274096546874368959750325 4619446551269472089976593)
                    ·
                      refine ⟨3464584913452104067482445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4619446551269472089976593 3464584913452104067482445)
                      ·
                        rfl

theorem cell23_6747255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 2, 1, 5, 2].length) (baseStart_6747255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6747255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6747255 prefixEnd_6747255 := by exact prefixLift 6747255
  have htrace : WordTrace (prefixWord ++ tailWord_6747255) baseStart_6747255 baseEnd_6747255 := by
    simpa [prefixWord, tailWord_6747255, baseEnd_6747255] using wordTrace_append hprefix tailTrace_6747255
  have hstable : (prefixWord ++ tailWord_6747255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6747255).length < 2 ^ (prefixWord ++ tailWord_6747255).sum := by decide
  have hdescent : baseEnd_6747255 < baseStart_6747255 := by decide
  rcases family_descends (prefixWord ++ tailWord_6747255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6747265 : List Nat := [1, 2, 4, 2, 2, 1, 2, 1, 3, 5]
def baseStart_6747265 : Nat := 118140960795 + 6747265 * 2 ^ 59
def prefixEnd_6747265 : Nat := 4983230072969 + 3 ^ 40 * 6747265 * 2
def baseEnd_6747265 : Nat := 1154863349419549676119133

theorem tailTrace_6747265 : CollatzResearch.WordTrace tailWord_6747265 prefixEnd_6747265 1154863349419549676119133 := by
  unfold tailWord_6747265
  simp only [CollatzResearch.WordTrace]
  refine ⟨246092971900818720964547249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164061981267212480643031499 246092971900818720964547249)
  ·
    refine ⟨184569728925614040723410437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246092971900818720964547249 184569728925614040723410437)
    ·
      refine ⟨34606824173552632635639457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 184569728925614040723410437 34606824173552632635639457)
      ·
        refine ⟨25955118130164474476729593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34606824173552632635639457 25955118130164474476729593)
        ·
          refine ⟨19466338597623355857547195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25955118130164474476729593 19466338597623355857547195)
          ·
            refine ⟨29199507896435033786320793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19466338597623355857547195 29199507896435033786320793)
            ·
              refine ⟨21899630922326275339740595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29199507896435033786320793 21899630922326275339740595)
              ·
                refine ⟨32849446383489413009610893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21899630922326275339740595 32849446383489413009610893)
                ·
                  refine ⟨12318542393808529878604085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32849446383489413009610893 12318542393808529878604085)
                  ·
                    refine ⟨1154863349419549676119133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12318542393808529878604085 1154863349419549676119133)
                    ·
                      rfl

theorem cell23_6747265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 1, 3, 5].length) (baseStart_6747265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6747265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6747265 prefixEnd_6747265 := by exact prefixLift 6747265
  have htrace : WordTrace (prefixWord ++ tailWord_6747265) baseStart_6747265 baseEnd_6747265 := by
    simpa [prefixWord, tailWord_6747265, baseEnd_6747265] using wordTrace_append hprefix tailTrace_6747265
  have hstable : (prefixWord ++ tailWord_6747265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6747265).length < 2 ^ (prefixWord ++ tailWord_6747265).sum := by decide
  have hdescent : baseEnd_6747265 < baseStart_6747265 := by decide
  rcases family_descends (prefixWord ++ tailWord_6747265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6747282 : List Nat := [3, 2, 3, 1, 1, 3, 1, 3, 1, 5]
def baseStart_6747282 : Nat := 118140960795 + 6747282 * 2 ^ 59
def prefixEnd_6747282 : Nat := 4983230072969 + 3 ^ 40 * 6747282 * 2
def baseEnd_6747282 : Nat := 1154866259143258487281607

theorem tailTrace_6747282 : CollatzResearch.WordTrace tailWord_6747282 prefixEnd_6747282 1154866259143258487281607 := by
  unfold tailWord_6747282
  simp only [CollatzResearch.WordTrace]
  refine ⟨61523397985439283216979025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164062394627838088578610733 61523397985439283216979025)
  ·
    refine ⟨46142548489079462412734269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61523397985439283216979025 46142548489079462412734269)
    ·
      refine ⟨17303455683404798404775351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46142548489079462412734269 17303455683404798404775351)
      ·
        refine ⟨25955183525107197607163027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17303455683404798404775351 25955183525107197607163027)
        ·
          refine ⟨38932775287660796410744541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25955183525107197607163027 38932775287660796410744541)
          ·
            refine ⟨14599790732872798654029203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38932775287660796410744541 14599790732872798654029203)
            ·
              refine ⟨21899686099309197981043805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14599790732872798654029203 21899686099309197981043805)
              ·
                refine ⟨8212382287240949242891427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21899686099309197981043805 8212382287240949242891427)
                ·
                  refine ⟨12318573430861423864337141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8212382287240949242891427 12318573430861423864337141)
                  ·
                    refine ⟨1154866259143258487281607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12318573430861423864337141 1154866259143258487281607)
                    ·
                      rfl

theorem cell23_6747282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 3, 1, 5].length) (baseStart_6747282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6747282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6747282 prefixEnd_6747282 := by exact prefixLift 6747282
  have htrace : WordTrace (prefixWord ++ tailWord_6747282) baseStart_6747282 baseEnd_6747282 := by
    simpa [prefixWord, tailWord_6747282, baseEnd_6747282] using wordTrace_append hprefix tailTrace_6747282
  have hstable : (prefixWord ++ tailWord_6747282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6747282).length < 2 ^ (prefixWord ++ tailWord_6747282).sum := by decide
  have hdescent : baseEnd_6747282 < baseStart_6747282 := by decide
  rcases family_descends (prefixWord ++ tailWord_6747282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6747315 : List Nat := [1, 1, 1, 2, 3, 2, 5, 1, 1, 2, 4]
def baseStart_6747315 : Nat := 118140960795 + 6747315 * 2 ^ 59
def prefixEnd_6747315 : Nat := 4983230072969 + 3 ^ 40 * 6747315 * 2
def baseEnd_6747315 : Nat := 3464615722291373832732169

theorem tailTrace_6747315 : CollatzResearch.WordTrace tailWord_6747315 prefixEnd_6747315 3464615722291373832732169 := by
  unfold tailWord_6747315
  simp only [CollatzResearch.WordTrace]
  refine ⟨246094795550637579503867399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164063197033758386335911599 246094795550637579503867399)
  ·
    refine ⟨369142193325956369255801099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246094795550637579503867399 369142193325956369255801099)
    ·
      refine ⟨553713289988934553883701649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369142193325956369255801099 553713289988934553883701649)
      ·
        refine ⟨415284967491700915412776237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 553713289988934553883701649 415284967491700915412776237)
        ·
          refine ⟨155731862809387843279791089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 415284967491700915412776237 155731862809387843279791089)
          ·
            refine ⟨116798897107040882459843317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155731862809387843279791089 116798897107040882459843317)
            ·
              refine ⟨10949896603785082730610311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 116798897107040882459843317 10949896603785082730610311)
              ·
                refine ⟨16424844905677624095915467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10949896603785082730610311 16424844905677624095915467)
                ·
                  refine ⟨24637267358516436143873201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16424844905677624095915467 24637267358516436143873201)
                  ·
                    refine ⟨18477950518887327107904901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24637267358516436143873201 18477950518887327107904901)
                    ·
                      refine ⟨3464615722291373832732169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18477950518887327107904901 3464615722291373832732169)
                      ·
                        rfl

theorem cell23_6747315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 1, 1, 2, 4].length) (baseStart_6747315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6747315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6747315 prefixEnd_6747315 := by exact prefixLift 6747315
  have htrace : WordTrace (prefixWord ++ tailWord_6747315) baseStart_6747315 baseEnd_6747315 := by
    simpa [prefixWord, tailWord_6747315, baseEnd_6747315] using wordTrace_append hprefix tailTrace_6747315
  have hstable : (prefixWord ++ tailWord_6747315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6747315).length < 2 ^ (prefixWord ++ tailWord_6747315).sum := by decide
  have hdescent : baseEnd_6747315 < baseStart_6747315 := by decide
  rcases family_descends (prefixWord ++ tailWord_6747315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6747325 : List Nat := [1, 4, 1, 2, 1, 1, 6, 7]
def baseStart_6747325 : Nat := 118140960795 + 6747325 * 2 ^ 59
def prefixEnd_6747325 : Nat := 4983230072969 + 3 ^ 40 * 6747325 * 2
def baseEnd_6747325 : Nat := 128319291003626621985449

theorem tailTrace_6747325 : CollatzResearch.WordTrace tailWord_6747325 prefixEnd_6747325 128319291003626621985449 := by
  unfold tailWord_6747325
  simp only [CollatzResearch.WordTrace]
  refine ⟨246095160280601351211731429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164063440187067567474487619 246095160280601351211731429)
  ·
    refine ⟨46142842552612753352199643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 246095160280601351211731429 46142842552612753352199643)
    ·
      refine ⟨69214263828919130028299465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46142842552612753352199643 69214263828919130028299465)
      ·
        refine ⟨51910697871689347521224599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69214263828919130028299465 51910697871689347521224599)
        ·
          refine ⟨77866046807534021281836899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51910697871689347521224599 77866046807534021281836899)
          ·
            refine ⟨116799070211301031922755349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77866046807534021281836899 116799070211301031922755349)
            ·
              refine ⟨5474956416154735871379157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 116799070211301031922755349 5474956416154735871379157)
              ·
                refine ⟨128319291003626621985449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5474956416154735871379157 128319291003626621985449)
                ·
                  rfl

theorem cell23_6747325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 6, 7].length) (baseStart_6747325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6747325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6747325 prefixEnd_6747325 := by exact prefixLift 6747325
  have htrace : WordTrace (prefixWord ++ tailWord_6747325) baseStart_6747325 baseEnd_6747325 := by
    simpa [prefixWord, tailWord_6747325, baseEnd_6747325] using wordTrace_append hprefix tailTrace_6747325
  have hstable : (prefixWord ++ tailWord_6747325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6747325).length < 2 ^ (prefixWord ++ tailWord_6747325).sum := by decide
  have hdescent : baseEnd_6747325 < baseStart_6747325 := by decide
  rcases family_descends (prefixWord ++ tailWord_6747325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6747335 : List Nat := [1, 1, 4, 1, 1, 1, 1, 6, 1, 3, 3]
def baseStart_6747335 : Nat := 118140960795 + 6747335 * 2 ^ 59
def prefixEnd_6747335 : Nat := 4983230072969 + 3 ^ 40 * 6747335 * 2
def baseEnd_6747335 : Nat := 3464625991904463754482077

theorem tailTrace_6747335 : CollatzResearch.WordTrace tailWord_6747335 prefixEnd_6747335 3464625991904463754482077 := by
  unfold tailWord_6747335
  simp only [CollatzResearch.WordTrace]
  refine ⟨246095525010565122919595459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164063683340376748613063639 246095525010565122919595459)
  ·
    refine ⟨369143287515847684379393189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246095525010565122919595459 369143287515847684379393189)
    ·
      refine ⟨69214366409221440821136223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 369143287515847684379393189 69214366409221440821136223)
      ·
        refine ⟨103821549613832161231704335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69214366409221440821136223 103821549613832161231704335)
        ·
          refine ⟨155732324420748241847556503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103821549613832161231704335 155732324420748241847556503)
          ·
            refine ⟨233598486631122362771334755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155732324420748241847556503 233598486631122362771334755)
            ·
              refine ⟨350397729946683544157002133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 233598486631122362771334755 350397729946683544157002133)
              ·
                refine ⟨16424893591250791132359475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 350397729946683544157002133 16424893591250791132359475)
                ·
                  refine ⟨24637340386876186698539213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16424893591250791132359475 24637340386876186698539213)
                  ·
                    refine ⟨9239002645078570011952205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24637340386876186698539213 9239002645078570011952205)
                    ·
                      refine ⟨3464625991904463754482077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9239002645078570011952205 3464625991904463754482077)
                      ·
                        rfl

theorem cell23_6747335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 6, 1, 3, 3].length) (baseStart_6747335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6747335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6747335 prefixEnd_6747335 := by exact prefixLift 6747335
  have htrace : WordTrace (prefixWord ++ tailWord_6747335) baseStart_6747335 baseEnd_6747335 := by
    simpa [prefixWord, tailWord_6747335, baseEnd_6747335] using wordTrace_append hprefix tailTrace_6747335
  have hstable : (prefixWord ++ tailWord_6747335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6747335).length < 2 ^ (prefixWord ++ tailWord_6747335).sum := by decide
  have hdescent : baseEnd_6747335 < baseStart_6747335 := by decide
  rcases family_descends (prefixWord ++ tailWord_6747335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6747336 : List Nat := [2, 1, 3, 1, 2, 1, 5, 3, 1, 2, 2]
def baseStart_6747336 : Nat := 118140960795 + 6747336 * 2 ^ 59
def prefixEnd_6747336 : Nat := 4983230072969 + 3 ^ 40 * 6747336 * 2
def baseEnd_6747336 : Nat := 3464626505385118250569573

theorem tailTrace_6747336 : CollatzResearch.WordTrace tailWord_6747336 prefixEnd_6747336 3464626505385118250569573 := by
  unfold tailWord_6747336
  simp only [CollatzResearch.WordTrace]
  refine ⟨123047780741780750045190931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164063707655707666726921241 123047780741780750045190931)
  ·
    refine ⟨184571671112671125067786397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123047780741780750045190931 184571671112671125067786397)
    ·
      refine ⟨69214376667251671900419899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184571671112671125067786397 69214376667251671900419899)
      ·
        refine ⟨103821565000877507850629849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69214376667251671900419899 103821565000877507850629849)
        ·
          refine ⟨77866173750658130887972387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103821565000877507850629849 77866173750658130887972387)
          ·
            refine ⟨116799260625987196331958581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77866173750658130887972387 116799260625987196331958581)
            ·
              refine ⟨10949930683686299656121117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 116799260625987196331958581 10949930683686299656121117)
              ·
                refine ⟨4106224006382362371045419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10949930683686299656121117 4106224006382362371045419)
                ·
                  refine ⟨6159336009573543556568129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4106224006382362371045419 6159336009573543556568129)
                  ·
                    refine ⟨4619502007180157667426097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6159336009573543556568129 4619502007180157667426097)
                    ·
                      refine ⟨3464626505385118250569573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4619502007180157667426097 3464626505385118250569573)
                      ·
                        rfl

theorem cell23_6747336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 3, 1, 2, 2].length) (baseStart_6747336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6747336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6747336 prefixEnd_6747336 := by exact prefixLift 6747336
  have htrace : WordTrace (prefixWord ++ tailWord_6747336) baseStart_6747336 baseEnd_6747336 := by
    simpa [prefixWord, tailWord_6747336, baseEnd_6747336] using wordTrace_append hprefix tailTrace_6747336
  have hstable : (prefixWord ++ tailWord_6747336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6747336).length < 2 ^ (prefixWord ++ tailWord_6747336).sum := by decide
  have hdescent : baseEnd_6747336 < baseStart_6747336 := by decide
  rcases family_descends (prefixWord ++ tailWord_6747336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6747342 : List Nat := [4, 1, 1, 1, 6, 1, 9]
def baseStart_6747342 : Nat := 118140960795 + 6747342 * 2 ^ 59
def prefixEnd_6747342 : Nat := 4983230072969 + 3 ^ 40 * 6747342 * 2
def baseEnd_6747342 : Nat := 42773204768753644778945

theorem tailTrace_6747342 : CollatzResearch.WordTrace tailWord_6747342 prefixEnd_6747342 42773204768753644778945 := by
  unfold tailWord_6747342
  simp only [CollatzResearch.WordTrace]
  refine ⟨30761972540192470389387535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164063853547693175410066853 30761972540192470389387535)
  ·
    refine ⟨46142958810288705584081303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30761972540192470389387535 46142958810288705584081303)
    ·
      refine ⟨69214438215433058376121955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46142958810288705584081303 69214438215433058376121955)
      ·
        refine ⟨103821657323149587564182933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69214438215433058376121955 103821657323149587564182933)
        ·
          refine ⟨4866640187022636917071075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 103821657323149587564182933 4866640187022636917071075)
          ·
            refine ⟨7299960280533955375606613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4866640187022636917071075 7299960280533955375606613)
            ·
              refine ⟨42773204768753644778945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7299960280533955375606613 42773204768753644778945)
              ·
                rfl

theorem cell23_6747342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 9].length) (baseStart_6747342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6747342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6747342 prefixEnd_6747342 := by exact prefixLift 6747342
  have htrace : WordTrace (prefixWord ++ tailWord_6747342) baseStart_6747342 baseEnd_6747342 := by
    simpa [prefixWord, tailWord_6747342, baseEnd_6747342] using wordTrace_append hprefix tailTrace_6747342
  have hstable : (prefixWord ++ tailWord_6747342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6747342).length < 2 ^ (prefixWord ++ tailWord_6747342).sum := by decide
  have hdescent : baseEnd_6747342 < baseStart_6747342 := by decide
  rcases family_descends (prefixWord ++ tailWord_6747342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6747379 : List Nat := [1, 1, 1, 2, 2, 5, 3, 2, 1, 3, 2]
def baseStart_6747379 : Nat := 118140960795 + 6747379 * 2 ^ 59
def prefixEnd_6747379 : Nat := 4983230072969 + 3 ^ 40 * 6747379 * 2
def baseEnd_6747379 : Nat := 3464648585053261582331875

theorem tailTrace_6747379 : CollatzResearch.WordTrace tailWord_6747379 prefixEnd_6747379 3464648585053261582331875 := by
  unfold tailWord_6747379
  simp only [CollatzResearch.WordTrace]
  refine ⟨246097129822405718434197191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164064753214937145622798127 246097129822405718434197191)
  ·
    refine ⟨369145694733608577651295787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246097129822405718434197191 369145694733608577651295787)
    ·
      refine ⟨553718542100412866476943681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369145694733608577651295787 553718542100412866476943681)
      ·
        refine ⟨415288906575309649857707761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 553718542100412866476943681 415288906575309649857707761)
        ·
          refine ⟨311466679931482237393280821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 415288906575309649857707761 311466679931482237393280821)
          ·
            refine ⟨29200001243576459755620077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 311466679931482237393280821 29200001243576459755620077)
            ·
              refine ⟨10950000466341172408357529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29200001243576459755620077 10950000466341172408357529)
              ·
                refine ⟨8212500349755879306268147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10950000466341172408357529 8212500349755879306268147)
                ·
                  refine ⟨12318750524633818959402221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8212500349755879306268147 12318750524633818959402221)
                  ·
                    refine ⟨4619531446737682109775833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12318750524633818959402221 4619531446737682109775833)
                    ·
                      refine ⟨3464648585053261582331875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4619531446737682109775833 3464648585053261582331875)
                      ·
                        rfl

theorem cell23_6747379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 2, 1, 3, 2].length) (baseStart_6747379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6747379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6747379 prefixEnd_6747379 := by exact prefixLift 6747379
  have htrace : WordTrace (prefixWord ++ tailWord_6747379) baseStart_6747379 baseEnd_6747379 := by
    simpa [prefixWord, tailWord_6747379, baseEnd_6747379] using wordTrace_append hprefix tailTrace_6747379
  have hstable : (prefixWord ++ tailWord_6747379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6747379).length < 2 ^ (prefixWord ++ tailWord_6747379).sum := by decide
  have hdescent : baseEnd_6747379 < baseStart_6747379 := by decide
  rcases family_descends (prefixWord ++ tailWord_6747379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6747395 : List Nat := [1, 1, 1, 3, 2, 4, 2, 1, 2, 1, 5]
def baseStart_6747395 : Nat := 118140960795 + 6747395 * 2 ^ 59
def prefixEnd_6747395 : Nat := 4983230072969 + 3 ^ 40 * 6747395 * 2
def baseEnd_6747395 : Nat := 3464656800743733519731801

theorem tailTrace_6747395 : CollatzResearch.WordTrace tailWord_6747395 prefixEnd_6747395 3464656800743733519731801 := by
  unfold tailWord_6747395
  simp only [CollatzResearch.WordTrace]
  refine ⟨246097713390347753166779639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164065142260231835444519759 246097713390347753166779639)
  ·
    refine ⟨369146570085521629750169459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246097713390347753166779639 369146570085521629750169459)
    ·
      refine ⟨553719855128282444625254189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369146570085521629750169459 553719855128282444625254189)
      ·
        refine ⟨207644945673105916734470321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 553719855128282444625254189 207644945673105916734470321)
        ·
          refine ⟨155733709254829437550852741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207644945673105916734470321 155733709254829437550852741)
          ·
            refine ⟨29200070485280519540784889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 155733709254829437550852741 29200070485280519540784889)
            ·
              refine ⟨21900052863960389655588667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29200070485280519540784889 21900052863960389655588667)
              ·
                refine ⟨32850079295940584483383001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21900052863960389655588667 32850079295940584483383001)
                ·
                  refine ⟨24637559471955438362537251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32850079295940584483383001 24637559471955438362537251)
                  ·
                    refine ⟨36956339207933157543805877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24637559471955438362537251 36956339207933157543805877)
                    ·
                      refine ⟨3464656800743733519731801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36956339207933157543805877 3464656800743733519731801)
                      ·
                        rfl

theorem cell23_6747395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 1, 2, 1, 5].length) (baseStart_6747395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6747395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6747395 prefixEnd_6747395 := by exact prefixLift 6747395
  have htrace : WordTrace (prefixWord ++ tailWord_6747395) baseStart_6747395 baseEnd_6747395 := by
    simpa [prefixWord, tailWord_6747395, baseEnd_6747395] using wordTrace_append hprefix tailTrace_6747395
  have hstable : (prefixWord ++ tailWord_6747395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6747395).length < 2 ^ (prefixWord ++ tailWord_6747395).sum := by decide
  have hdescent : baseEnd_6747395 < baseStart_6747395 := by decide
  rcases family_descends (prefixWord ++ tailWord_6747395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6747415 : List Nat := [1, 1, 3, 4, 1, 1, 2, 3, 7]
def baseStart_6747415 : Nat := 118140960795 + 6747415 * 2 ^ 59
def prefixEnd_6747415 : Nat := 4983230072969 + 3 ^ 40 * 6747415 * 2
def baseEnd_6747415 : Nat := 384963007817424826831301

theorem tailTrace_6747415 : CollatzResearch.WordTrace tailWord_6747415 prefixEnd_6747415 384963007817424826831301 := by
  unfold tailWord_6747415
  simp only [CollatzResearch.WordTrace]
  refine ⟨246098442850275296582507699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164065628566850197721671799 246098442850275296582507699)
  ·
    refine ⟨369147664275412944873761549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246098442850275296582507699 369147664275412944873761549)
    ·
      refine ⟨138430374103279854327660581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 369147664275412944873761549 138430374103279854327660581)
      ·
        refine ⟨25955695144364972686436359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 138430374103279854327660581 25955695144364972686436359)
        ·
          refine ⟨38933542716547459029654539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25955695144364972686436359 38933542716547459029654539)
          ·
            refine ⟨58400314074821188544481809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38933542716547459029654539 58400314074821188544481809)
            ·
              refine ⟨43800235556115891408361357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58400314074821188544481809 43800235556115891408361357)
              ·
                refine ⟨16425088333543459278135509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43800235556115891408361357 16425088333543459278135509)
                ·
                  refine ⟨384963007817424826831301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16425088333543459278135509 384963007817424826831301)
                  ·
                    rfl

theorem cell23_6747415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 3, 7].length) (baseStart_6747415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6747415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6747415 prefixEnd_6747415 := by exact prefixLift 6747415
  have htrace : WordTrace (prefixWord ++ tailWord_6747415) baseStart_6747415 baseEnd_6747415 := by
    simpa [prefixWord, tailWord_6747415, baseEnd_6747415] using wordTrace_append hprefix tailTrace_6747415
  have hstable : (prefixWord ++ tailWord_6747415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6747415).length < 2 ^ (prefixWord ++ tailWord_6747415).sum := by decide
  have hdescent : baseEnd_6747415 < baseStart_6747415 := by decide
  rcases family_descends (prefixWord ++ tailWord_6747415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6747426 : List Nat := [3, 3, 1, 1, 4, 1, 2, 1, 1, 4, 2]
def baseStart_6747426 : Nat := 118140960795 + 6747426 * 2 ^ 59
def prefixEnd_6747426 : Nat := 4983230072969 + 3 ^ 40 * 6747426 * 2
def baseEnd_6747426 : Nat := 3464672718644022898444159

theorem tailTrace_6747426 : CollatzResearch.WordTrace tailWord_6747426 prefixEnd_6747426 3464672718644022898444159 := by
  unfold tailWord_6747426
  simp only [CollatzResearch.WordTrace]
  refine ⟨61524711013308861365289533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164065896035490296974105421 61524711013308861365289533)
  ·
    refine ⟨23071766629990823011983575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61524711013308861365289533 23071766629990823011983575)
    ·
      refine ⟨34607649944986234517975363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23071766629990823011983575 34607649944986234517975363)
      ·
        refine ⟨51911474917479351776963045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34607649944986234517975363 51911474917479351776963045)
        ·
          refine ⟨9733401547027378458180571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51911474917479351776963045 9733401547027378458180571)
          ·
            refine ⟨14600102320541067687270857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9733401547027378458180571 14600102320541067687270857)
            ·
              refine ⟨10950076740405800765453143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14600102320541067687270857 10950076740405800765453143)
              ·
                refine ⟨16425115110608701148179715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10950076740405800765453143 16425115110608701148179715)
                ·
                  refine ⟨24637672665913051722269573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16425115110608701148179715 24637672665913051722269573)
                  ·
                    refine ⟨4619563624858697197925545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24637672665913051722269573 4619563624858697197925545)
                    ·
                      refine ⟨3464672718644022898444159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4619563624858697197925545 3464672718644022898444159)
                      ·
                        rfl

theorem cell23_6747426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 1, 1, 4, 2].length) (baseStart_6747426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6747426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6747426 prefixEnd_6747426 := by exact prefixLift 6747426
  have htrace : WordTrace (prefixWord ++ tailWord_6747426) baseStart_6747426 baseEnd_6747426 := by
    simpa [prefixWord, tailWord_6747426, baseEnd_6747426] using wordTrace_append hprefix tailTrace_6747426
  have hstable : (prefixWord ++ tailWord_6747426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6747426).length < 2 ^ (prefixWord ++ tailWord_6747426).sum := by decide
  have hdescent : baseEnd_6747426 < baseStart_6747426 := by decide
  rcases family_descends (prefixWord ++ tailWord_6747426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6747432 : List Nat := [2, 1, 5, 1, 2, 2, 1, 2, 7]
def baseStart_6747432 : Nat := 118140960795 + 6747432 * 2 ^ 59
def prefixEnd_6747432 : Nat := 4983230072969 + 3 ^ 40 * 6747432 * 2
def baseEnd_6747432 : Nat := 384963977725327763885459

theorem tailTrace_6747432 : CollatzResearch.WordTrace tailWord_6747432 prefixEnd_6747432 384963977725327763885459 := by
  unfold tailWord_6747432
  simp only [CollatzResearch.WordTrace]
  refine ⟨123049531445606854242938275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164066041927475805657251033 123049531445606854242938275)
  ·
    refine ⟨184574297168410281364407413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123049531445606854242938275 184574297168410281364407413)
    ·
      refine ⟨17303840359538463877913195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 184574297168410281364407413 17303840359538463877913195)
      ·
        refine ⟨25955760539307695816869793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17303840359538463877913195 25955760539307695816869793)
        ·
          refine ⟨19466820404480771862652345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25955760539307695816869793 19466820404480771862652345)
          ·
            refine ⟨14600115303360578896989259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19466820404480771862652345 14600115303360578896989259)
            ·
              refine ⟨21900172955040868345483889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14600115303360578896989259 21900172955040868345483889)
              ·
                refine ⟨16425129716280651259112917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21900172955040868345483889 16425129716280651259112917)
                ·
                  refine ⟨384963977725327763885459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16425129716280651259112917 384963977725327763885459)
                  ·
                    rfl

theorem cell23_6747432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 2, 7].length) (baseStart_6747432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6747432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6747432 prefixEnd_6747432 := by exact prefixLift 6747432
  have htrace : WordTrace (prefixWord ++ tailWord_6747432) baseStart_6747432 baseEnd_6747432 := by
    simpa [prefixWord, tailWord_6747432, baseEnd_6747432] using wordTrace_append hprefix tailTrace_6747432
  have hstable : (prefixWord ++ tailWord_6747432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6747432).length < 2 ^ (prefixWord ++ tailWord_6747432).sum := by decide
  have hdescent : baseEnd_6747432 < baseStart_6747432 := by decide
  rcases family_descends (prefixWord ++ tailWord_6747432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6747460 : List Nat := [2, 3, 4, 1, 1, 3, 1, 2, 2, 2, 2]
def baseStart_6747460 : Nat := 118140960795 + 6747460 * 2 ^ 59
def prefixEnd_6747460 : Nat := 4983230072969 + 3 ^ 40 * 6747460 * 2
def baseEnd_6747460 : Nat := 3464690176986275765419003

theorem tailTrace_6747460 : CollatzResearch.WordTrace tailWord_6747460 prefixEnd_6747460 3464690176986275765419003 := by
  unfold tailWord_6747460
  simp only [CollatzResearch.WordTrace]
  refine ⟨123050042067556134633947917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164066722756741512845263889 123050042067556134633947917)
  ·
    refine ⟨46143765775333550487730469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123050042067556134633947917 46143765775333550487730469)
    ·
      refine ⟨8651956082875040716449463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46143765775333550487730469 8651956082875040716449463)
      ·
        refine ⟨12977934124312561074674195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8651956082875040716449463 12977934124312561074674195)
        ·
          refine ⟨19466901186468841612011293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12977934124312561074674195 19466901186468841612011293)
          ·
            refine ⟨7300087944925815604504235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19466901186468841612011293 7300087944925815604504235)
            ·
              refine ⟨10950131917388723406756353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7300087944925815604504235 10950131917388723406756353)
              ·
                refine ⟨8212598938041542555067265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10950131917388723406756353 8212598938041542555067265)
                ·
                  refine ⟨6159449203531156916300449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8212598938041542555067265 6159449203531156916300449)
                  ·
                    refine ⟨4619586902648367687225337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6159449203531156916300449 4619586902648367687225337)
                    ·
                      refine ⟨3464690176986275765419003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4619586902648367687225337 3464690176986275765419003)
                      ·
                        rfl

theorem cell23_6747460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 2, 2, 2, 2].length) (baseStart_6747460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6747460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6747460 prefixEnd_6747460 := by exact prefixLift 6747460
  have htrace : WordTrace (prefixWord ++ tailWord_6747460) baseStart_6747460 baseEnd_6747460 := by
    simpa [prefixWord, tailWord_6747460, baseEnd_6747460] using wordTrace_append hprefix tailTrace_6747460
  have hstable : (prefixWord ++ tailWord_6747460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6747460).length < 2 ^ (prefixWord ++ tailWord_6747460).sum := by decide
  have hdescent : baseEnd_6747460 < baseStart_6747460 := by decide
  rcases family_descends (prefixWord ++ tailWord_6747460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6747505 : List Nat := [1, 2, 2, 2, 1, 2, 3, 2, 8]
def baseStart_6747505 : Nat := 118140960795 + 6747505 * 2 ^ 59
def prefixEnd_6747505 : Nat := 4983230072969 + 3 ^ 40 * 6747505 * 2
def baseEnd_6747505 : Nat := 384968142623969787706255

theorem tailTrace_6747505 : CollatzResearch.WordTrace tailWord_6747505 prefixEnd_6747505 384968142623969787706255 := by
  unfold tailWord_6747505
  simp only [CollatzResearch.WordTrace]
  refine ⟨246101725419949241953283969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164067816946632827968855979 246101725419949241953283969)
  ·
    refine ⟨184576294064961931464962977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246101725419949241953283969 184576294064961931464962977)
    ·
      refine ⟨138432220548721448598722233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184576294064961931464962977 138432220548721448598722233)
      ·
        refine ⟨103824165411541086449041675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138432220548721448598722233 103824165411541086449041675)
        ·
          refine ⟨155736248117311629673562513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103824165411541086449041675 155736248117311629673562513)
          ·
            refine ⟨116802186087983722255171885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155736248117311629673562513 116802186087983722255171885)
            ·
              refine ⟨43800819782993895845689457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116802186087983722255171885 43800819782993895845689457)
              ·
                refine ⟨32850614837245421884267093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43800819782993895845689457 32850614837245421884267093)
                ·
                  refine ⟨384968142623969787706255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32850614837245421884267093 384968142623969787706255)
                  ·
                    rfl

theorem cell23_6747505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 2, 8].length) (baseStart_6747505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6747505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6747505 prefixEnd_6747505 := by exact prefixLift 6747505
  have htrace : WordTrace (prefixWord ++ tailWord_6747505) baseStart_6747505 baseEnd_6747505 := by
    simpa [prefixWord, tailWord_6747505, baseEnd_6747505] using wordTrace_append hprefix tailTrace_6747505
  have hstable : (prefixWord ++ tailWord_6747505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6747505).length < 2 ^ (prefixWord ++ tailWord_6747505).sum := by decide
  have hdescent : baseEnd_6747505 < baseStart_6747505 := by decide
  rcases family_descends (prefixWord ++ tailWord_6747505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6747525 : List Nat := [1, 3, 1, 1, 3, 1, 2, 1, 1, 1, 8]
def baseStart_6747525 : Nat := 118140960795 + 6747525 * 2 ^ 59
def prefixEnd_6747525 : Nat := 4983230072969 + 3 ^ 40 * 6747525 * 2
def baseEnd_6747525 : Nat := 3464723553228818011106203

theorem tailTrace_6747525 : CollatzResearch.WordTrace tailWord_6747525 prefixEnd_6747525 3464723553228818011106203 := by
  unfold tailWord_6747525
  simp only [CollatzResearch.WordTrace]
  refine ⟨246102454879876785369012029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164068303253251190246008019 246102454879876785369012029)
  ·
    refine ⟨92288420579953794513379511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 246102454879876785369012029 92288420579953794513379511)
    ·
      refine ⟨138432630869930691770069267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92288420579953794513379511 138432630869930691770069267)
      ·
        refine ⟨207648946304896037655103901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138432630869930691770069267 207648946304896037655103901)
        ·
          refine ⟨77868354864336014120663963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 207648946304896037655103901 77868354864336014120663963)
          ·
            refine ⟨116802532296504021180995945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77868354864336014120663963 116802532296504021180995945)
            ·
              refine ⟨87601899222378015885746959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116802532296504021180995945 87601899222378015885746959)
              ·
                refine ⟨131402848833567023828620439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87601899222378015885746959 131402848833567023828620439)
                ·
                  refine ⟨197104273250350535742930659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 131402848833567023828620439 197104273250350535742930659)
                  ·
                    refine ⟨295656409875525803614395989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 197104273250350535742930659 295656409875525803614395989)
                    ·
                      refine ⟨3464723553228818011106203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 295656409875525803614395989 3464723553228818011106203)
                      ·
                        rfl

theorem cell23_6747525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 1, 8].length) (baseStart_6747525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6747525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6747525 prefixEnd_6747525 := by exact prefixLift 6747525
  have htrace : WordTrace (prefixWord ++ tailWord_6747525) baseStart_6747525 baseEnd_6747525 := by
    simpa [prefixWord, tailWord_6747525, baseEnd_6747525] using wordTrace_append hprefix tailTrace_6747525
  have hstable : (prefixWord ++ tailWord_6747525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6747525).length < 2 ^ (prefixWord ++ tailWord_6747525).sum := by decide
  have hdescent : baseEnd_6747525 < baseStart_6747525 := by decide
  rcases family_descends (prefixWord ++ tailWord_6747525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6747552 : List Nat := [2, 1, 1, 4, 1, 2, 3, 1, 3, 5]
def baseStart_6747552 : Nat := 118140960795 + 6747552 * 2 ^ 59
def prefixEnd_6747552 : Nat := 4983230072969 + 3 ^ 40 * 6747552 * 2
def baseEnd_6747552 : Nat := 1154912472402163135156193

theorem tailTrace_6747552 : CollatzResearch.WordTrace tailWord_6747552 prefixEnd_6747552 1154912472402163135156193 := by
  unfold tailWord_6747552
  simp only [CollatzResearch.WordTrace]
  refine ⟨123051719825389484490122455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164068959767185979320163273 123051719825389484490122455)
  ·
    refine ⟨184577579738084226735183683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123051719825389484490122455 184577579738084226735183683)
    ·
      refine ⟨276866369607126340102775525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184577579738084226735183683 276866369607126340102775525)
      ·
        refine ⟨51912444301336188769270411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 276866369607126340102775525 51912444301336188769270411)
        ·
          refine ⟨77868666452004283153905617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51912444301336188769270411 77868666452004283153905617)
          ·
            refine ⟨58401499839003212365429213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77868666452004283153905617 58401499839003212365429213)
            ·
              refine ⟨21900562439626204637035955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58401499839003212365429213 21900562439626204637035955)
              ·
                refine ⟨32850843659439306955553933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21900562439626204637035955 32850843659439306955553933)
                ·
                  refine ⟨12319066372289740108332725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32850843659439306955553933 12319066372289740108332725)
                  ·
                    refine ⟨1154912472402163135156193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12319066372289740108332725 1154912472402163135156193)
                    ·
                      rfl

theorem cell23_6747552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 1, 3, 5].length) (baseStart_6747552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6747552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6747552 prefixEnd_6747552 := by exact prefixLift 6747552
  have htrace : WordTrace (prefixWord ++ tailWord_6747552) baseStart_6747552 baseEnd_6747552 := by
    simpa [prefixWord, tailWord_6747552, baseEnd_6747552] using wordTrace_append hprefix tailTrace_6747552
  have hstable : (prefixWord ++ tailWord_6747552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6747552).length < 2 ^ (prefixWord ++ tailWord_6747552).sum := by decide
  have hdescent : baseEnd_6747552 < baseStart_6747552 := by decide
  rcases family_descends (prefixWord ++ tailWord_6747552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6747582 : List Nat := [4, 2, 1, 1, 1, 1, 1, 1, 5, 6]
def baseStart_6747582 : Nat := 118140960795 + 6747582 * 2 ^ 59
def prefixEnd_6747582 : Nat := 4983230072969 + 3 ^ 40 * 6747582 * 2
def baseEnd_6747582 : Nat := 1154917607208708096031147

theorem tailTrace_6747582 : CollatzResearch.WordTrace tailWord_6747582 prefixEnd_6747582 1154917607208708096031147 := by
  unfold tailWord_6747582
  simp only [CollatzResearch.WordTrace]
  refine ⟨30763066730083785512979625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164069689227113522735891333 30763066730083785512979625)
  ·
    refine ⟨23072300047562839134734719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30763066730083785512979625 23072300047562839134734719)
    ·
      refine ⟨34608450071344258702102079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23072300047562839134734719 34608450071344258702102079)
      ·
        refine ⟨51912675107016388053153119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34608450071344258702102079 51912675107016388053153119)
        ·
          refine ⟨77869012660524582079729679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51912675107016388053153119 77869012660524582079729679)
          ·
            refine ⟨116803518990786873119594519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77869012660524582079729679 116803518990786873119594519)
            ·
              refine ⟨175205278486180309679391779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116803518990786873119594519 175205278486180309679391779)
              ·
                refine ⟨262807917729270464519087669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 175205278486180309679391779 262807917729270464519087669)
                ·
                  refine ⟨24638242287119106048664469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 262807917729270464519087669 24638242287119106048664469)
                  ·
                    refine ⟨1154917607208708096031147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24638242287119106048664469 1154917607208708096031147)
                    ·
                      rfl

theorem cell23_6747582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 5, 6].length) (baseStart_6747582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6747582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6747582 prefixEnd_6747582 := by exact prefixLift 6747582
  have htrace : WordTrace (prefixWord ++ tailWord_6747582) baseStart_6747582 baseEnd_6747582 := by
    simpa [prefixWord, tailWord_6747582, baseEnd_6747582] using wordTrace_append hprefix tailTrace_6747582
  have hstable : (prefixWord ++ tailWord_6747582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6747582).length < 2 ^ (prefixWord ++ tailWord_6747582).sum := by decide
  have hdescent : baseEnd_6747582 < baseStart_6747582 := by decide
  rcases family_descends (prefixWord ++ tailWord_6747582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6747592 : List Nat := [2, 1, 3, 1, 3, 1, 2, 1, 3, 1, 5]
def baseStart_6747592 : Nat := 118140960795 + 6747592 * 2 ^ 59
def prefixEnd_6747592 : Nat := 4983230072969 + 3 ^ 40 * 6747592 * 2
def baseEnd_6747592 : Nat := 3464757956432669248968395

theorem tailTrace_6747592 : CollatzResearch.WordTrace tailWord_6747592 prefixEnd_6747592 3464757956432669248968395 := by
  unfold tailWord_6747592
  simp only [CollatzResearch.WordTrace]
  refine ⟨123052449285317027905850515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164069932380422703874467353 123052449285317027905850515)
  ·
    refine ⟨184578673927975541858775773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123052449285317027905850515 184578673927975541858775773)
    ·
      refine ⟨69217002722990828197040915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184578673927975541858775773 69217002722990828197040915)
      ·
        refine ⟨103825504084486242295561373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69217002722990828197040915 103825504084486242295561373)
        ·
          refine ⟨38934564031682340860835515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103825504084486242295561373 38934564031682340860835515)
          ·
            refine ⟨58401846047523511291253273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38934564031682340860835515 58401846047523511291253273)
            ·
              refine ⟨43801384535642633468439955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58401846047523511291253273 43801384535642633468439955)
              ·
                refine ⟨65702076803463950202659933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43801384535642633468439955 65702076803463950202659933)
                ·
                  refine ⟨24638278801298981325997475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65702076803463950202659933 24638278801298981325997475)
                  ·
                    refine ⟨36957418201948471988996213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24638278801298981325997475 36957418201948471988996213)
                    ·
                      refine ⟨3464757956432669248968395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36957418201948471988996213 3464757956432669248968395)
                      ·
                        rfl

theorem cell23_6747592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 1, 3, 1, 5].length) (baseStart_6747592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6747592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6747592 prefixEnd_6747592 := by exact prefixLift 6747592
  have htrace : WordTrace (prefixWord ++ tailWord_6747592) baseStart_6747592 baseEnd_6747592 := by
    simpa [prefixWord, tailWord_6747592, baseEnd_6747592] using wordTrace_append hprefix tailTrace_6747592
  have hstable : (prefixWord ++ tailWord_6747592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6747592).length < 2 ^ (prefixWord ++ tailWord_6747592).sum := by decide
  have hdescent : baseEnd_6747592 < baseStart_6747592 := by decide
  rcases family_descends (prefixWord ++ tailWord_6747592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6747599 : List Nat := [1, 1, 2, 1, 1, 4, 4, 3, 2, 4]
def baseStart_6747599 : Nat := 118140960795 + 6747599 * 2 ^ 59
def prefixEnd_6747599 : Nat := 4983230072969 + 3 ^ 40 * 6747599 * 2
def baseEnd_6747599 : Nat := 1154920516932416907193621

theorem tailTrace_6747599 : CollatzResearch.WordTrace tailWord_6747599 prefixEnd_6747599 1154920516932416907193621 := by
  unfold tailWord_6747599
  simp only [CollatzResearch.WordTrace]
  refine ⟨246105153881608696007205851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164070102587739130671470567 246105153881608696007205851)
  ·
    refine ⟨369157730822413044010808777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246105153881608696007205851 369157730822413044010808777)
    ·
      refine ⟨276868298116809783008106583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 369157730822413044010808777 276868298116809783008106583)
      ·
        refine ⟨415302447175214674512159875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276868298116809783008106583 415302447175214674512159875)
        ·
          refine ⟨622953670762822011768239813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 415302447175214674512159875 622953670762822011768239813)
          ·
            refine ⟨116803813268029127206544965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 622953670762822011768239813 116803813268029127206544965)
            ·
              refine ⟨21900714987755461351227181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 116803813268029127206544965 21900714987755461351227181)
              ·
                refine ⟨8212768120408298006710193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21900714987755461351227181 8212768120408298006710193)
                ·
                  refine ⟨6159576090306223505032645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8212768120408298006710193 6159576090306223505032645)
                  ·
                    refine ⟨1154920516932416907193621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6159576090306223505032645 1154920516932416907193621)
                    ·
                      rfl

theorem cell23_6747599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 3, 2, 4].length) (baseStart_6747599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6747599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6747599 prefixEnd_6747599 := by exact prefixLift 6747599
  have htrace : WordTrace (prefixWord ++ tailWord_6747599) baseStart_6747599 baseEnd_6747599 := by
    simpa [prefixWord, tailWord_6747599, baseEnd_6747599] using wordTrace_append hprefix tailTrace_6747599
  have hstable : (prefixWord ++ tailWord_6747599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6747599).length < 2 ^ (prefixWord ++ tailWord_6747599).sum := by decide
  have hdescent : baseEnd_6747599 < baseStart_6747599 := by decide
  rcases family_descends (prefixWord ++ tailWord_6747599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6747606 : List Nat := [5, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4]
def baseStart_6747606 : Nat := 118140960795 + 6747606 * 2 ^ 59
def prefixEnd_6747606 : Nat := 4983230072969 + 3 ^ 40 * 6747606 * 2
def baseEnd_6747606 : Nat := 3464765145161832194193331

theorem tailTrace_6747606 : CollatzResearch.WordTrace tailWord_6747606 prefixEnd_6747606 3464765145161832194193331 := by
  unfold tailWord_6747606
  simp only [CollatzResearch.WordTrace]
  refine ⟨15381588074536458512669417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 164070272795055557468473781 15381588074536458512669417)
  ·
    refine ⟨11536191055902343884502063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15381588074536458512669417 11536191055902343884502063)
    ·
      refine ⟨17304286583853515826753095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11536191055902343884502063 17304286583853515826753095)
      ·
        refine ⟨25956429875780273740129643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17304286583853515826753095 25956429875780273740129643)
        ·
          refine ⟨38934644813670410610194465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25956429875780273740129643 38934644813670410610194465)
          ·
            refine ⟨29200983610252807957645849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38934644813670410610194465 29200983610252807957645849)
            ·
              refine ⟨21900737707689605968234387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29200983610252807957645849 21900737707689605968234387)
              ·
                refine ⟨32851106561534408952351581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21900737707689605968234387 32851106561534408952351581)
                ·
                  refine ⟨12319164960575403357131843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32851106561534408952351581 12319164960575403357131843)
                  ·
                    refine ⟨18478747440863105035697765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12319164960575403357131843 18478747440863105035697765)
                    ·
                      refine ⟨3464765145161832194193331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18478747440863105035697765 3464765145161832194193331)
                      ·
                        rfl

theorem cell23_6747606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_6747606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6747606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6747606 prefixEnd_6747606 := by exact prefixLift 6747606
  have htrace : WordTrace (prefixWord ++ tailWord_6747606) baseStart_6747606 baseEnd_6747606 := by
    simpa [prefixWord, tailWord_6747606, baseEnd_6747606] using wordTrace_append hprefix tailTrace_6747606
  have hstable : (prefixWord ++ tailWord_6747606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6747606).length < 2 ^ (prefixWord ++ tailWord_6747606).sum := by decide
  have hdescent : baseEnd_6747606 < baseStart_6747606 := by decide
  rcases family_descends (prefixWord ++ tailWord_6747606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6747609 : List Nat := [1, 2, 1, 2, 4, 2, 2, 1, 3, 2, 3]
def baseStart_6747609 : Nat := 118140960795 + 6747609 * 2 ^ 59
def prefixEnd_6747609 : Nat := 4983230072969 + 3 ^ 40 * 6747609 * 2
def baseEnd_6747609 : Nat := 3464766685603795682455817

theorem tailTrace_6747609 : CollatzResearch.WordTrace tailWord_6747609 prefixEnd_6747609 3464766685603795682455817 := by
  unfold tailWord_6747609
  simp only [CollatzResearch.WordTrace]
  refine ⟨246105518611572467715069881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164070345741048311810046587 246105518611572467715069881)
  ·
    refine ⟨184579138958679350786302411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246105518611572467715069881 184579138958679350786302411)
    ·
      refine ⟨276868708438019026179453617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184579138958679350786302411 276868708438019026179453617)
      ·
        refine ⟨207651531328514269634590213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 276868708438019026179453617 207651531328514269634590213)
        ·
          refine ⟨38934662124096425556485665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 207651531328514269634590213 38934662124096425556485665)
          ·
            refine ⟨29200996593072319167364249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38934662124096425556485665 29200996593072319167364249)
            ·
              refine ⟨21900747444804239375523187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29200996593072319167364249 21900747444804239375523187)
              ·
                refine ⟨32851121167206359063284781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21900747444804239375523187 32851121167206359063284781)
                ·
                  refine ⟨12319170437702384648731793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32851121167206359063284781 12319170437702384648731793)
                  ·
                    refine ⟨9239377828276788486548845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12319170437702384648731793 9239377828276788486548845)
                    ·
                      refine ⟨3464766685603795682455817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9239377828276788486548845 3464766685603795682455817)
                      ·
                        rfl

theorem cell23_6747609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 1, 3, 2, 3].length) (baseStart_6747609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6747609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6747609 prefixEnd_6747609 := by exact prefixLift 6747609
  have htrace : WordTrace (prefixWord ++ tailWord_6747609) baseStart_6747609 baseEnd_6747609 := by
    simpa [prefixWord, tailWord_6747609, baseEnd_6747609] using wordTrace_append hprefix tailTrace_6747609
  have hstable : (prefixWord ++ tailWord_6747609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6747609).length < 2 ^ (prefixWord ++ tailWord_6747609).sum := by decide
  have hdescent : baseEnd_6747609 < baseStart_6747609 := by decide
  rcases family_descends (prefixWord ++ tailWord_6747609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6747619 : List Nat := [1, 1, 1, 6, 2, 1, 2, 2, 1, 2, 4]
def baseStart_6747619 : Nat := 118140960795 + 6747619 * 2 ^ 59
def prefixEnd_6747619 : Nat := 4983230072969 + 3 ^ 40 * 6747619 * 2
def baseEnd_6747619 : Nat := 3464771820410340643330771

theorem tailTrace_6747619 : CollatzResearch.WordTrace tailWord_6747619 prefixEnd_6747619 3464771820410340643330771 := by
  unfold tailWord_6747619
  simp only [CollatzResearch.WordTrace]
  refine ⟨246105883341536239422933911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164070588894357492948622607 246105883341536239422933911)
  ·
    refine ⟨369158825012304359134400867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246105883341536239422933911 369158825012304359134400867)
    ·
      refine ⟨553738237518456538701601301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369158825012304359134400867 553738237518456538701601301)
      ·
        refine ⟨25956479883677650251637561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 553738237518456538701601301 25956479883677650251637561)
        ·
          refine ⟨19467359912758237688728171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25956479883677650251637561 19467359912758237688728171)
          ·
            refine ⟨29201039869137356533092257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19467359912758237688728171 29201039869137356533092257)
            ·
              refine ⟨21900779901853017399819193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29201039869137356533092257 21900779901853017399819193)
              ·
                refine ⟨16425584926389763049864395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21900779901853017399819193 16425584926389763049864395)
                ·
                  refine ⟨24638377389584644574796593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16425584926389763049864395 24638377389584644574796593)
                  ·
                    refine ⟨18478783042188483431097445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24638377389584644574796593 18478783042188483431097445)
                    ·
                      refine ⟨3464771820410340643330771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18478783042188483431097445 3464771820410340643330771)
                      ·
                        rfl

theorem cell23_6747619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_6747619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6747619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6747619 prefixEnd_6747619 := by exact prefixLift 6747619
  have htrace : WordTrace (prefixWord ++ tailWord_6747619) baseStart_6747619 baseEnd_6747619 := by
    simpa [prefixWord, tailWord_6747619, baseEnd_6747619] using wordTrace_append hprefix tailTrace_6747619
  have hstable : (prefixWord ++ tailWord_6747619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6747619).length < 2 ^ (prefixWord ++ tailWord_6747619).sum := by decide
  have hdescent : baseEnd_6747619 < baseStart_6747619 := by decide
  rcases family_descends (prefixWord ++ tailWord_6747619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6747623 : List Nat := [1, 1, 5, 2, 1, 4, 2, 1, 1, 1, 4]
def baseStart_6747623 : Nat := 118140960795 + 6747623 * 2 ^ 59
def prefixEnd_6747623 : Nat := 4983230072969 + 3 ^ 40 * 6747623 * 2
def baseEnd_6747623 : Nat := 3464773874332958627680753

theorem tailTrace_6747623 : CollatzResearch.WordTrace tailWord_6747623 prefixEnd_6747623 3464773874332958627680753 := by
  unfold tailWord_6747623
  simp only [CollatzResearch.WordTrace]
  refine ⟨246106029233521748106079523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164070686155681165404053015 246106029233521748106079523)
  ·
    refine ⟨369159043850282622159119285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246106029233521748106079523 369159043850282622159119285)
    ·
      refine ⟨34608660360963995827417433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 369159043850282622159119285 34608660360963995827417433)
      ·
        refine ⟨25956495270722996870563075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34608660360963995827417433 25956495270722996870563075)
        ·
          refine ⟨38934742906084495305844613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25956495270722996870563075 38934742906084495305844613)
          ·
            refine ⟨7300264294890842869845865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38934742906084495305844613 7300264294890842869845865)
            ·
              refine ⟨5475198221168132152384399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7300264294890842869845865 5475198221168132152384399)
              ·
                refine ⟨8212797331752198228576599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5475198221168132152384399 8212797331752198228576599)
                ·
                  refine ⟨12319195997628297342864899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8212797331752198228576599 12319195997628297342864899)
                  ·
                    refine ⟨18478793996442446014297349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12319195997628297342864899 18478793996442446014297349)
                    ·
                      refine ⟨3464773874332958627680753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18478793996442446014297349 3464773874332958627680753)
                      ·
                        rfl

theorem cell23_6747623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 2, 1, 1, 1, 4].length) (baseStart_6747623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6747623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6747623 prefixEnd_6747623 := by exact prefixLift 6747623
  have htrace : WordTrace (prefixWord ++ tailWord_6747623) baseStart_6747623 baseEnd_6747623 := by
    simpa [prefixWord, tailWord_6747623, baseEnd_6747623] using wordTrace_append hprefix tailTrace_6747623
  have hstable : (prefixWord ++ tailWord_6747623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6747623).length < 2 ^ (prefixWord ++ tailWord_6747623).sum := by decide
  have hdescent : baseEnd_6747623 < baseStart_6747623 := by decide
  rcases family_descends (prefixWord ++ tailWord_6747623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6747629 : List Nat := [1, 5, 1, 3, 2, 1, 10]
def baseStart_6747629 : Nat := 118140960795 + 6747629 * 2 ^ 59
def prefixEnd_6747629 : Nat := 4983230072969 + 3 ^ 40 * 6747629 * 2
def baseEnd_6747629 : Nat := 42775024138480069187725

theorem tailTrace_6747629 : CollatzResearch.WordTrace tailWord_6747629 prefixEnd_6747629 42775024138480069187725 := by
  unfold tailWord_6747629
  simp only [CollatzResearch.WordTrace]
  refine ⟨246106248071500011130797941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164070832047666674087198627 246106248071500011130797941)
  ·
    refine ⟨23072460756703126043512307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 246106248071500011130797941 23072460756703126043512307)
    ·
      refine ⟨34608691135054689065268461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23072460756703126043512307 34608691135054689065268461)
      ·
        refine ⟨12978259175645508399475673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34608691135054689065268461 12978259175645508399475673)
        ·
          refine ⟨9733694381734131299606755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12978259175645508399475673 9733694381734131299606755)
          ·
            refine ⟨14600541572601196949410133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9733694381734131299606755 14600541572601196949410133)
            ·
              refine ⟨42775024138480069187725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14600541572601196949410133 42775024138480069187725)
              ·
                rfl

theorem cell23_6747629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 10].length) (baseStart_6747629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6747629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6747629 prefixEnd_6747629 := by exact prefixLift 6747629
  have htrace : WordTrace (prefixWord ++ tailWord_6747629) baseStart_6747629 baseEnd_6747629 := by
    simpa [prefixWord, tailWord_6747629, baseEnd_6747629] using wordTrace_append hprefix tailTrace_6747629
  have hstable : (prefixWord ++ tailWord_6747629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6747629).length < 2 ^ (prefixWord ++ tailWord_6747629).sum := by decide
  have hdescent : baseEnd_6747629 < baseStart_6747629 := by decide
  rcases family_descends (prefixWord ++ tailWord_6747629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6747650 : List Nat := [3, 4, 1, 2, 1, 2, 3, 1, 2, 4]
def baseStart_6747650 : Nat := 118140960795 + 6747650 * 2 ^ 59
def prefixEnd_6747650 : Nat := 4983230072969 + 3 ^ 40 * 6747650 * 2
def baseEnd_6747650 : Nat := 1154929246103543340681043

theorem tailTrace_6747650 : CollatzResearch.WordTrace tailWord_6747650 prefixEnd_6747650 1154929246103543340681043 := by
  unfold tailWord_6747650
  simp only [CollatzResearch.WordTrace]
  refine ⟨61526753501105982929328101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164071342669615954478208269 61526753501105982929328101)
  ·
    refine ⟨11536266281457371799249019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61526753501105982929328101 11536266281457371799249019)
    ·
      refine ⟨17304399422186057698873529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11536266281457371799249019 17304399422186057698873529)
      ·
        refine ⟨12978299566639543274155147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17304399422186057698873529 12978299566639543274155147)
        ·
          refine ⟨19467449349959314911232721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12978299566639543274155147 19467449349959314911232721)
          ·
            refine ⟨14600587012469486183424541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19467449349959314911232721 14600587012469486183424541)
            ·
              refine ⟨5475220129676057318784203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14600587012469486183424541 5475220129676057318784203)
              ·
                refine ⟨8212830194514085978176305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5475220129676057318784203 8212830194514085978176305)
                ·
                  refine ⟨6159622645885564483632229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8212830194514085978176305 6159622645885564483632229)
                  ·
                    refine ⟨1154929246103543340681043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6159622645885564483632229 1154929246103543340681043)
                    ·
                      rfl

theorem cell23_6747650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 3, 1, 2, 4].length) (baseStart_6747650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6747650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6747650 prefixEnd_6747650 := by exact prefixLift 6747650
  have htrace : WordTrace (prefixWord ++ tailWord_6747650) baseStart_6747650 baseEnd_6747650 := by
    simpa [prefixWord, tailWord_6747650, baseEnd_6747650] using wordTrace_append hprefix tailTrace_6747650
  have hstable : (prefixWord ++ tailWord_6747650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6747650).length < 2 ^ (prefixWord ++ tailWord_6747650).sum := by decide
  have hdescent : baseEnd_6747650 < baseStart_6747650 := by decide
  rcases family_descends (prefixWord ++ tailWord_6747650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6747656 : List Nat := [2, 1, 3, 2, 1, 1, 2, 5, 2, 1, 3]
def baseStart_6747656 : Nat := 118140960795 + 6747656 * 2 ^ 59
def prefixEnd_6747656 : Nat := 4983230072969 + 3 ^ 40 * 6747656 * 2
def baseEnd_6747656 : Nat := 3464790819194556998568101

theorem tailTrace_6747656 : CollatzResearch.WordTrace tailWord_6747656 prefixEnd_6747656 3464790819194556998568101 := by
  unfold tailWord_6747656
  simp only [CollatzResearch.WordTrace]
  refine ⟨123053616421201097371015411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164071488561601463161353881 123053616421201097371015411)
  ·
    refine ⟨184580424631801646056523117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123053616421201097371015411 184580424631801646056523117)
    ·
      refine ⟨69217659236925617271196169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184580424631801646056523117 69217659236925617271196169)
      ·
        refine ⟨51913244427694212953397127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69217659236925617271196169 51913244427694212953397127)
        ·
          refine ⟨77869866641541319430095691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51913244427694212953397127 77869866641541319430095691)
          ·
            refine ⟨116804799962311979145143537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77869866641541319430095691 116804799962311979145143537)
            ·
              refine ⟨87603599971733984358857653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116804799962311979145143537 87603599971733984358857653)
              ·
                refine ⟨8212837497350061033642905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 87603599971733984358857653 8212837497350061033642905)
                ·
                  refine ⟨6159628123012545775232179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8212837497350061033642905 6159628123012545775232179)
                  ·
                    refine ⟨9239442184518818662848269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6159628123012545775232179 9239442184518818662848269)
                    ·
                      refine ⟨3464790819194556998568101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9239442184518818662848269 3464790819194556998568101)
                      ·
                        rfl

theorem cell23_6747656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 5, 2, 1, 3].length) (baseStart_6747656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6747656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6747656 prefixEnd_6747656 := by exact prefixLift 6747656
  have htrace : WordTrace (prefixWord ++ tailWord_6747656) baseStart_6747656 baseEnd_6747656 := by
    simpa [prefixWord, tailWord_6747656, baseEnd_6747656] using wordTrace_append hprefix tailTrace_6747656
  have hstable : (prefixWord ++ tailWord_6747656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6747656).length < 2 ^ (prefixWord ++ tailWord_6747656).sum := by decide
  have hdescent : baseEnd_6747656 < baseStart_6747656 := by decide
  rcases family_descends (prefixWord ++ tailWord_6747656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6747769 : List Nat := [1, 2, 1, 3, 3, 1, 2, 2, 1, 3, 4]
def baseStart_6747769 : Nat := 118140960795 + 6747769 * 2 ^ 59
def prefixEnd_6747769 : Nat := 4983230072969 + 3 ^ 40 * 6747769 * 2
def baseEnd_6747769 : Nat := 3464848842508515056455081

theorem tailTrace_6747769 : CollatzResearch.WordTrace tailWord_6747769 prefixEnd_6747769 3464848842508515056455081 := by
  unfold tailWord_6747769
  simp only [CollatzResearch.WordTrace]
  refine ⟨246111354290992815040894361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164074236193995210027262907 246111354290992815040894361)
  ·
    refine ⟨184583515718244611280670771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246111354290992815040894361 184583515718244611280670771)
    ·
      refine ⟨276875273577366916921006157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184583515718244611280670771 276875273577366916921006157)
      ·
        refine ⟨103828227591512593845377309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 276875273577366916921006157 103828227591512593845377309)
        ·
          refine ⟨38935585346817222692016491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103828227591512593845377309 38935585346817222692016491)
          ·
            refine ⟨58403378020225834038024737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38935585346817222692016491 58403378020225834038024737)
            ·
              refine ⟨43802533515169375528518553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58403378020225834038024737 43802533515169375528518553)
              ·
                refine ⟨32851900136377031646388915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43802533515169375528518553 32851900136377031646388915)
                ·
                  refine ⟨49277850204565547469583373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32851900136377031646388915 49277850204565547469583373)
                  ·
                    refine ⟨18479193826712080301093765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49277850204565547469583373 18479193826712080301093765)
                    ·
                      refine ⟨3464848842508515056455081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18479193826712080301093765 3464848842508515056455081)
                      ·
                        rfl

theorem cell23_6747769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 2, 1, 3, 4].length) (baseStart_6747769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6747769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6747769 prefixEnd_6747769 := by exact prefixLift 6747769
  have htrace : WordTrace (prefixWord ++ tailWord_6747769) baseStart_6747769 baseEnd_6747769 := by
    simpa [prefixWord, tailWord_6747769, baseEnd_6747769] using wordTrace_append hprefix tailTrace_6747769
  have hstable : (prefixWord ++ tailWord_6747769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6747769).length < 2 ^ (prefixWord ++ tailWord_6747769).sum := by decide
  have hdescent : baseEnd_6747769 < baseStart_6747769 := by decide
  rcases family_descends (prefixWord ++ tailWord_6747769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6747786 : List Nat := [3, 1, 2, 3, 2, 2, 1, 1, 1, 3, 4]
def baseStart_6747786 : Nat := 118140960795 + 6747786 * 2 ^ 59
def prefixEnd_6747786 : Nat := 4983230072969 + 3 ^ 40 * 6747786 * 2
def baseEnd_6747786 : Nat := 3464857571679641489942503

theorem tailTrace_6747786 : CollatzResearch.WordTrace tailWord_6747786 prefixEnd_6747786 3464857571679641489942503 := by
  unfold tailWord_6747786
  simp only [CollatzResearch.WordTrace]
  refine ⟨61527993582982806736065803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164074649554620817962842141 61527993582982806736065803)
  ·
    refine ⟨92291990374474210104098705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61527993582982806736065803 92291990374474210104098705)
    ·
      refine ⟨69218992780855657578074029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92291990374474210104098705 69218992780855657578074029)
      ·
        refine ⟨25957122292820871591777761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69218992780855657578074029 25957122292820871591777761)
        ·
          refine ⟨19467841719615653693833321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25957122292820871591777761 19467841719615653693833321)
          ·
            refine ⟨14600881289711740270374991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19467841719615653693833321 14600881289711740270374991)
            ·
              refine ⟨21901321934567610405562487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14600881289711740270374991 21901321934567610405562487)
              ·
                refine ⟨32851982901851415608343731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21901321934567610405562487 32851982901851415608343731)
                ·
                  refine ⟨49277974352777123412515597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32851982901851415608343731 49277974352777123412515597)
                  ·
                    refine ⟨18479240382291421279693349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49277974352777123412515597 18479240382291421279693349)
                    ·
                      refine ⟨3464857571679641489942503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18479240382291421279693349 3464857571679641489942503)
                      ·
                        rfl

theorem cell23_6747786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_6747786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6747786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6747786 prefixEnd_6747786 := by exact prefixLift 6747786
  have htrace : WordTrace (prefixWord ++ tailWord_6747786) baseStart_6747786 baseEnd_6747786 := by
    simpa [prefixWord, tailWord_6747786, baseEnd_6747786] using wordTrace_append hprefix tailTrace_6747786
  have hstable : (prefixWord ++ tailWord_6747786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6747786).length < 2 ^ (prefixWord ++ tailWord_6747786).sum := by decide
  have hdescent : baseEnd_6747786 < baseStart_6747786 := by decide
  rcases family_descends (prefixWord ++ tailWord_6747786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6747799 : List Nat := [1, 1, 3, 3, 2, 2, 1, 1, 2, 1, 6]
def baseStart_6747799 : Nat := 118140960795 + 6747799 * 2 ^ 59
def prefixEnd_6747799 : Nat := 4983230072969 + 3 ^ 40 * 6747799 * 2
def baseEnd_6747799 : Nat := 3464864246928149939079943

theorem tailTrace_6747799 : CollatzResearch.WordTrace tailWord_6747799 prefixEnd_6747799 3464864246928149939079943 := by
  unfold tailWord_6747799
  simp only [CollatzResearch.WordTrace]
  refine ⟨246112448480884130164486451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164074965653922753442990967 246112448480884130164486451)
  ·
    refine ⟨369168672721326195246729677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246112448480884130164486451 369168672721326195246729677)
    ·
      refine ⟨138438252270497323217523629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 369168672721326195246729677 138438252270497323217523629)
      ·
        refine ⟨51914344601436496206571361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138438252270497323217523629 51914344601436496206571361)
        ·
          refine ⟨38935758451077372154928521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51914344601436496206571361 38935758451077372154928521)
          ·
            refine ⟨29201818838308029116196391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38935758451077372154928521 29201818838308029116196391)
            ·
              refine ⟨43802728257462043674294587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29201818838308029116196391 43802728257462043674294587)
              ·
                refine ⟨65704092386193065511441881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43802728257462043674294587 65704092386193065511441881)
                ·
                  refine ⟨49278069289644799133581411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65704092386193065511441881 49278069289644799133581411)
                  ·
                    refine ⟨73917103934467198700372117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49278069289644799133581411 73917103934467198700372117)
                    ·
                      refine ⟨3464864246928149939079943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73917103934467198700372117 3464864246928149939079943)
                      ·
                        rfl

theorem cell23_6747799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 1, 2, 1, 6].length) (baseStart_6747799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6747799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6747799 prefixEnd_6747799 := by exact prefixLift 6747799
  have htrace : WordTrace (prefixWord ++ tailWord_6747799) baseStart_6747799 baseEnd_6747799 := by
    simpa [prefixWord, tailWord_6747799, baseEnd_6747799] using wordTrace_append hprefix tailTrace_6747799
  have hstable : (prefixWord ++ tailWord_6747799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6747799).length < 2 ^ (prefixWord ++ tailWord_6747799).sum := by decide
  have hdescent : baseEnd_6747799 < baseStart_6747799 := by decide
  rcases family_descends (prefixWord ++ tailWord_6747799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6747813 : List Nat := [1, 3, 1, 2, 1, 2, 4, 4, 1, 4]
def baseStart_6747813 : Nat := 118140960795 + 6747813 * 2 ^ 59
def prefixEnd_6747813 : Nat := 4983230072969 + 3 ^ 40 * 6747813 * 2
def baseEnd_6747813 : Nat := 1154957145219104294768293

theorem tailTrace_6747813 : CollatzResearch.WordTrace tailWord_6747813 prefixEnd_6747813 1154957145219104294768293 := by
  unfold tailWord_6747813
  simp only [CollatzResearch.WordTrace]
  refine ⟨246112959102833410555496093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164075306068555607036997395 246112959102833410555496093)
  ·
    refine ⟨92292359663562528958311035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 246112959102833410555496093 92292359663562528958311035)
    ·
      refine ⟨138438539495343793437466553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92292359663562528958311035 138438539495343793437466553)
      ·
        refine ⟨103828904621507845078099915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138438539495343793437466553 103828904621507845078099915)
        ·
          refine ⟨155743356932261767617149873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103828904621507845078099915 155743356932261767617149873)
          ·
            refine ⟨116807517699196325712862405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155743356932261767617149873 116807517699196325712862405)
            ·
              refine ⟨21901409568599311071161701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 116807517699196325712862405 21901409568599311071161701)
              ·
                refine ⟨4106514294112370825842819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21901409568599311071161701 4106514294112370825842819)
                ·
                  refine ⟨6159771441168556238764229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4106514294112370825842819 6159771441168556238764229)
                  ·
                    refine ⟨1154957145219104294768293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6159771441168556238764229 1154957145219104294768293)
                    ·
                      rfl

theorem cell23_6747813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 4, 1, 4].length) (baseStart_6747813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6747813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6747813 prefixEnd_6747813 := by exact prefixLift 6747813
  have htrace : WordTrace (prefixWord ++ tailWord_6747813) baseStart_6747813 baseEnd_6747813 := by
    simpa [prefixWord, tailWord_6747813, baseEnd_6747813] using wordTrace_append hprefix tailTrace_6747813
  have hstable : (prefixWord ++ tailWord_6747813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6747813).length < 2 ^ (prefixWord ++ tailWord_6747813).sum := by decide
  have hdescent : baseEnd_6747813 < baseStart_6747813 := by decide
  rcases family_descends (prefixWord ++ tailWord_6747813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6747830 : List Nat := [5, 1, 3, 1, 1, 1, 2, 2, 3, 4]
def baseStart_6747830 : Nat := 118140960795 + 6747830 * 2 ^ 59
def prefixEnd_6747830 : Nat := 4983230072969 + 3 ^ 40 * 6747830 * 2
def baseEnd_6747830 : Nat := 1154960054942813105930767

theorem tailTrace_6747830 : CollatzResearch.WordTrace tailWord_6747830 prefixEnd_6747830 1154960054942813105930767 := by
  unfold tailWord_6747830
  simp only [CollatzResearch.WordTrace]
  refine ⟨15382098696485738903679059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 164075719429181214972576629 15382098696485738903679059)
  ·
    refine ⟨23073148044728608355518589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15382098696485738903679059 23073148044728608355518589)
    ·
      refine ⟨8652430516773228133319471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23073148044728608355518589 8652430516773228133319471)
      ·
        refine ⟨12978645775159842199979207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8652430516773228133319471 12978645775159842199979207)
        ·
          refine ⟨19467968662739763299968811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12978645775159842199979207 19467968662739763299968811)
          ·
            refine ⟨29201952994109644949953217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19467968662739763299968811 29201952994109644949953217)
            ·
              refine ⟨21901464745582233712464913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29201952994109644949953217 21901464745582233712464913)
              ·
                refine ⟨16426098559186675284348685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21901464745582233712464913 16426098559186675284348685)
                ·
                  refine ⟨6159786959695003231630757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16426098559186675284348685 6159786959695003231630757)
                  ·
                    refine ⟨1154960054942813105930767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6159786959695003231630757 1154960054942813105930767)
                    ·
                      rfl

theorem cell23_6747830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_6747830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6747830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6747830 prefixEnd_6747830 := by exact prefixLift 6747830
  have htrace : WordTrace (prefixWord ++ tailWord_6747830) baseStart_6747830 baseEnd_6747830 := by
    simpa [prefixWord, tailWord_6747830, baseEnd_6747830] using wordTrace_append hprefix tailTrace_6747830
  have hstable : (prefixWord ++ tailWord_6747830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6747830).length < 2 ^ (prefixWord ++ tailWord_6747830).sum := by decide
  have hdescent : baseEnd_6747830 < baseStart_6747830 := by decide
  rcases family_descends (prefixWord ++ tailWord_6747830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6747863 : List Nat := [1, 1, 3, 2, 1, 3, 3, 2, 2, 3, 2]
def baseStart_6747863 : Nat := 118140960795 + 6747863 * 2 ^ 59
def prefixEnd_6747863 : Nat := 4983230072969 + 3 ^ 40 * 6747863 * 2
def baseEnd_6747863 : Nat := 3464897109690037688679649

theorem tailTrace_6747863 : CollatzResearch.WordTrace tailWord_6747863 prefixEnd_6747863 3464897109690037688679649 := by
  unfold tailWord_6747863
  simp only [CollatzResearch.WordTrace]
  refine ⟨246114782752652269094816243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164076521835101512729877495 246114782752652269094816243)
  ·
    refine ⟨369172174128978403642224365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246114782752652269094816243 369172174128978403642224365)
    ·
      refine ⟨138439565298366901365834137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 369172174128978403642224365 138439565298366901365834137)
      ·
        refine ⟨103829673973775176024375603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138439565298366901365834137 103829673973775176024375603)
        ·
          refine ⟨155744510960662764036563405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103829673973775176024375603 155744510960662764036563405)
          ·
            refine ⟨58404191610248536513711277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 155744510960662764036563405 58404191610248536513711277)
            ·
              refine ⟨21901571853843201192641729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58404191610248536513711277 21901571853843201192641729)
              ·
                refine ⟨16426178890382400894481297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21901571853843201192641729 16426178890382400894481297)
                ·
                  refine ⟨12319634167786800670860973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16426178890382400894481297 12319634167786800670860973)
                  ·
                    refine ⟨4619862812920050251572865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12319634167786800670860973 4619862812920050251572865)
                    ·
                      refine ⟨3464897109690037688679649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4619862812920050251572865 3464897109690037688679649)
                      ·
                        rfl

theorem cell23_6747863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 2, 2, 3, 2].length) (baseStart_6747863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6747863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6747863 prefixEnd_6747863 := by exact prefixLift 6747863
  have htrace : WordTrace (prefixWord ++ tailWord_6747863) baseStart_6747863 baseEnd_6747863 := by
    simpa [prefixWord, tailWord_6747863, baseEnd_6747863] using wordTrace_append hprefix tailTrace_6747863
  have hstable : (prefixWord ++ tailWord_6747863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6747863).length < 2 ^ (prefixWord ++ tailWord_6747863).sum := by decide
  have hdescent : baseEnd_6747863 < baseStart_6747863 := by decide
  rcases family_descends (prefixWord ++ tailWord_6747863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6747876 : List Nat := [2, 3, 1, 1, 1, 3, 2, 2, 3, 1, 4]
def baseStart_6747876 : Nat := 118140960795 + 6747876 * 2 ^ 59
def prefixEnd_6747876 : Nat := 4983230072969 + 3 ^ 40 * 6747876 * 2
def baseEnd_6747876 : Nat := 3464903784938546137817089

theorem tailTrace_6747876 : CollatzResearch.WordTrace tailWord_6747876 prefixEnd_6747876 3464903784938546137817089 := by
  unfold tailWord_6747876
  simp only [CollatzResearch.WordTrace]
  refine ⟨123057628450802586157519741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164076837934403448210026321 123057628450802586157519741)
  ·
    refine ⟨46146610669050969809069903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123057628450802586157519741 46146610669050969809069903)
    ·
      refine ⟨69219916003576454713604855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46146610669050969809069903 69219916003576454713604855)
      ·
        refine ⟨103829874005364682070407283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69219916003576454713604855 103829874005364682070407283)
        ·
          refine ⟨155744811008047023105610925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103829874005364682070407283 155744811008047023105610925)
          ·
            refine ⟨58404304128017633664604097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 155744811008047023105610925 58404304128017633664604097)
            ·
              refine ⟨43803228096013225248453073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58404304128017633664604097 43803228096013225248453073)
              ·
                refine ⟨32852421072009918936339805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43803228096013225248453073 32852421072009918936339805)
                ·
                  refine ⟨12319657902003719601127427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32852421072009918936339805 12319657902003719601127427)
                  ·
                    refine ⟨18479486853005579401691141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12319657902003719601127427 18479486853005579401691141)
                    ·
                      refine ⟨3464903784938546137817089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18479486853005579401691141 3464903784938546137817089)
                      ·
                        rfl

theorem cell23_6747876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 2, 3, 1, 4].length) (baseStart_6747876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6747876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6747876 prefixEnd_6747876 := by exact prefixLift 6747876
  have htrace : WordTrace (prefixWord ++ tailWord_6747876) baseStart_6747876 baseEnd_6747876 := by
    simpa [prefixWord, tailWord_6747876, baseEnd_6747876] using wordTrace_append hprefix tailTrace_6747876
  have hstable : (prefixWord ++ tailWord_6747876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6747876).length < 2 ^ (prefixWord ++ tailWord_6747876).sum := by decide
  have hdescent : baseEnd_6747876 < baseStart_6747876 := by decide
  rcases family_descends (prefixWord ++ tailWord_6747876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6747886 : List Nat := [4, 1, 2, 1, 1, 2, 2, 3, 1, 6]
def baseStart_6747886 : Nat := 118140960795 + 6747886 * 2 ^ 59
def prefixEnd_6747886 : Nat := 4983230072969 + 3 ^ 40 * 6747886 * 2
def baseEnd_6747886 : Nat := 1154969639915030366230681

theorem tailTrace_6747886 : CollatzResearch.WordTrace tailWord_6747886 prefixEnd_6747886 1154969639915030366230681 := by
  unfold tailWord_6747886
  simp only [CollatzResearch.WordTrace]
  refine ⟨30764452703946118002862939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164077081087712629348602341 30764452703946118002862939)
  ·
    refine ⟨46146679055919177004294409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30764452703946118002862939 46146679055919177004294409)
    ·
      refine ⟨34610009291939382753220807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46146679055919177004294409 34610009291939382753220807)
      ·
        refine ⟨51915013937909074129831211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34610009291939382753220807 51915013937909074129831211)
        ·
          refine ⟨77872520906863611194746817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51915013937909074129831211 77872520906863611194746817)
          ·
            refine ⟨58404390680147708396060113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77872520906863611194746817 58404390680147708396060113)
            ·
              refine ⟨43803293010110781297045085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58404390680147708396060113 43803293010110781297045085)
              ·
                refine ⟨16426234878791542986391907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43803293010110781297045085 16426234878791542986391907)
                ·
                  refine ⟨24639352318187314479587861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16426234878791542986391907 24639352318187314479587861)
                  ·
                    refine ⟨1154969639915030366230681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24639352318187314479587861 1154969639915030366230681)
                    ·
                      rfl

theorem cell23_6747886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 3, 1, 6].length) (baseStart_6747886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6747886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6747886 prefixEnd_6747886 := by exact prefixLift 6747886
  have htrace : WordTrace (prefixWord ++ tailWord_6747886) baseStart_6747886 baseEnd_6747886 := by
    simpa [prefixWord, tailWord_6747886, baseEnd_6747886] using wordTrace_append hprefix tailTrace_6747886
  have hstable : (prefixWord ++ tailWord_6747886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6747886).length < 2 ^ (prefixWord ++ tailWord_6747886).sum := by decide
  have hdescent : baseEnd_6747886 < baseStart_6747886 := by decide
  rcases family_descends (prefixWord ++ tailWord_6747886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6747919 : List Nat := [1, 1, 2, 1, 1, 1, 4, 2, 2, 2, 6]
def baseStart_6747919 : Nat := 118140960795 + 6747919 * 2 ^ 59
def prefixEnd_6747919 : Nat := 4983230072969 + 3 ^ 40 * 6747919 * 2
def baseEnd_6747919 : Nat := 3464925864606689469579391

theorem tailTrace_6747919 : CollatzResearch.WordTrace tailWord_6747919 prefixEnd_6747919 3464925864606689469579391 := by
  unfold tailWord_6747919
  simp only [CollatzResearch.WordTrace]
  refine ⟨246116825240449390658854811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164077883493632927105903207 246116825240449390658854811)
  ·
    refine ⟨369175237860674085988282217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246116825240449390658854811 369175237860674085988282217)
    ·
      refine ⟨276881428395505564491211663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 369175237860674085988282217 276881428395505564491211663)
      ·
        refine ⟨415322142593258346736817495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276881428395505564491211663 415322142593258346736817495)
        ·
          refine ⟨622983213889887520105226243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 415322142593258346736817495 622983213889887520105226243)
          ·
            refine ⟨934474820834831280157839365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 622983213889887520105226243 934474820834831280157839365)
            ·
              refine ⟨175214028906530865029594881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 934474820834831280157839365 175214028906530865029594881)
              ·
                refine ⟨131410521679898148772196161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 175214028906530865029594881 131410521679898148772196161)
                ·
                  refine ⟨98557891259923611579147121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 131410521679898148772196161 98557891259923611579147121)
                  ·
                    refine ⟨73918418444942708684360341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 98557891259923611579147121 73918418444942708684360341)
                    ·
                      refine ⟨3464925864606689469579391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73918418444942708684360341 3464925864606689469579391)
                      ·
                        rfl

theorem cell23_6747919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 2, 2, 6].length) (baseStart_6747919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6747919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6747919 prefixEnd_6747919 := by exact prefixLift 6747919
  have htrace : WordTrace (prefixWord ++ tailWord_6747919) baseStart_6747919 baseEnd_6747919 := by
    simpa [prefixWord, tailWord_6747919, baseEnd_6747919] using wordTrace_append hprefix tailTrace_6747919
  have hstable : (prefixWord ++ tailWord_6747919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6747919).length < 2 ^ (prefixWord ++ tailWord_6747919).sum := by decide
  have hdescent : baseEnd_6747919 < baseStart_6747919 := by decide
  rcases family_descends (prefixWord ++ tailWord_6747919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6747950 : List Nat := [4, 1, 3, 2, 2, 1, 3, 7]
def baseStart_6747950 : Nat := 118140960795 + 6747950 * 2 ^ 59
def prefixEnd_6747950 : Nat := 4983230072969 + 3 ^ 40 * 6747950 * 2
def baseEnd_6747950 : Nat := 128331177129888105492287

theorem tailTrace_6747950 : CollatzResearch.WordTrace tailWord_6747950 prefixEnd_6747950 128331177129888105492287 := by
  unfold tailWord_6747950
  simp only [CollatzResearch.WordTrace]
  refine ⟨30764744487917135369154163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164078637268891388635488869 30764744487917135369154163)
  ·
    refine ⟨46147116731875703053731245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30764744487917135369154163 46147116731875703053731245)
    ·
      refine ⟨17305168774453388645149217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46147116731875703053731245 17305168774453388645149217)
      ·
        refine ⟨12978876580840041483861913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17305168774453388645149217 12978876580840041483861913)
        ·
          refine ⟨9734157435630031112896435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12978876580840041483861913 9734157435630031112896435)
          ·
            refine ⟨14601236153445046669344653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9734157435630031112896435 14601236153445046669344653)
            ·
              refine ⟨5475463557541892501004245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14601236153445046669344653 5475463557541892501004245)
              ·
                refine ⟨128331177129888105492287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5475463557541892501004245 128331177129888105492287)
                ·
                  rfl

theorem cell23_6747950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 3, 7].length) (baseStart_6747950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6747950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6747950 prefixEnd_6747950 := by exact prefixLift 6747950
  have htrace : WordTrace (prefixWord ++ tailWord_6747950) baseStart_6747950 baseEnd_6747950 := by
    simpa [prefixWord, tailWord_6747950, baseEnd_6747950] using wordTrace_append hprefix tailTrace_6747950
  have hstable : (prefixWord ++ tailWord_6747950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6747950).length < 2 ^ (prefixWord ++ tailWord_6747950).sum := by decide
  have hdescent : baseEnd_6747950 < baseStart_6747950 := by decide
  rcases family_descends (prefixWord ++ tailWord_6747950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6747961 : List Nat := [1, 2, 1, 7, 1, 1, 2, 3, 1, 2, 2]
def baseStart_6747961 : Nat := 118140960795 + 6747961 * 2 ^ 59
def prefixEnd_6747961 : Nat := 4983230072969 + 3 ^ 40 * 6747961 * 2
def baseEnd_6747961 : Nat := 3464947430794178305254199

theorem tailTrace_6747961 : CollatzResearch.WordTrace tailWord_6747961 prefixEnd_6747961 3464947430794178305254199 := by
  unfold tailWord_6747961
  simp only [CollatzResearch.WordTrace]
  refine ⟨246118357106297231831883737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164078904737531487887922491 246118357106297231831883737)
  ·
    refine ⟨184588767829722923873912803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246118357106297231831883737 184588767829722923873912803)
    ·
      refine ⟨276883151744584385810869205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184588767829722923873912803 276883151744584385810869205)
      ·
        refine ⟨6489448869013696542442247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 276883151744584385810869205 6489448869013696542442247)
        ·
          refine ⟨9734173303520544813663371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6489448869013696542442247 9734173303520544813663371)
          ·
            refine ⟨14601259955280817220495057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9734173303520544813663371 14601259955280817220495057)
            ·
              refine ⟨10950944966460612915371293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14601259955280817220495057 10950944966460612915371293)
              ·
                refine ⟨4106604362422729843264235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10950944966460612915371293 4106604362422729843264235)
                ·
                  refine ⟨6159906543634094764896353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4106604362422729843264235 6159906543634094764896353)
                  ·
                    refine ⟨4619929907725571073672265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6159906543634094764896353 4619929907725571073672265)
                    ·
                      refine ⟨3464947430794178305254199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4619929907725571073672265 3464947430794178305254199)
                      ·
                        rfl

theorem cell23_6747961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_6747961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6747961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6747961 prefixEnd_6747961 := by exact prefixLift 6747961
  have htrace : WordTrace (prefixWord ++ tailWord_6747961) baseStart_6747961 baseEnd_6747961 := by
    simpa [prefixWord, tailWord_6747961, baseEnd_6747961] using wordTrace_append hprefix tailTrace_6747961
  have hstable : (prefixWord ++ tailWord_6747961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6747961).length < 2 ^ (prefixWord ++ tailWord_6747961).sum := by decide
  have hdescent : baseEnd_6747961 < baseStart_6747961 := by decide
  rcases family_descends (prefixWord ++ tailWord_6747961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6747976 : List Nat := [2, 1, 3, 1, 1, 4, 1, 2, 2, 6]
def baseStart_6747976 : Nat := 118140960795 + 6747976 * 2 ^ 59
def prefixEnd_6747976 : Nat := 4983230072969 + 3 ^ 40 * 6747976 * 2
def baseEnd_6747976 : Nat := 1154985044334665248855543

theorem tailTrace_6747976 : CollatzResearch.WordTrace tailWord_6747976 prefixEnd_6747976 1154985044334665248855543 := by
  unfold tailWord_6747976
  simp only [CollatzResearch.WordTrace]
  refine ⟨123059452100621444696839891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164079269467495259595786521 123059452100621444696839891)
  ·
    refine ⟨184589178150932167045259837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123059452100621444696839891 184589178150932167045259837)
    ·
      refine ⟨69220941806599562641972439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184589178150932167045259837 69220941806599562641972439)
      ·
        refine ⟨103831412709899343962958659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69220941806599562641972439 103831412709899343962958659)
        ·
          refine ⟨155747119064849015944437989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103831412709899343962958659 155747119064849015944437989)
          ·
            refine ⟨29202584824659190489582123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 155747119064849015944437989 29202584824659190489582123)
            ·
              refine ⟨43803877236988785734373185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29202584824659190489582123 43803877236988785734373185)
              ·
                refine ⟨32852907927741589300779889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43803877236988785734373185 32852907927741589300779889)
                ·
                  refine ⟨24639680945806191975584917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32852907927741589300779889 24639680945806191975584917)
                  ·
                    refine ⟨1154985044334665248855543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24639680945806191975584917 1154985044334665248855543)
                    ·
                      rfl

theorem cell23_6747976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 2, 2, 6].length) (baseStart_6747976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6747976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6747976 prefixEnd_6747976 := by exact prefixLift 6747976
  have htrace : WordTrace (prefixWord ++ tailWord_6747976) baseStart_6747976 baseEnd_6747976 := by
    simpa [prefixWord, tailWord_6747976, baseEnd_6747976] using wordTrace_append hprefix tailTrace_6747976
  have hstable : (prefixWord ++ tailWord_6747976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6747976).length < 2 ^ (prefixWord ++ tailWord_6747976).sum := by decide
  have hdescent : baseEnd_6747976 < baseStart_6747976 := by decide
  rcases family_descends (prefixWord ++ tailWord_6747976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6748000 : List Nat := [2, 1, 1, 3, 3, 2, 3, 1, 1, 4, 2]
def baseStart_6748000 : Nat := 118140960795 + 6748000 * 2 ^ 59
def prefixEnd_6748000 : Nat := 4983230072969 + 3 ^ 40 * 6748000 * 2
def baseEnd_6748000 : Nat := 3464967456539703652666519

theorem tailTrace_6748000 : CollatzResearch.WordTrace tailWord_6748000 prefixEnd_6748000 3464967456539703652666519 := by
  unfold tailWord_6748000
  simp only [CollatzResearch.WordTrace]
  refine ⟨123059889776577970746276727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164079853035437294328368969 123059889776577970746276727)
  ·
    refine ⟨184589834664866956119415091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123059889776577970746276727 184589834664866956119415091)
    ·
      refine ⟨276884751997300434179122637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184589834664866956119415091 276884751997300434179122637)
      ·
        refine ⟨103831781998987662817170989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 276884751997300434179122637 103831781998987662817170989)
        ·
          refine ⟨38936918249620373556439121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103831781998987662817170989 38936918249620373556439121)
          ·
            refine ⟨29202688687215280167329341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38936918249620373556439121 29202688687215280167329341)
            ·
              refine ⟨10951008257705730062748503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29202688687215280167329341 10951008257705730062748503)
              ·
                refine ⟨16426512386558595094122755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10951008257705730062748503 16426512386558595094122755)
                ·
                  refine ⟨24639768579837892641184133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16426512386558595094122755 24639768579837892641184133)
                  ·
                    refine ⟨4619956608719604870222025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24639768579837892641184133 4619956608719604870222025)
                    ·
                      refine ⟨3464967456539703652666519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4619956608719604870222025 3464967456539703652666519)
                      ·
                        rfl

theorem cell23_6748000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 1, 1, 4, 2].length) (baseStart_6748000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6748000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6748000 prefixEnd_6748000 := by exact prefixLift 6748000
  have htrace : WordTrace (prefixWord ++ tailWord_6748000) baseStart_6748000 baseEnd_6748000 := by
    simpa [prefixWord, tailWord_6748000, baseEnd_6748000] using wordTrace_append hprefix tailTrace_6748000
  have hstable : (prefixWord ++ tailWord_6748000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6748000).length < 2 ^ (prefixWord ++ tailWord_6748000).sum := by decide
  have hdescent : baseEnd_6748000 < baseStart_6748000 := by decide
  rcases family_descends (prefixWord ++ tailWord_6748000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6748040 : List Nat := [2, 1, 3, 3, 3, 2, 1, 1, 7]
def baseStart_6748040 : Nat := 118140960795 + 6748040 * 2 ^ 59
def prefixEnd_6748040 : Nat := 4983230072969 + 3 ^ 40 * 6748040 * 2
def baseEnd_6748040 : Nat := 384998666196209277351815

theorem tailTrace_6748040 : CollatzResearch.WordTrace tailWord_6748040 prefixEnd_6748040 384998666196209277351815 := by
  unfold tailWord_6748040
  simp only [CollatzResearch.WordTrace]
  refine ⟨123060619236505514162004787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164080825648674018882673049 123060619236505514162004787)
  ·
    refine ⟨184590928854758271243007181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123060619236505514162004787 184590928854758271243007181)
    ·
      refine ⟨69221598320534351716127693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184590928854758271243007181 69221598320534351716127693)
      ·
        refine ⟨25958099370200381893547885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69221598320534351716127693 25958099370200381893547885)
        ·
          refine ⟨9734287263825143210080457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25958099370200381893547885 9734287263825143210080457)
          ·
            refine ⟨7300715447868857407560343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9734287263825143210080457 7300715447868857407560343)
            ·
              refine ⟨10951073171803286111340515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7300715447868857407560343 10951073171803286111340515)
              ·
                refine ⟨16426609757704929167010773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10951073171803286111340515 16426609757704929167010773)
                ·
                  refine ⟨384998666196209277351815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16426609757704929167010773 384998666196209277351815)
                  ·
                    rfl

theorem cell23_6748040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 1, 7].length) (baseStart_6748040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6748040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6748040 prefixEnd_6748040 := by exact prefixLift 6748040
  have htrace : WordTrace (prefixWord ++ tailWord_6748040) baseStart_6748040 baseEnd_6748040 := by
    simpa [prefixWord, tailWord_6748040, baseEnd_6748040] using wordTrace_append hprefix tailTrace_6748040
  have hstable : (prefixWord ++ tailWord_6748040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6748040).length < 2 ^ (prefixWord ++ tailWord_6748040).sum := by decide
  have hdescent : baseEnd_6748040 < baseStart_6748040 := by decide
  rcases family_descends (prefixWord ++ tailWord_6748040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6748043 : List Nat := [1, 1, 1, 1, 4, 2, 1, 3, 2, 5, 2]
def baseStart_6748043 : Nat := 118140960795 + 6748043 * 2 ^ 59
def prefixEnd_6748043 : Nat := 4983230072969 + 3 ^ 40 * 6748043 * 2
def baseEnd_6748043 : Nat := 3464989536207846984428821

theorem tailTrace_6748043 : CollatzResearch.WordTrace tailWord_6748043 prefixEnd_6748043 3464989536207846984428821 := by
  unfold tailWord_6748043
  simp only [CollatzResearch.WordTrace]
  refine ⟨246121347892000159836368783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164080898594666773224245855 246121347892000159836368783)
  ·
    refine ⟨369182021838000239754553175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246121347892000159836368783 369182021838000239754553175)
    ·
      refine ⟨553773032757000359631829763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369182021838000239754553175 553773032757000359631829763)
      ·
        refine ⟨830659549135500539447744645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 553773032757000359631829763 830659549135500539447744645)
        ·
          refine ⟨155748665462906351146452121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 830659549135500539447744645 155748665462906351146452121)
          ·
            refine ⟨116811499097179763359839091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155748665462906351146452121 116811499097179763359839091)
            ·
              refine ⟨175217248645769645039758637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116811499097179763359839091 175217248645769645039758637)
              ·
                refine ⟨65706468242163616889909489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 175217248645769645039758637 65706468242163616889909489)
                ·
                  refine ⟨49279851181622712667432117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65706468242163616889909489 49279851181622712667432117)
                  ·
                    refine ⟨4619986048277129312571761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49279851181622712667432117 4619986048277129312571761)
                    ·
                      refine ⟨3464989536207846984428821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4619986048277129312571761 3464989536207846984428821)
                      ·
                        rfl

theorem cell23_6748043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 3, 2, 5, 2].length) (baseStart_6748043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6748043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6748043 prefixEnd_6748043 := by exact prefixLift 6748043
  have htrace : WordTrace (prefixWord ++ tailWord_6748043) baseStart_6748043 baseEnd_6748043 := by
    simpa [prefixWord, tailWord_6748043, baseEnd_6748043] using wordTrace_append hprefix tailTrace_6748043
  have hstable : (prefixWord ++ tailWord_6748043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6748043).length < 2 ^ (prefixWord ++ tailWord_6748043).sum := by decide
  have hdescent : baseEnd_6748043 < baseStart_6748043 := by decide
  rcases family_descends (prefixWord ++ tailWord_6748043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6748073 : List Nat := [1, 2, 1, 1, 1, 1, 4, 1, 3, 6, 2]
def baseStart_6748073 : Nat := 118140960795 + 6748073 * 2 ^ 59
def prefixEnd_6748073 : Nat := 4983230072969 + 3 ^ 40 * 6748073 * 2
def baseEnd_6748073 : Nat := 3465004940627481867053683

theorem tailTrace_6748073 : CollatzResearch.WordTrace tailWord_6748073 prefixEnd_6748073 3465004940627481867053683 := by
  unfold tailWord_6748073
  simp only [CollatzResearch.WordTrace]
  refine ⟨246122442081891474959960873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164081628054594316639973915 246122442081891474959960873)
  ·
    refine ⟨184591831561418606219970655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246122442081891474959960873 184591831561418606219970655)
    ·
      refine ⟨276887747342127909329955983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184591831561418606219970655 276887747342127909329955983)
      ·
        refine ⟨415331621013191863994933975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276887747342127909329955983 415331621013191863994933975)
        ·
          refine ⟨622997431519787795992400963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 415331621013191863994933975 622997431519787795992400963)
          ·
            refine ⟨934496147279681693988601445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 622997431519787795992400963 934496147279681693988601445)
            ·
              refine ⟨175218027614940317622862771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 934496147279681693988601445 175218027614940317622862771)
              ·
                refine ⟨262827041422410476434294157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 175218027614940317622862771 262827041422410476434294157)
                ·
                  refine ⟨98560140533403928662860309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 262827041422410476434294157 98560140533403928662860309)
                  ·
                    refine ⟨4620006587503309156071577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 98560140533403928662860309 4620006587503309156071577)
                    ·
                      refine ⟨3465004940627481867053683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4620006587503309156071577 3465004940627481867053683)
                      ·
                        rfl

theorem cell23_6748073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 3, 6, 2].length) (baseStart_6748073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6748073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6748073 prefixEnd_6748073 := by exact prefixLift 6748073
  have htrace : WordTrace (prefixWord ++ tailWord_6748073) baseStart_6748073 baseEnd_6748073 := by
    simpa [prefixWord, tailWord_6748073, baseEnd_6748073] using wordTrace_append hprefix tailTrace_6748073
  have hstable : (prefixWord ++ tailWord_6748073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6748073).length < 2 ^ (prefixWord ++ tailWord_6748073).sum := by decide
  have hdescent : baseEnd_6748073 < baseStart_6748073 := by decide
  rcases family_descends (prefixWord ++ tailWord_6748073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6748076 : List Nat := [2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 5]
def baseStart_6748076 : Nat := 118140960795 + 6748076 * 2 ^ 59
def prefixEnd_6748076 : Nat := 4983230072969 + 3 ^ 40 * 6748076 * 2
def baseEnd_6748076 : Nat := 3465006481069445355316169

theorem tailTrace_6748076 : CollatzResearch.WordTrace tailWord_6748076 prefixEnd_6748076 3465006481069445355316169 := by
  unfold tailWord_6748076
  simp only [CollatzResearch.WordTrace]
  refine ⟨123061275750440303236160041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164081701000587070981546721 123061275750440303236160041)
  ·
    refine ⟨92295956812830227427120031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123061275750440303236160041 92295956812830227427120031)
    ·
      refine ⟨138443935219245341140680047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92295956812830227427120031 138443935219245341140680047)
      ·
        refine ⟨207665902828868011711020071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138443935219245341140680047 207665902828868011711020071)
        ·
          refine ⟨311498854243302017566530107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207665902828868011711020071 311498854243302017566530107)
          ·
            refine ⟨467248281364953026349795161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 311498854243302017566530107 467248281364953026349795161)
            ·
              refine ⟨350436211023714769762346371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 467248281364953026349795161 350436211023714769762346371)
              ·
                refine ⟨525654316535572154643519557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 350436211023714769762346371 525654316535572154643519557)
                ·
                  refine ⟨98560184350419778995659917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 525654316535572154643519557 98560184350419778995659917)
                  ·
                    refine ⟨36960069131407417123372469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 98560184350419778995659917 36960069131407417123372469)
                    ·
                      refine ⟨3465006481069445355316169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36960069131407417123372469 3465006481069445355316169)
                      ·
                        rfl

theorem cell23_6748076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 5].length) (baseStart_6748076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6748076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6748076 prefixEnd_6748076 := by exact prefixLift 6748076
  have htrace : WordTrace (prefixWord ++ tailWord_6748076) baseStart_6748076 baseEnd_6748076 := by
    simpa [prefixWord, tailWord_6748076, baseEnd_6748076] using wordTrace_append hprefix tailTrace_6748076
  have hstable : (prefixWord ++ tailWord_6748076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6748076).length < 2 ^ (prefixWord ++ tailWord_6748076).sum := by decide
  have hdescent : baseEnd_6748076 < baseStart_6748076 := by decide
  rcases family_descends (prefixWord ++ tailWord_6748076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6748124 : List Nat := [2, 2, 6, 1, 1, 1, 1, 1, 1, 3, 4]
def baseStart_6748124 : Nat := 118140960795 + 6748124 * 2 ^ 59
def prefixEnd_6748124 : Nat := 4983230072969 + 3 ^ 40 * 6748124 * 2
def baseEnd_6748124 : Nat := 3465031128140861167515949

theorem tailTrace_6748124 : CollatzResearch.WordTrace tailWord_6748124 prefixEnd_6748124 3465031128140861167515949 := by
  unfold tailWord_6748124
  simp only [CollatzResearch.WordTrace]
  refine ⟨123062151102353355335033713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164082868136471140446711617 123062151102353355335033713)
  ·
    refine ⟨92296613326765016501275285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123062151102353355335033713 92296613326765016501275285)
    ·
      refine ⟨4326403749692110148497279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 92296613326765016501275285 4326403749692110148497279)
      ·
        refine ⟨6489605624538165222745919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4326403749692110148497279 6489605624538165222745919)
        ·
          refine ⟨9734408436807247834118879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6489605624538165222745919 9734408436807247834118879)
          ·
            refine ⟨14601612655210871751178319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9734408436807247834118879 14601612655210871751178319)
            ·
              refine ⟨21902418982816307626767479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14601612655210871751178319 21902418982816307626767479)
              ·
                refine ⟨32853628474224461440151219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21902418982816307626767479 32853628474224461440151219)
                ·
                  refine ⟨49280442711336692160226829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32853628474224461440151219 49280442711336692160226829)
                  ·
                    refine ⟨18480166016751259560085061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49280442711336692160226829 18480166016751259560085061)
                    ·
                      refine ⟨3465031128140861167515949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18480166016751259560085061 3465031128140861167515949)
                      ·
                        rfl

theorem cell23_6748124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_6748124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6748124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6748124 prefixEnd_6748124 := by exact prefixLift 6748124
  have htrace : WordTrace (prefixWord ++ tailWord_6748124) baseStart_6748124 baseEnd_6748124 := by
    simpa [prefixWord, tailWord_6748124, baseEnd_6748124] using wordTrace_append hprefix tailTrace_6748124
  have hstable : (prefixWord ++ tailWord_6748124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6748124).length < 2 ^ (prefixWord ++ tailWord_6748124).sum := by decide
  have hdescent : baseEnd_6748124 < baseStart_6748124 := by decide
  rcases family_descends (prefixWord ++ tailWord_6748124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6748127 : List Nat := [1, 1, 2, 3, 4, 3, 1, 1, 2, 2, 3]
def baseStart_6748127 : Nat := 118140960795 + 6748127 * 2 ^ 59
def prefixEnd_6748127 : Nat := 4983230072969 + 3 ^ 40 * 6748127 * 2
def baseEnd_6748127 : Nat := 3465032668582824655778435

theorem tailTrace_6748127 : CollatzResearch.WordTrace tailWord_6748127 prefixEnd_6748127 3465032668582824655778435 := by
  unfold tailWord_6748127
  simp only [CollatzResearch.WordTrace]
  refine ⟨246124411623695842182426635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164082941082463894788284423 246124411623695842182426635)
  ·
    refine ⟨369186617435543763273639953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246124411623695842182426635 369186617435543763273639953)
    ·
      refine ⟨276889963076657822455229965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 369186617435543763273639953 276889963076657822455229965)
      ·
        refine ⟨103833736153746683420711237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 276889963076657822455229965 103833736153746683420711237)
        ·
          refine ⟨19468825528827503141383357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103833736153746683420711237 19468825528827503141383357)
          ·
            refine ⟨7300809573310313678018759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19468825528827503141383357 7300809573310313678018759)
            ·
              refine ⟨10951214359965470517028139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7300809573310313678018759 10951214359965470517028139)
              ·
                refine ⟨16426821539948205775542209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10951214359965470517028139 16426821539948205775542209)
                ·
                  refine ⟨12320116154961154331656657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16426821539948205775542209 12320116154961154331656657)
                  ·
                    refine ⟨9240087116220865748742493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12320116154961154331656657 9240087116220865748742493)
                    ·
                      refine ⟨3465032668582824655778435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9240087116220865748742493 3465032668582824655778435)
                      ·
                        rfl

theorem cell23_6748127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 1, 2, 2, 3].length) (baseStart_6748127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6748127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6748127 prefixEnd_6748127 := by exact prefixLift 6748127
  have htrace : WordTrace (prefixWord ++ tailWord_6748127) baseStart_6748127 baseEnd_6748127 := by
    simpa [prefixWord, tailWord_6748127, baseEnd_6748127] using wordTrace_append hprefix tailTrace_6748127
  have hstable : (prefixWord ++ tailWord_6748127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6748127).length < 2 ^ (prefixWord ++ tailWord_6748127).sum := by decide
  have hdescent : baseEnd_6748127 < baseStart_6748127 := by decide
  rcases family_descends (prefixWord ++ tailWord_6748127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6748163 : List Nat := [1, 1, 1, 3, 2, 1, 1, 3, 5, 1, 4]
def baseStart_6748163 : Nat := 118140960795 + 6748163 * 2 ^ 59
def prefixEnd_6748163 : Nat := 4983230072969 + 3 ^ 40 * 6748163 * 2
def baseEnd_6748163 : Nat := 3465051153886386514928269

theorem tailTrace_6748163 : CollatzResearch.WordTrace tailWord_6748163 prefixEnd_6748163 3465051153886386514928269 := by
  unfold tailWord_6748163
  simp only [CollatzResearch.WordTrace]
  refine ⟨246125724651565420330737143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164083816434376946887158095 246125724651565420330737143)
  ·
    refine ⟨369188586977348130496105715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246125724651565420330737143 369188586977348130496105715)
    ·
      refine ⟨553782880466022195744158573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369188586977348130496105715 553782880466022195744158573)
      ·
        refine ⟨207668580174758323404059465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 553782880466022195744158573 207668580174758323404059465)
        ·
          refine ⟨155751435131068742553044599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207668580174758323404059465 155751435131068742553044599)
          ·
            refine ⟨233627152696603113829566899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155751435131068742553044599 233627152696603113829566899)
            ·
              refine ⟨350440729044904670744350349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 233627152696603113829566899 350440729044904670744350349)
              ·
                refine ⟨131415273391839251529131381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 350440729044904670744350349 131415273391839251529131381)
                ·
                  refine ⟨12320181880484929830856067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 131415273391839251529131381 12320181880484929830856067)
                  ·
                    refine ⟨18480272820727394746284101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12320181880484929830856067 18480272820727394746284101)
                    ·
                      refine ⟨3465051153886386514928269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18480272820727394746284101 3465051153886386514928269)
                      ·
                        rfl

theorem cell23_6748163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 5, 1, 4].length) (baseStart_6748163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6748163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6748163 prefixEnd_6748163 := by exact prefixLift 6748163
  have htrace : WordTrace (prefixWord ++ tailWord_6748163) baseStart_6748163 baseEnd_6748163 := by
    simpa [prefixWord, tailWord_6748163, baseEnd_6748163] using wordTrace_append hprefix tailTrace_6748163
  have hstable : (prefixWord ++ tailWord_6748163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6748163).length < 2 ^ (prefixWord ++ tailWord_6748163).sum := by decide
  have hdescent : baseEnd_6748163 < baseStart_6748163 := by decide
  rcases family_descends (prefixWord ++ tailWord_6748163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6748164 : List Nat := [2, 3, 2, 4, 1, 1, 3, 1, 6]
def baseStart_6748164 : Nat := 118140960795 + 6748164 * 2 ^ 59
def prefixEnd_6748164 : Nat := 4983230072969 + 3 ^ 40 * 6748164 * 2
def baseEnd_6748164 : Nat := 385005740818560112335085

theorem tailTrace_6748164 : CollatzResearch.WordTrace tailWord_6748164 prefixEnd_6748164 385005740818560112335085 := by
  unfold tailWord_6748164
  simp only [CollatzResearch.WordTrace]
  refine ⟨123062880562280898750761773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164083840749707865001015697 123062880562280898750761773)
  ·
    refine ⟨46148580210855337031535665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123062880562280898750761773 46148580210855337031535665)
    ·
      refine ⟨34611435158141502773651749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46148580210855337031535665 34611435158141502773651749)
      ·
        refine ⟨6489644092151531770059703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34611435158141502773651749 6489644092151531770059703)
        ·
          refine ⟨9734466138227297655089555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6489644092151531770059703 9734466138227297655089555)
          ·
            refine ⟨14601699207340946482634333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9734466138227297655089555 14601699207340946482634333)
            ·
              refine ⟨5475637202752854930987875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14601699207340946482634333 5475637202752854930987875)
              ·
                refine ⟨8213455804129282396481813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5475637202752854930987875 8213455804129282396481813)
                ·
                  refine ⟨385005740818560112335085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8213455804129282396481813 385005740818560112335085)
                  ·
                    rfl

theorem cell23_6748164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 3, 1, 6].length) (baseStart_6748164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6748164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6748164 prefixEnd_6748164 := by exact prefixLift 6748164
  have htrace : WordTrace (prefixWord ++ tailWord_6748164) baseStart_6748164 baseEnd_6748164 := by
    simpa [prefixWord, tailWord_6748164, baseEnd_6748164] using wordTrace_append hprefix tailTrace_6748164
  have hstable : (prefixWord ++ tailWord_6748164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6748164).length < 2 ^ (prefixWord ++ tailWord_6748164).sum := by decide
  have hdescent : baseEnd_6748164 < baseStart_6748164 := by decide
  rcases family_descends (prefixWord ++ tailWord_6748164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6748224 : List Nat := [2, 1, 1, 2, 2, 6, 2, 1, 2, 4]
def baseStart_6748224 : Nat := 118140960795 + 6748224 * 2 ^ 59
def prefixEnd_6748224 : Nat := 4983230072969 + 3 ^ 40 * 6748224 * 2
def baseEnd_6748224 : Nat := 1155027492068770258755163

theorem tailTrace_6748224 : CollatzResearch.WordTrace tailWord_6748224 prefixEnd_6748224 1155027492068770258755163 := by
  unfold tailWord_6748224
  simp only [CollatzResearch.WordTrace]
  refine ⟨123063974752172213874353863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164085299669562951832471817 123063974752172213874353863)
  ·
    refine ⟨184595962128258320811530795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123063974752172213874353863 184595962128258320811530795)
    ·
      refine ⟨276893943192387481217296193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184595962128258320811530795 276893943192387481217296193)
      ·
        refine ⟨207670457394290610912972145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 276893943192387481217296193 207670457394290610912972145)
        ·
          refine ⟨155752843045717958184729109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207670457394290610912972145 155752843045717958184729109)
          ·
            refine ⟨7300914517768029289909177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 155752843045717958184729109 7300914517768029289909177)
            ·
              refine ⟨5475685888326021967431883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7300914517768029289909177 5475685888326021967431883)
              ·
                refine ⟨8213528832489032951147825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5475685888326021967431883 8213528832489032951147825)
                ·
                  refine ⟨6160146624366774713360869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8213528832489032951147825 6160146624366774713360869)
                  ·
                    refine ⟨1155027492068770258755163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6160146624366774713360869 1155027492068770258755163)
                    ·
                      rfl

theorem cell23_6748224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 2, 1, 2, 4].length) (baseStart_6748224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6748224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6748224 prefixEnd_6748224 := by exact prefixLift 6748224
  have htrace : WordTrace (prefixWord ++ tailWord_6748224) baseStart_6748224 baseEnd_6748224 := by
    simpa [prefixWord, tailWord_6748224, baseEnd_6748224] using wordTrace_append hprefix tailTrace_6748224
  have hstable : (prefixWord ++ tailWord_6748224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6748224).length < 2 ^ (prefixWord ++ tailWord_6748224).sum := by decide
  have hdescent : baseEnd_6748224 < baseStart_6748224 := by decide
  rcases family_descends (prefixWord ++ tailWord_6748224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6748254 : List Nat := [4, 4, 1, 1, 3, 10]
def baseStart_6748254 : Nat := 118140960795 + 6748254 * 2 ^ 59
def prefixEnd_6748254 : Nat := 4983230072969 + 3 ^ 40 * 6748254 * 2
def baseEnd_6748254 : Nat := 14259662060189076785557

theorem tailTrace_6748254 : CollatzResearch.WordTrace tailWord_6748254 prefixEnd_6748254 14259662060189076785557 := by
  unfold tailWord_6748254
  simp only [CollatzResearch.WordTrace]
  refine ⟨30766130461779467859037477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164086029129490495248199877 30766130461779467859037477)
  ·
    refine ⟨5768649461583650223569527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30766130461779467859037477 5768649461583650223569527)
    ·
      refine ⟨8652974192375475335354291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5768649461583650223569527 8652974192375475335354291)
      ·
        refine ⟨12979461288563213003031437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8652974192375475335354291 12979461288563213003031437)
        ·
          refine ⟨4867297983211204876136789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12979461288563213003031437 4867297983211204876136789)
          ·
            refine ⟨14259662060189076785557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4867297983211204876136789 14259662060189076785557)
            ·
              rfl

theorem cell23_6748254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 10].length) (baseStart_6748254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6748254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6748254 prefixEnd_6748254 := by exact prefixLift 6748254
  have htrace : WordTrace (prefixWord ++ tailWord_6748254) baseStart_6748254 baseEnd_6748254 := by
    simpa [prefixWord, tailWord_6748254, baseEnd_6748254] using wordTrace_append hprefix tailTrace_6748254
  have hstable : (prefixWord ++ tailWord_6748254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6748254).length < 2 ^ (prefixWord ++ tailWord_6748254).sum := by decide
  have hdescent : baseEnd_6748254 < baseStart_6748254 := by decide
  rcases family_descends (prefixWord ++ tailWord_6748254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6748270 : List Nat := [4, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4]
def baseStart_6748270 : Nat := 118140960795 + 6748270 * 2 ^ 59
def prefixEnd_6748270 : Nat := 4983230072969 + 3 ^ 40 * 6748270 * 2
def baseEnd_6748270 : Nat := 3465106096316417596290277

theorem tailTrace_6748270 : CollatzResearch.WordTrace tailWord_6748270 prefixEnd_6748270 3465106096316417596290277 := by
  unfold tailWord_6748270
  simp only [CollatzResearch.WordTrace]
  refine ⟨30766203407772222200610283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164086418174785185069921509 30766203407772222200610283)
  ·
    refine ⟨46149305111658333300915425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30766203407772222200610283 46149305111658333300915425)
    ·
      refine ⟨34611978833743749975686569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46149305111658333300915425 34611978833743749975686569)
      ·
        refine ⟨25958984125307812481764927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34611978833743749975686569 25958984125307812481764927)
        ·
          refine ⟨38938476187961718722647391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25958984125307812481764927 38938476187961718722647391)
          ·
            refine ⟨58407714281942578083971087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38938476187961718722647391 58407714281942578083971087)
            ·
              refine ⟨87611571422913867125956631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58407714281942578083971087 87611571422913867125956631)
              ·
                refine ⟨131417357134370800688934947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87611571422913867125956631 131417357134370800688934947)
                ·
                  refine ⟨197126035701556201033402421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 131417357134370800688934947 197126035701556201033402421)
                  ·
                    refine ⟨18480565847020893846881477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 197126035701556201033402421 18480565847020893846881477)
                    ·
                      refine ⟨3465106096316417596290277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18480565847020893846881477 3465106096316417596290277)
                      ·
                        rfl

theorem cell23_6748270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_6748270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6748270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6748270 prefixEnd_6748270 := by exact prefixLift 6748270
  have htrace : WordTrace (prefixWord ++ tailWord_6748270) baseStart_6748270 baseEnd_6748270 := by
    simpa [prefixWord, tailWord_6748270, baseEnd_6748270] using wordTrace_append hprefix tailTrace_6748270
  have hstable : (prefixWord ++ tailWord_6748270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6748270).length < 2 ^ (prefixWord ++ tailWord_6748270).sum := by decide
  have hdescent : baseEnd_6748270 < baseStart_6748270 := by decide
  rcases family_descends (prefixWord ++ tailWord_6748270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6748308 : List Nat := [2, 4, 2, 3, 1, 1, 1, 3, 1, 3, 2]
def baseStart_6748308 : Nat := 118140960795 + 6748308 * 2 ^ 59
def prefixEnd_6748308 : Nat := 4983230072969 + 3 ^ 40 * 6748308 * 2
def baseEnd_6748308 : Nat := 3465125608581288447615103

theorem tailTrace_6748308 : CollatzResearch.WordTrace tailWord_6748308 prefixEnd_6748308 3465125608581288447615103 := by
  unfold tailWord_6748308
  simp only [CollatzResearch.WordTrace]
  refine ⟨123065506618020055047382789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164087342157360073396510385 123065506618020055047382789)
  ·
    refine ⟨23074782490878760321384273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123065506618020055047382789 23074782490878760321384273)
    ·
      refine ⟨17306086868159070241038205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23074782490878760321384273 17306086868159070241038205)
      ·
        refine ⟨6489782575559651340389327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17306086868159070241038205 6489782575559651340389327)
        ·
          refine ⟨9734673863339477010583991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6489782575559651340389327 9734673863339477010583991)
          ·
            refine ⟨14602010795009215515875987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9734673863339477010583991 14602010795009215515875987)
            ·
              refine ⟨21903016192513823273813981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14602010795009215515875987 21903016192513823273813981)
              ·
                refine ⟨8213631072192683727680243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21903016192513823273813981 8213631072192683727680243)
                ·
                  refine ⟨12320446608289025591520365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8213631072192683727680243 12320446608289025591520365)
                  ·
                    refine ⟨4620167478108384596820137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12320446608289025591520365 4620167478108384596820137)
                    ·
                      refine ⟨3465125608581288447615103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4620167478108384596820137 3465125608581288447615103)
                      ·
                        rfl

theorem cell23_6748308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_6748308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6748308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6748308 prefixEnd_6748308 := by exact prefixLift 6748308
  have htrace : WordTrace (prefixWord ++ tailWord_6748308) baseStart_6748308 baseEnd_6748308 := by
    simpa [prefixWord, tailWord_6748308, baseEnd_6748308] using wordTrace_append hprefix tailTrace_6748308
  have hstable : (prefixWord ++ tailWord_6748308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6748308).length < 2 ^ (prefixWord ++ tailWord_6748308).sum := by decide
  have hdescent : baseEnd_6748308 < baseStart_6748308 := by decide
  rcases family_descends (prefixWord ++ tailWord_6748308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6748321 : List Nat := [1, 2, 3, 3, 1, 2, 3, 2, 2, 2, 2]
def baseStart_6748321 : Nat := 118140960795 + 6748321 * 2 ^ 59
def prefixEnd_6748321 : Nat := 4983230072969 + 3 ^ 40 * 6748321 * 2
def baseEnd_6748321 : Nat := 3465132283829796896752543

theorem tailTrace_6748321 : CollatzResearch.WordTrace tailWord_6748321 prefixEnd_6748321 3465132283829796896752543 := by
  unfold tailWord_6748321
  simp only [CollatzResearch.WordTrace]
  refine ⟨246131487384993013314988817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164087658256662008876659211 246131487384993013314988817)
  ·
    refine ⟨184598615538744759986241613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246131487384993013314988817 184598615538744759986241613)
    ·
      refine ⟨69224480827029284994840605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184598615538744759986241613 69224480827029284994840605)
      ·
        refine ⟨25959180310135981873065227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69224480827029284994840605 25959180310135981873065227)
        ·
          refine ⟨38938770465203972809597841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25959180310135981873065227 38938770465203972809597841)
          ·
            refine ⟨29204077848902979607198381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38938770465203972809597841 29204077848902979607198381)
            ·
              refine ⟨10951529193338617352699393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29204077848902979607198381 10951529193338617352699393)
              ·
                refine ⟨8213646895003963014524545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10951529193338617352699393 8213646895003963014524545)
                ·
                  refine ⟨6160235171252972260893409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8213646895003963014524545 6160235171252972260893409)
                  ·
                    refine ⟨4620176378439729195670057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6160235171252972260893409 4620176378439729195670057)
                    ·
                      refine ⟨3465132283829796896752543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4620176378439729195670057 3465132283829796896752543)
                      ·
                        rfl

theorem cell23_6748321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 2, 2, 2, 2].length) (baseStart_6748321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6748321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6748321 prefixEnd_6748321 := by exact prefixLift 6748321
  have htrace : WordTrace (prefixWord ++ tailWord_6748321) baseStart_6748321 baseEnd_6748321 := by
    simpa [prefixWord, tailWord_6748321, baseEnd_6748321] using wordTrace_append hprefix tailTrace_6748321
  have hstable : (prefixWord ++ tailWord_6748321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6748321).length < 2 ^ (prefixWord ++ tailWord_6748321).sum := by decide
  have hdescent : baseEnd_6748321 < baseStart_6748321 := by decide
  rcases family_descends (prefixWord ++ tailWord_6748321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6748374 : List Nat := [5, 2, 1, 2, 1, 1, 1, 1, 4, 5]
def baseStart_6748374 : Nat := 118140960795 + 6748374 * 2 ^ 59
def prefixEnd_6748374 : Nat := 4983230072969 + 3 ^ 40 * 6748374 * 2
def baseEnd_6748374 : Nat := 1155053166101495063129933

theorem tailTrace_6748374 : CollatzResearch.WordTrace tailWord_6748374 prefixEnd_6748374 1155053166101495063129933 := by
  unfold tailWord_6748374
  simp only [CollatzResearch.WordTrace]
  refine ⟨15383338778362562710416761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 164088946969200668911112117 15383338778362562710416761)
  ·
    refine ⟨11537504083771922032812571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15383338778362562710416761 11537504083771922032812571)
    ·
      refine ⟨17306256125657883049218857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11537504083771922032812571 17306256125657883049218857)
      ·
        refine ⟨12979692094243412286914143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17306256125657883049218857 12979692094243412286914143)
        ·
          refine ⟨19469538141365118430371215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12979692094243412286914143 19469538141365118430371215)
          ·
            refine ⟨29204307212047677645556823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19469538141365118430371215 29204307212047677645556823)
            ·
              refine ⟨43806460818071516468335235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29204307212047677645556823 43806460818071516468335235)
              ·
                refine ⟨65709691227107274702502853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43806460818071516468335235 65709691227107274702502853)
                ·
                  refine ⟨12320567105082614006719285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65709691227107274702502853 12320567105082614006719285)
                  ·
                    refine ⟨1155053166101495063129933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12320567105082614006719285 1155053166101495063129933)
                    ·
                      rfl

theorem cell23_6748374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_6748374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6748374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6748374 prefixEnd_6748374 := by exact prefixLift 6748374
  have htrace : WordTrace (prefixWord ++ tailWord_6748374) baseStart_6748374 baseEnd_6748374 := by
    simpa [prefixWord, tailWord_6748374, baseEnd_6748374] using wordTrace_append hprefix tailTrace_6748374
  have hstable : (prefixWord ++ tailWord_6748374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6748374).length < 2 ^ (prefixWord ++ tailWord_6748374).sum := by decide
  have hdescent : baseEnd_6748374 < baseStart_6748374 := by decide
  rcases family_descends (prefixWord ++ tailWord_6748374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6748377 : List Nat := [1, 2, 1, 2, 3, 1, 2, 1, 4, 4, 2]
def baseStart_6748377 : Nat := 118140960795 + 6748377 * 2 ^ 59
def prefixEnd_6748377 : Nat := 4983230072969 + 3 ^ 40 * 6748377 * 2
def baseEnd_6748377 : Nat := 3465161038746448677652285

theorem tailTrace_6748377 : CollatzResearch.WordTrace tailWord_6748377 prefixEnd_6748377 3465161038746448677652285 := by
  unfold tailWord_6748377
  simp only [CollatzResearch.WordTrace]
  refine ⟨246133529872790134879027385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164089019915193423252684923 246133529872790134879027385)
  ·
    refine ⟨184600147404592601159270539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246133529872790134879027385 184600147404592601159270539)
    ·
      refine ⟨276900221106888901738905809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184600147404592601159270539 276900221106888901738905809)
      ·
        refine ⟨207675165830166676304179357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 276900221106888901738905809 207675165830166676304179357)
        ·
          refine ⟨77878187186312503614067259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 207675165830166676304179357 77878187186312503614067259)
          ·
            refine ⟨116817280779468755421100889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77878187186312503614067259 116817280779468755421100889)
            ·
              refine ⟨87612960584601566565825667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116817280779468755421100889 87612960584601566565825667)
              ·
                refine ⟨131419440876902349848738501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87612960584601566565825667 131419440876902349848738501)
                ·
                  refine ⟨24641145164419190596638469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 131419440876902349848738501 24641145164419190596638469)
                  ·
                    refine ⟨4620214718328598236869713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24641145164419190596638469 4620214718328598236869713)
                    ·
                      refine ⟨3465161038746448677652285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4620214718328598236869713 3465161038746448677652285)
                      ·
                        rfl

theorem cell23_6748377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 4, 4, 2].length) (baseStart_6748377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6748377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6748377 prefixEnd_6748377 := by exact prefixLift 6748377
  have htrace : WordTrace (prefixWord ++ tailWord_6748377) baseStart_6748377 baseEnd_6748377 := by
    simpa [prefixWord, tailWord_6748377, baseEnd_6748377] using wordTrace_append hprefix tailTrace_6748377
  have hstable : (prefixWord ++ tailWord_6748377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6748377).length < 2 ^ (prefixWord ++ tailWord_6748377).sum := by decide
  have hdescent : baseEnd_6748377 < baseStart_6748377 := by decide
  rcases family_descends (prefixWord ++ tailWord_6748377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6748444 : List Nat := [2, 2, 3, 1, 1, 1, 1, 5, 3, 1, 3]
def baseStart_6748444 : Nat := 118140960795 + 6748444 * 2 ^ 59
def prefixEnd_6748444 : Nat := 4983230072969 + 3 ^ 40 * 6748444 * 2
def baseEnd_6748444 : Nat := 3465195441950299915514477

theorem tailTrace_6748444 : CollatzResearch.WordTrace tailWord_6748444 prefixEnd_6748444 3465195441950299915514477 := by
  unfold tailWord_6748444
  simp only [CollatzResearch.WordTrace]
  refine ⟨123067986781773702660858193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164090649042364936881144257 123067986781773702660858193)
  ·
    refine ⟨92300990086330276995643645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123067986781773702660858193 92300990086330276995643645)
    ·
      refine ⟨34612871282373853873366367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92300990086330276995643645 34612871282373853873366367)
      ·
        refine ⟨51919306923560780810049551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34612871282373853873366367 51919306923560780810049551)
        ·
          refine ⟨77878960385341171215074327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51919306923560780810049551 77878960385341171215074327)
          ·
            refine ⟨116818440578011756822611491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77878960385341171215074327 116818440578011756822611491)
            ·
              refine ⟨175227660867017635233917237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116818440578011756822611491 175227660867017635233917237)
              ·
                refine ⟨16427593206282903303179741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 175227660867017635233917237 16427593206282903303179741)
                ·
                  refine ⟨6160347452356088738692403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16427593206282903303179741 6160347452356088738692403)
                  ·
                    refine ⟨9240521178534133108038605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6160347452356088738692403 9240521178534133108038605)
                    ·
                      refine ⟨3465195441950299915514477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9240521178534133108038605 3465195441950299915514477)
                      ·
                        rfl

theorem cell23_6748444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 5, 3, 1, 3].length) (baseStart_6748444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6748444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6748444 prefixEnd_6748444 := by exact prefixLift 6748444
  have htrace : WordTrace (prefixWord ++ tailWord_6748444) baseStart_6748444 baseEnd_6748444 := by
    simpa [prefixWord, tailWord_6748444, baseEnd_6748444] using wordTrace_append hprefix tailTrace_6748444
  have hstable : (prefixWord ++ tailWord_6748444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6748444).length < 2 ^ (prefixWord ++ tailWord_6748444).sum := by decide
  have hdescent : baseEnd_6748444 < baseStart_6748444 := by decide
  rcases family_descends (prefixWord ++ tailWord_6748444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6748447 : List Nat := [1, 1, 2, 4, 3, 1, 1, 2, 3, 5]
def baseStart_6748447 : Nat := 118140960795 + 6748447 * 2 ^ 59
def prefixEnd_6748447 : Nat := 4983230072969 + 3 ^ 40 * 6748447 * 2
def baseEnd_6748447 : Nat := 1155065660797421134592321

theorem tailTrace_6748447 : CollatzResearch.WordTrace tailWord_6748447 prefixEnd_6748447 1155065660797421134592321 := by
  unfold tailWord_6748447
  simp only [CollatzResearch.WordTrace]
  refine ⟨246136082982536536834075595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164090721988357691222717063 246136082982536536834075595)
  ·
    refine ⟨369204124473804805251113393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246136082982536536834075595 369204124473804805251113393)
    ·
      refine ⟨276903093355353603938335045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 369204124473804805251113393 276903093355353603938335045)
      ·
        refine ⟨51919330004128800738437821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 276903093355353603938335045 51919330004128800738437821)
        ·
          refine ⟨19469748751548300276914183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51919330004128800738437821 19469748751548300276914183)
          ·
            refine ⟨29204623127322450415371275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19469748751548300276914183 29204623127322450415371275)
            ·
              refine ⟨43806934690983675623056913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29204623127322450415371275 43806934690983675623056913)
              ·
                refine ⟨32855201018237756717292685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43806934690983675623056913 32855201018237756717292685)
                ·
                  refine ⟨12320700381839158768984757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32855201018237756717292685 12320700381839158768984757)
                  ·
                    refine ⟨1155065660797421134592321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12320700381839158768984757 1155065660797421134592321)
                    ·
                      rfl

theorem cell23_6748447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 2, 3, 5].length) (baseStart_6748447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6748447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6748447 prefixEnd_6748447 := by exact prefixLift 6748447
  have htrace : WordTrace (prefixWord ++ tailWord_6748447) baseStart_6748447 baseEnd_6748447 := by
    simpa [prefixWord, tailWord_6748447, baseEnd_6748447] using wordTrace_append hprefix tailTrace_6748447
  have hstable : (prefixWord ++ tailWord_6748447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6748447).length < 2 ^ (prefixWord ++ tailWord_6748447).sum := by decide
  have hdescent : baseEnd_6748447 < baseStart_6748447 := by decide
  rcases family_descends (prefixWord ++ tailWord_6748447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6748467 : List Nat := [1, 1, 1, 2, 5, 1, 1, 3, 3, 1, 4]
def baseStart_6748467 : Nat := 118140960795 + 6748467 * 2 ^ 59
def prefixEnd_6748467 : Nat := 4983230072969 + 3 ^ 40 * 6748467 * 2
def baseEnd_6748467 : Nat := 3465207252005353325526871

theorem tailTrace_6748467 : CollatzResearch.WordTrace tailWord_6748467 prefixEnd_6748467 3465207252005353325526871 := by
  unfold tailWord_6748467
  simp only [CollatzResearch.WordTrace]
  refine ⟨246136812442464080249803655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164091208294976053499869103 246136812442464080249803655)
  ·
    refine ⟨369205218663696120374705483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246136812442464080249803655 369205218663696120374705483)
    ·
      refine ⟨553807827995544180562058225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369205218663696120374705483 553807827995544180562058225)
      ·
        refine ⟨415355870996658135421543669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 553807827995544180562058225 415355870996658135421543669)
        ·
          refine ⟨38939612905936700195769719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 415355870996658135421543669 38939612905936700195769719)
          ·
            refine ⟨58409419358905050293654579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38939612905936700195769719 58409419358905050293654579)
            ·
              refine ⟨87614129038357575440481869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58409419358905050293654579 87614129038357575440481869)
              ·
                refine ⟨32855298389384090790180701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87614129038357575440481869 32855298389384090790180701)
                ·
                  refine ⟨12320736896019034046317763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32855298389384090790180701 12320736896019034046317763)
                  ·
                    refine ⟨18481105344028551069476645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12320736896019034046317763 18481105344028551069476645)
                    ·
                      refine ⟨3465207252005353325526871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18481105344028551069476645 3465207252005353325526871)
                      ·
                        rfl

theorem cell23_6748467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 3, 3, 1, 4].length) (baseStart_6748467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6748467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6748467 prefixEnd_6748467 := by exact prefixLift 6748467
  have htrace : WordTrace (prefixWord ++ tailWord_6748467) baseStart_6748467 baseEnd_6748467 := by
    simpa [prefixWord, tailWord_6748467, baseEnd_6748467] using wordTrace_append hprefix tailTrace_6748467
  have hstable : (prefixWord ++ tailWord_6748467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6748467).length < 2 ^ (prefixWord ++ tailWord_6748467).sum := by decide
  have hdescent : baseEnd_6748467 < baseStart_6748467 := by decide
  rcases family_descends (prefixWord ++ tailWord_6748467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6748478 : List Nat := [4, 2, 1, 2, 1, 2, 1, 5, 1, 1, 3]
def baseStart_6748478 : Nat := 118140960795 + 6748478 * 2 ^ 59
def prefixEnd_6748478 : Nat := 4983230072969 + 3 ^ 40 * 6748478 * 2
def baseEnd_6748478 : Nat := 3465212900292552782489321

theorem tailTrace_6748478 : CollatzResearch.WordTrace tailWord_6748478 prefixEnd_6748478 3465212900292552782489321 := by
  unfold tailWord_6748478
  simp only [CollatzResearch.WordTrace]
  refine ⟨30767151705678028641056761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164091475763616152752302725 30767151705678028641056761)
  ·
    refine ⟨23075363779258521480792571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30767151705678028641056761 23075363779258521480792571)
    ·
      refine ⟨34613045668887782221188857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23075363779258521480792571 34613045668887782221188857)
      ·
        refine ⟨25959784251665836665891643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34613045668887782221188857 25959784251665836665891643)
        ·
          refine ⟨38939676377498754998837465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25959784251665836665891643 38939676377498754998837465)
          ·
            refine ⟨29204757283124066249128099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38939676377498754998837465 29204757283124066249128099)
            ·
              refine ⟨43807135924686099373692149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29204757283124066249128099 43807135924686099373692149)
              ·
                refine ⟨4106918992939321816283639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43807135924686099373692149 4106918992939321816283639)
                ·
                  refine ⟨6160378489408982724425459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4106918992939321816283639 6160378489408982724425459)
                  ·
                    refine ⟨9240567734113474086638189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6160378489408982724425459 9240567734113474086638189)
                    ·
                      refine ⟨3465212900292552782489321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9240567734113474086638189 3465212900292552782489321)
                      ·
                        rfl

theorem cell23_6748478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 5, 1, 1, 3].length) (baseStart_6748478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6748478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6748478 prefixEnd_6748478 := by exact prefixLift 6748478
  have htrace : WordTrace (prefixWord ++ tailWord_6748478) baseStart_6748478 baseEnd_6748478 := by
    simpa [prefixWord, tailWord_6748478, baseEnd_6748478] using wordTrace_append hprefix tailTrace_6748478
  have hstable : (prefixWord ++ tailWord_6748478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6748478).length < 2 ^ (prefixWord ++ tailWord_6748478).sum := by decide
  have hdescent : baseEnd_6748478 < baseStart_6748478 := by decide
  rcases family_descends (prefixWord ++ tailWord_6748478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6748481 : List Nat := [1, 2, 5, 2, 2, 1, 1, 3, 1, 5]
def baseStart_6748481 : Nat := 118140960795 + 6748481 * 2 ^ 59
def prefixEnd_6748481 : Nat := 4983230072969 + 3 ^ 40 * 6748481 * 2
def baseEnd_6748481 : Nat := 1155071480244838756917269

theorem tailTrace_6748481 : CollatzResearch.WordTrace tailWord_6748481 prefixEnd_6748481 1155071480244838756917269 := by
  unfold tailWord_6748481
  simp only [CollatzResearch.WordTrace]
  refine ⟨246137323064413360640813297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164091548709608907093875531 246137323064413360640813297)
  ·
    refine ⟨184602992298310020480609973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246137323064413360640813297 184602992298310020480609973)
    ·
      refine ⟨17306530527966564420057185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 184602992298310020480609973 17306530527966564420057185)
      ·
        refine ⟨12979897895974923315042889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17306530527966564420057185 12979897895974923315042889)
        ·
          refine ⟨9734923421981192486282167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12979897895974923315042889 9734923421981192486282167)
          ·
            refine ⟨14602385132971788729423251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9734923421981192486282167 14602385132971788729423251)
            ·
              refine ⟨21903577699457683094134877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14602385132971788729423251 21903577699457683094134877)
              ·
                refine ⟨8213841637296631160300579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21903577699457683094134877 8213841637296631160300579)
                ·
                  refine ⟨12320762455944946740450869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8213841637296631160300579 12320762455944946740450869)
                  ·
                    refine ⟨1155071480244838756917269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12320762455944946740450869 1155071480244838756917269)
                    ·
                      rfl

theorem cell23_6748481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 3, 1, 5].length) (baseStart_6748481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6748481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6748481 prefixEnd_6748481 := by exact prefixLift 6748481
  have htrace : WordTrace (prefixWord ++ tailWord_6748481) baseStart_6748481 baseEnd_6748481 := by
    simpa [prefixWord, tailWord_6748481, baseEnd_6748481] using wordTrace_append hprefix tailTrace_6748481
  have hstable : (prefixWord ++ tailWord_6748481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6748481).length < 2 ^ (prefixWord ++ tailWord_6748481).sum := by decide
  have hdescent : baseEnd_6748481 < baseStart_6748481 := by decide
  rcases family_descends (prefixWord ++ tailWord_6748481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6748487 : List Nat := [1, 1, 4, 1, 2, 2, 2, 3, 1, 1, 5]
def baseStart_6748487 : Nat := 118140960795 + 6748487 * 2 ^ 59
def prefixEnd_6748487 : Nat := 4983230072969 + 3 ^ 40 * 6748487 * 2
def baseEnd_6748487 : Nat := 3465217521618443247276779

theorem tailTrace_6748487 : CollatzResearch.WordTrace tailWord_6748487 prefixEnd_6748487 3465217521618443247276779 := by
  unfold tailWord_6748487
  simp only [CollatzResearch.WordTrace]
  refine ⟨246137541902391623665531715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164091694601594415777021143 246137541902391623665531715)
  ·
    refine ⟨369206312853587435498297573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246137541902391623665531715 369206312853587435498297573)
    ·
      refine ⟨69226183660047644155930795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 369206312853587435498297573 69226183660047644155930795)
      ·
        refine ⟨103839275490071466233896193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69226183660047644155930795 103839275490071466233896193)
        ·
          refine ⟨77879456617553599675422145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103839275490071466233896193 77879456617553599675422145)
          ·
            refine ⟨58409592463165199756566609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77879456617553599675422145 58409592463165199756566609)
            ·
              refine ⟨43807194347373899817424957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58409592463165199756566609 43807194347373899817424957)
              ·
                refine ⟨16427697880265212431534359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43807194347373899817424957 16427697880265212431534359)
                ·
                  refine ⟨24641546820397818647301539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16427697880265212431534359 24641546820397818647301539)
                  ·
                    refine ⟨36962320230596727970952309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24641546820397818647301539 36962320230596727970952309)
                    ·
                      refine ⟨3465217521618443247276779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36962320230596727970952309 3465217521618443247276779)
                      ·
                        rfl

theorem cell23_6748487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 3, 1, 1, 5].length) (baseStart_6748487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6748487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6748487 prefixEnd_6748487 := by exact prefixLift 6748487
  have htrace : WordTrace (prefixWord ++ tailWord_6748487) baseStart_6748487 baseEnd_6748487 := by
    simpa [prefixWord, tailWord_6748487, baseEnd_6748487] using wordTrace_append hprefix tailTrace_6748487
  have hstable : (prefixWord ++ tailWord_6748487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6748487).length < 2 ^ (prefixWord ++ tailWord_6748487).sum := by decide
  have hdescent : baseEnd_6748487 < baseStart_6748487 := by decide
  rcases family_descends (prefixWord ++ tailWord_6748487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6748494 : List Nat := [4, 1, 1, 1, 1, 1, 2, 6, 2, 4]
def baseStart_6748494 : Nat := 118140960795 + 6748494 * 2 ^ 59
def prefixEnd_6748494 : Nat := 4983230072969 + 3 ^ 40 * 6748494 * 2
def baseEnd_6748494 : Nat := 1155073705327674906629749

theorem tailTrace_6748494 : CollatzResearch.WordTrace tailWord_6748494 prefixEnd_6748494 1155073705327674906629749 := by
  unfold tailWord_6748494
  simp only [CollatzResearch.WordTrace]
  refine ⟨30767224651670782982629567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164091864808910842574024357 30767224651670782982629567)
  ·
    refine ⟨46150836977506174473944351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30767224651670782982629567 46150836977506174473944351)
    ·
      refine ⟨69226255466259261710916527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46150836977506174473944351 69226255466259261710916527)
      ·
        refine ⟨103839383199388892566374791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69226255466259261710916527 103839383199388892566374791)
        ·
          refine ⟨155759074799083338849562187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103839383199388892566374791 155759074799083338849562187)
          ·
            refine ⟨233638612198625008274343281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155759074799083338849562187 233638612198625008274343281)
            ·
              refine ⟨175228959148968756205757461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 233638612198625008274343281 175228959148968756205757461)
              ·
                refine ⟨8213857460107910447144881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 175228959148968756205757461 8213857460107910447144881)
                ·
                  refine ⟨6160393095080932835358661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8213857460107910447144881 6160393095080932835358661)
                  ·
                    refine ⟨1155073705327674906629749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6160393095080932835358661 1155073705327674906629749)
                    ·
                      rfl

theorem cell23_6748494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 6, 2, 4].length) (baseStart_6748494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6748494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6748494 prefixEnd_6748494 := by exact prefixLift 6748494
  have htrace : WordTrace (prefixWord ++ tailWord_6748494) baseStart_6748494 baseEnd_6748494 := by
    simpa [prefixWord, tailWord_6748494, baseEnd_6748494] using wordTrace_append hprefix tailTrace_6748494
  have hstable : (prefixWord ++ tailWord_6748494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6748494).length < 2 ^ (prefixWord ++ tailWord_6748494).sum := by decide
  have hdescent : baseEnd_6748494 < baseStart_6748494 := by decide
  rcases family_descends (prefixWord ++ tailWord_6748494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6748514 : List Nat := [3, 3, 2, 1, 1, 3, 1, 1, 1, 1, 6]
def baseStart_6748514 : Nat := 118140960795 + 6748514 * 2 ^ 59
def prefixEnd_6748514 : Nat := 4983230072969 + 3 ^ 40 * 6748514 * 2
def baseEnd_6748514 : Nat := 3465231385596114641639155

theorem tailTrace_6748514 : CollatzResearch.WordTrace tailWord_6748514 prefixEnd_6748514 3465231385596114641639155 := by
  unfold tailWord_6748514
  simp only [CollatzResearch.WordTrace]
  refine ⟨61534631668323451819191149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164092351115529204851176397 61534631668323451819191149)
  ·
    refine ⟨23075486875621294432196681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61534631668323451819191149 23075486875621294432196681)
    ·
      refine ⟨17306615156715970824147511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23075486875621294432196681 17306615156715970824147511)
      ·
        refine ⟨25959922735073956236221267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17306615156715970824147511 25959922735073956236221267)
        ·
          refine ⟨38939884102610934354331901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25959922735073956236221267 38939884102610934354331901)
          ·
            refine ⟨14602456538479100382874463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38939884102610934354331901 14602456538479100382874463)
            ·
              refine ⟨21903684807718650574311695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14602456538479100382874463 21903684807718650574311695)
              ·
                refine ⟨32855527211577975861467543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21903684807718650574311695 32855527211577975861467543)
                ·
                  refine ⟨49283290817366963792201315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32855527211577975861467543 49283290817366963792201315)
                  ·
                    refine ⟨73924936226050445688301973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49283290817366963792201315 73924936226050445688301973)
                    ·
                      refine ⟨3465231385596114641639155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73924936226050445688301973 3465231385596114641639155)
                      ·
                        rfl

theorem cell23_6748514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_6748514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6748514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6748514 prefixEnd_6748514 := by exact prefixLift 6748514
  have htrace : WordTrace (prefixWord ++ tailWord_6748514) baseStart_6748514 baseEnd_6748514 := by
    simpa [prefixWord, tailWord_6748514, baseEnd_6748514] using wordTrace_append hprefix tailTrace_6748514
  have hstable : (prefixWord ++ tailWord_6748514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6748514).length < 2 ^ (prefixWord ++ tailWord_6748514).sum := by decide
  have hdescent : baseEnd_6748514 < baseStart_6748514 := by decide
  rcases family_descends (prefixWord ++ tailWord_6748514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6748544 : List Nat := [2, 1, 1, 2, 1, 2, 1, 1, 7, 3, 2]
def baseStart_6748544 : Nat := 118140960795 + 6748544 * 2 ^ 59
def prefixEnd_6748544 : Nat := 4983230072969 + 3 ^ 40 * 6748544 * 2
def baseEnd_6748544 : Nat := 3465246790015749524264017

theorem tailTrace_6748544 : CollatzResearch.WordTrace tailWord_6748544 prefixEnd_6748544 3465246790015749524264017 := by
  unfold tailWord_6748544
  simp only [CollatzResearch.WordTrace]
  refine ⟨123069810431592561200178343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164093080575456748266904457 123069810431592561200178343)
  ·
    refine ⟨184604715647388841800267515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123069810431592561200178343 184604715647388841800267515)
    ·
      refine ⟨276907073471083262700401273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184604715647388841800267515 276907073471083262700401273)
      ·
        refine ⟨207680305103312447025300955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 276907073471083262700401273 207680305103312447025300955)
        ·
          refine ⟨311520457654968670537951433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207680305103312447025300955 311520457654968670537951433)
          ·
            refine ⟨233640343241226502903463575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 311520457654968670537951433 233640343241226502903463575)
            ·
              refine ⟨350460514861839754355195363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 233640343241226502903463575 350460514861839754355195363)
              ·
                refine ⟨525690772292759631532793045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 350460514861839754355195363 525690772292759631532793045)
                ·
                  refine ⟨12320877475611553864049837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 525690772292759631532793045 12320877475611553864049837)
                  ·
                    refine ⟨4620329053354332699018689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12320877475611553864049837 4620329053354332699018689)
                    ·
                      refine ⟨3465246790015749524264017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4620329053354332699018689 3465246790015749524264017)
                      ·
                        rfl

theorem cell23_6748544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 7, 3, 2].length) (baseStart_6748544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6748544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6748544 prefixEnd_6748544 := by exact prefixLift 6748544
  have htrace : WordTrace (prefixWord ++ tailWord_6748544) baseStart_6748544 baseEnd_6748544 := by
    simpa [prefixWord, tailWord_6748544, baseEnd_6748544] using wordTrace_append hprefix tailTrace_6748544
  have hstable : (prefixWord ++ tailWord_6748544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6748544).length < 2 ^ (prefixWord ++ tailWord_6748544).sum := by decide
  have hdescent : baseEnd_6748544 < baseStart_6748544 := by decide
  rcases family_descends (prefixWord ++ tailWord_6748544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6748551 : List Nat := [1, 1, 4, 2, 2, 1, 2, 4, 2, 1, 3]
def baseStart_6748551 : Nat := 118140960795 + 6748551 * 2 ^ 59
def prefixEnd_6748551 : Nat := 4983230072969 + 3 ^ 40 * 6748551 * 2
def baseEnd_6748551 : Nat := 3465250384380330996876485

theorem tailTrace_6748551 : CollatzResearch.WordTrace tailWord_6748551 prefixEnd_6748551 3465250384380330996876485 := by
  unfold tailWord_6748551
  simp only [CollatzResearch.WordTrace]
  refine ⟨246139876174159762595861507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164093250782773175063907671 246139876174159762595861507)
  ·
    refine ⟨369209814261239643893792261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246139876174159762595861507 369209814261239643893792261)
    ·
      refine ⟨69226840173982433230086049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 369209814261239643893792261 69226840173982433230086049)
      ·
        refine ⟨51920130130486824922564537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69226840173982433230086049 51920130130486824922564537)
        ·
          refine ⟨38940097597865118691923403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51920130130486824922564537 38940097597865118691923403)
          ·
            refine ⟨58410146396797678037885105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38940097597865118691923403 58410146396797678037885105)
            ·
              refine ⟨43807609797598258528413829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58410146396797678037885105 43807609797598258528413829)
              ·
                refine ⟨8213926837049673474077593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43807609797598258528413829 8213926837049673474077593)
                ·
                  refine ⟨6160445127787255105558195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8213926837049673474077593 6160445127787255105558195)
                  ·
                    refine ⟨9240667691680882658337293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6160445127787255105558195 9240667691680882658337293)
                    ·
                      refine ⟨3465250384380330996876485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9240667691680882658337293 3465250384380330996876485)
                      ·
                        rfl

theorem cell23_6748551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 4, 2, 1, 3].length) (baseStart_6748551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6748551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6748551 prefixEnd_6748551 := by exact prefixLift 6748551
  have htrace : WordTrace (prefixWord ++ tailWord_6748551) baseStart_6748551 baseEnd_6748551 := by
    simpa [prefixWord, tailWord_6748551, baseEnd_6748551] using wordTrace_append hprefix tailTrace_6748551
  have hstable : (prefixWord ++ tailWord_6748551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6748551).length < 2 ^ (prefixWord ++ tailWord_6748551).sum := by decide
  have hdescent : baseEnd_6748551 < baseStart_6748551 := by decide
  rcases family_descends (prefixWord ++ tailWord_6748551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6748567 : List Nat := [1, 1, 3, 3, 1, 1, 2, 3, 2, 6]
def baseStart_6748567 : Nat := 118140960795 + 6748567 * 2 ^ 59
def prefixEnd_6748567 : Nat := 4983230072969 + 3 ^ 40 * 6748567 * 2
def baseEnd_6748567 : Nat := 1155086200023600978092137

theorem tailTrace_6748567 : CollatzResearch.WordTrace tailWord_6748567 prefixEnd_6748567 1155086200023600978092137 := by
  unfold tailWord_6748567
  simp only [CollatzResearch.WordTrace]
  refine ⟨246140459742101797328443955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164093639828067864885629303 246140459742101797328443955)
  ·
    refine ⟨369210689613152695992665933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246140459742101797328443955 369210689613152695992665933)
    ·
      refine ⟨138454008604932260997249725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 369210689613152695992665933 138454008604932260997249725)
      ·
        refine ⟨51920253226849597873968647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138454008604932260997249725 51920253226849597873968647)
        ·
          refine ⟨77880379840274396810952971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51920253226849597873968647 77880379840274396810952971)
          ·
            refine ⟨116820569760411595216429457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77880379840274396810952971 116820569760411595216429457)
            ·
              refine ⟨87615427320308696412322093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116820569760411595216429457 87615427320308696412322093)
              ·
                refine ⟨32855785245115761154620785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87615427320308696412322093 32855785245115761154620785)
                ·
                  refine ⟨24641838933836820865965589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32855785245115761154620785 24641838933836820865965589)
                  ·
                    refine ⟨1155086200023600978092137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24641838933836820865965589 1155086200023600978092137)
                    ·
                      rfl

theorem cell23_6748567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 3, 2, 6].length) (baseStart_6748567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6748567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6748567 prefixEnd_6748567 := by exact prefixLift 6748567
  have htrace : WordTrace (prefixWord ++ tailWord_6748567) baseStart_6748567 baseEnd_6748567 := by
    simpa [prefixWord, tailWord_6748567, baseEnd_6748567] using wordTrace_append hprefix tailTrace_6748567
  have hstable : (prefixWord ++ tailWord_6748567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6748567).length < 2 ^ (prefixWord ++ tailWord_6748567).sum := by decide
  have hdescent : baseEnd_6748567 < baseStart_6748567 := by decide
  rcases family_descends (prefixWord ++ tailWord_6748567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6748568 : List Nat := [2, 1, 2, 5, 1, 2, 1, 3, 2, 1, 3]
def baseStart_6748568 : Nat := 118140960795 + 6748568 * 2 ^ 59
def prefixEnd_6748568 : Nat := 4983230072969 + 3 ^ 40 * 6748568 * 2
def baseEnd_6748568 : Nat := 3465259113551457430363907

theorem tailTrace_6748568 : CollatzResearch.WordTrace tailWord_6748568 prefixEnd_6748568 3465259113551457430363907 := by
  unfold tailWord_6748568
  simp only [CollatzResearch.WordTrace]
  refine ⟨123070248107549087249615179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164093664143398782999486905 123070248107549087249615179)
  ·
    refine ⟨184605372161323630874422769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123070248107549087249615179 184605372161323630874422769)
    ·
      refine ⟨138454029120992723155817077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184605372161323630874422769 138454029120992723155817077)
      ·
        refine ⟨12980065230093067795857851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 138454029120992723155817077 12980065230093067795857851)
        ·
          refine ⟨19470097845139601693786777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12980065230093067795857851 19470097845139601693786777)
          ·
            refine ⟨14602573383854701270340083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19470097845139601693786777 14602573383854701270340083)
            ·
              refine ⟨21903860075782051905510125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14602573383854701270340083 21903860075782051905510125)
              ·
                refine ⟨8213947528418269464566297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21903860075782051905510125 8213947528418269464566297)
                ·
                  refine ⟨6160460646313702098424723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8213947528418269464566297 6160460646313702098424723)
                  ·
                    refine ⟨9240690969470553147637085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6160460646313702098424723 9240690969470553147637085)
                    ·
                      refine ⟨3465259113551457430363907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9240690969470553147637085 3465259113551457430363907)
                      ·
                        rfl

theorem cell23_6748568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_6748568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6748568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6748568 prefixEnd_6748568 := by exact prefixLift 6748568
  have htrace : WordTrace (prefixWord ++ tailWord_6748568) baseStart_6748568 baseEnd_6748568 := by
    simpa [prefixWord, tailWord_6748568, baseEnd_6748568] using wordTrace_append hprefix tailTrace_6748568
  have hstable : (prefixWord ++ tailWord_6748568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6748568).length < 2 ^ (prefixWord ++ tailWord_6748568).sum := by decide
  have hdescent : baseEnd_6748568 < baseStart_6748568 := by decide
  rcases family_descends (prefixWord ++ tailWord_6748568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6748664 : List Nat := [2, 1, 2, 1, 1, 4, 2, 1, 4, 1, 4]
def baseStart_6748664 : Nat := 118140960795 + 6748664 * 2 ^ 59
def prefixEnd_6748664 : Nat := 4983230072969 + 3 ^ 40 * 6748664 * 2
def baseEnd_6748664 : Nat := 3465308407694289054763465

theorem tailTrace_6748664 : CollatzResearch.WordTrace tailWord_6748664 prefixEnd_6748664 3465308407694289054763465 := by
  unfold tailWord_6748664
  simp only [CollatzResearch.WordTrace]
  refine ⟨123071998811375191447362523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164095998415166921929816697 123071998811375191447362523)
  ·
    refine ⟨184607998217062787171043785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123071998811375191447362523 184607998217062787171043785)
    ·
      refine ⟨138455998662797090378282839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184607998217062787171043785 138455998662797090378282839)
      ·
        refine ⟨207683997994195635567424259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138455998662797090378282839 207683997994195635567424259)
        ·
          refine ⟨311525996991293453351136389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207683997994195635567424259 311525996991293453351136389)
          ·
            refine ⟨58411124435867522503338073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 311525996991293453351136389 58411124435867522503338073)
            ·
              refine ⟨43808343326900641877503555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58411124435867522503338073 43808343326900641877503555)
              ·
                refine ⟨65712514990350962816255333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43808343326900641877503555 65712514990350962816255333)
                ·
                  refine ⟨12321096560690805528047875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65712514990350962816255333 12321096560690805528047875)
                  ·
                    refine ⟨18481644841036208292071813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12321096560690805528047875 18481644841036208292071813)
                    ·
                      refine ⟨3465308407694289054763465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18481644841036208292071813 3465308407694289054763465)
                      ·
                        rfl

theorem cell23_6748664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 1, 4, 1, 4].length) (baseStart_6748664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6748664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6748664 prefixEnd_6748664 := by exact prefixLift 6748664
  have htrace : WordTrace (prefixWord ++ tailWord_6748664) baseStart_6748664 baseEnd_6748664 := by
    simpa [prefixWord, tailWord_6748664, baseEnd_6748664] using wordTrace_append hprefix tailTrace_6748664
  have hstable : (prefixWord ++ tailWord_6748664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6748664).length < 2 ^ (prefixWord ++ tailWord_6748664).sum := by decide
  have hdescent : baseEnd_6748664 < baseStart_6748664 := by decide
  rcases family_descends (prefixWord ++ tailWord_6748664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6748687 : List Nat := [1, 1, 2, 1, 1, 1, 2, 4, 10]
def baseStart_6748687 : Nat := 118140960795 + 6748687 * 2 ^ 59
def prefixEnd_6748687 : Nat := 4983230072969 + 3 ^ 40 * 6748687 * 2
def baseEnd_6748687 : Nat := 385035579749926940530651

theorem tailTrace_6748687 : CollatzResearch.WordTrace tailWord_6748687 prefixEnd_6748687 385035579749926940530651 := by
  unfold tailWord_6748687
  simp only [CollatzResearch.WordTrace]
  refine ⟨246144836501667057822812315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164096557667778038548541543 246144836501667057822812315)
  ·
    refine ⟨369217254752500586734218473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246144836501667057822812315 369217254752500586734218473)
    ·
      refine ⟨276912941064375440050663855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 369217254752500586734218473 276912941064375440050663855)
      ·
        refine ⟨415369411596563160075995783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276912941064375440050663855 415369411596563160075995783)
        ·
          refine ⟨623054117394844740113993675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 415369411596563160075995783 623054117394844740113993675)
          ·
            refine ⟨934581176092267110170990513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 623054117394844740113993675 934581176092267110170990513)
            ·
              refine ⟨700935882069200332628242885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 934581176092267110170990513 700935882069200332628242885)
              ·
                refine ⟨131425477887975062367795541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 700935882069200332628242885 131425477887975062367795541)
                ·
                  refine ⟨385035579749926940530651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 131425477887975062367795541 385035579749926940530651)
                  ·
                    rfl

theorem cell23_6748687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 10].length) (baseStart_6748687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6748687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6748687 prefixEnd_6748687 := by exact prefixLift 6748687
  have htrace : WordTrace (prefixWord ++ tailWord_6748687) baseStart_6748687 baseEnd_6748687 := by
    simpa [prefixWord, tailWord_6748687, baseEnd_6748687] using wordTrace_append hprefix tailTrace_6748687
  have hstable : (prefixWord ++ tailWord_6748687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6748687).length < 2 ^ (prefixWord ++ tailWord_6748687).sum := by decide
  have hdescent : baseEnd_6748687 < baseStart_6748687 := by decide
  rcases family_descends (prefixWord ++ tailWord_6748687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6748701 : List Nat := [1, 4, 2, 2, 1, 2, 2, 1, 1, 4, 3]
def baseStart_6748701 : Nat := 118140960795 + 6748701 * 2 ^ 59
def prefixEnd_6748701 : Nat := 4983230072969 + 3 ^ 40 * 6748701 * 2
def baseEnd_6748701 : Nat := 3465327406478505410000795

theorem tailTrace_6748701 : CollatzResearch.WordTrace tailWord_6748701 prefixEnd_6748701 3465327406478505410000795 := by
  unfold tailWord_6748701
  simp only [CollatzResearch.WordTrace]
  refine ⟨246145347123616338213821957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164096898082410892142547971 246145347123616338213821957)
  ·
    refine ⟨46152252585678063415091617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 246145347123616338213821957 46152252585678063415091617)
    ·
      refine ⟨34614189439258547561318713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46152252585678063415091617 34614189439258547561318713)
      ·
        refine ⟨25960642079443910670989035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34614189439258547561318713 25960642079443910670989035)
        ·
          refine ⟨38940963119165866006483553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25960642079443910670989035 38940963119165866006483553)
          ·
            refine ⟨29205722339374399504862665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38940963119165866006483553 29205722339374399504862665)
            ·
              refine ⟨21904291754530799628646999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29205722339374399504862665 21904291754530799628646999)
              ·
                refine ⟨32856437631796199442970499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21904291754530799628646999 32856437631796199442970499)
                ·
                  refine ⟨49284656447694299164455749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32856437631796199442970499 49284656447694299164455749)
                  ·
                    refine ⟨9240873083942681093335453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49284656447694299164455749 9240873083942681093335453)
                    ·
                      refine ⟨3465327406478505410000795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9240873083942681093335453 3465327406478505410000795)
                      ·
                        rfl

theorem cell23_6748701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 1, 1, 4, 3].length) (baseStart_6748701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6748701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6748701 prefixEnd_6748701 := by exact prefixLift 6748701
  have htrace : WordTrace (prefixWord ++ tailWord_6748701) baseStart_6748701 baseEnd_6748701 := by
    simpa [prefixWord, tailWord_6748701, baseEnd_6748701] using wordTrace_append hprefix tailTrace_6748701
  have hstable : (prefixWord ++ tailWord_6748701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6748701).length < 2 ^ (prefixWord ++ tailWord_6748701).sum := by decide
  have hdescent : baseEnd_6748701 < baseStart_6748701 := by decide
  rcases family_descends (prefixWord ++ tailWord_6748701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6748725 : List Nat := [1, 3, 3, 1, 1, 2, 5, 2, 1, 4]
def baseStart_6748725 : Nat := 118140960795 + 6748725 * 2 ^ 59
def prefixEnd_6748725 : Nat := 4983230072969 + 3 ^ 40 * 6748725 * 2
def baseEnd_6748725 : Nat := 1155113243338071105366895

theorem tailTrace_6748725 : CollatzResearch.WordTrace tailWord_6748725 prefixEnd_6748725 1155113243338071105366895 := by
  unfold tailWord_6748725
  simp only [CollatzResearch.WordTrace]
  refine ⟨246146222475529390312695629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164097481650352926875130419 246146222475529390312695629)
  ·
    refine ⟨92304833428323521367260861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 246146222475529390312695629 92304833428323521367260861)
    ·
      refine ⟨34614312535621320512722823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92304833428323521367260861 34614312535621320512722823)
      ·
        refine ⟨51921468803431980769084235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34614312535621320512722823 51921468803431980769084235)
        ·
          refine ⟨77882203205147971153626353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51921468803431980769084235 77882203205147971153626353)
          ·
            refine ⟨58411652403860978365219765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77882203205147971153626353 58411652403860978365219765)
            ·
              refine ⟨5476092412861966721739353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58411652403860978365219765 5476092412861966721739353)
              ·
                refine ⟨4107069309646475041304515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5476092412861966721739353 4107069309646475041304515)
                ·
                  refine ⟨6160603964469712561956773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4107069309646475041304515 6160603964469712561956773)
                  ·
                    refine ⟨1155113243338071105366895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6160603964469712561956773 1155113243338071105366895)
                    ·
                      rfl

theorem cell23_6748725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 5, 2, 1, 4].length) (baseStart_6748725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6748725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6748725 prefixEnd_6748725 := by exact prefixLift 6748725
  have htrace : WordTrace (prefixWord ++ tailWord_6748725) baseStart_6748725 baseEnd_6748725 := by
    simpa [prefixWord, tailWord_6748725, baseEnd_6748725] using wordTrace_append hprefix tailTrace_6748725
  have hstable : (prefixWord ++ tailWord_6748725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6748725).length < 2 ^ (prefixWord ++ tailWord_6748725).sum := by decide
  have hdescent : baseEnd_6748725 < baseStart_6748725 := by decide
  rcases family_descends (prefixWord ++ tailWord_6748725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6748751 : List Nat := [1, 1, 2, 1, 1, 2, 7, 2, 1, 5]
def baseStart_6748751 : Nat := 118140960795 + 6748751 * 2 ^ 59
def prefixEnd_6748751 : Nat := 4983230072969 + 3 ^ 40 * 6748751 * 2
def baseEnd_6748751 : Nat := 1155117693503743404791855

theorem tailTrace_6748751 : CollatzResearch.WordTrace tailWord_6748751 prefixEnd_6748751 1155117693503743404791855 := by
  unfold tailWord_6748751
  simp only [CollatzResearch.WordTrace]
  refine ⟨246147170773435196753142107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164098113848956797835428071 246147170773435196753142107)
  ·
    refine ⟨369220756160152795129713161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246147170773435196753142107 369220756160152795129713161)
    ·
      refine ⟨276915567120114596347284871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 369220756160152795129713161 276915567120114596347284871)
      ·
        refine ⟨415373350680171894520927307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276915567120114596347284871 415373350680171894520927307)
        ·
          refine ⟨623060026020257841781390961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 415373350680171894520927307 623060026020257841781390961)
          ·
            refine ⟨467295019515193381336043221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 623060026020257841781390961 467295019515193381336043221)
            ·
              refine ⟨10952227019887344875063513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 467295019515193381336043221 10952227019887344875063513)
              ·
                refine ⟨8214170264915508656297635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10952227019887344875063513 8214170264915508656297635)
                ·
                  refine ⟨12321255397373262984446453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8214170264915508656297635 12321255397373262984446453)
                  ·
                    refine ⟨1155117693503743404791855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12321255397373262984446453 1155117693503743404791855)
                    ·
                      rfl

theorem cell23_6748751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 2, 1, 5].length) (baseStart_6748751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6748751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6748751 prefixEnd_6748751 := by exact prefixLift 6748751
  have htrace : WordTrace (prefixWord ++ tailWord_6748751) baseStart_6748751 baseEnd_6748751 := by
    simpa [prefixWord, tailWord_6748751, baseEnd_6748751] using wordTrace_append hprefix tailTrace_6748751
  have hstable : (prefixWord ++ tailWord_6748751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6748751).length < 2 ^ (prefixWord ++ tailWord_6748751).sum := by decide
  have hdescent : baseEnd_6748751 < baseStart_6748751 := by decide
  rcases family_descends (prefixWord ++ tailWord_6748751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6748782 : List Nat := [4, 1, 2, 2, 2, 2, 1, 4, 1, 1, 3]
def baseStart_6748782 : Nat := 118140960795 + 6748782 * 2 ^ 59
def prefixEnd_6748782 : Nat := 4983230072969 + 3 ^ 40 * 6748782 * 2
def baseEnd_6748782 : Nat := 3465368998411519593087923

theorem tailTrace_6748782 : CollatzResearch.WordTrace tailWord_6748782 prefixEnd_6748782 3465368998411519593087923 := by
  unfold tailWord_6748782
  simp only [CollatzResearch.WordTrace]
  refine ⟨30768537679540361130940075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164098867624215259365013733 30768537679540361130940075)
  ·
    refine ⟨46152806519310541696410113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30768537679540361130940075 46152806519310541696410113)
    ·
      refine ⟨34614604889482906272307585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46152806519310541696410113 34614604889482906272307585)
      ·
        refine ⟨25960953667112179704230689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34614604889482906272307585 25960953667112179704230689)
        ·
          refine ⟨19470715250334134778173017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25960953667112179704230689 19470715250334134778173017)
          ·
            refine ⟨14603036437750601083629763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19470715250334134778173017 14603036437750601083629763)
            ·
              refine ⟨21904554656625901625444645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14603036437750601083629763 21904554656625901625444645)
              ·
                refine ⟨4107103998117356554770871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21904554656625901625444645 4107103998117356554770871)
                ·
                  refine ⟨6160655997176034832156307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4107103998117356554770871 6160655997176034832156307)
                  ·
                    refine ⟨9240983995764052248234461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6160655997176034832156307 9240983995764052248234461)
                    ·
                      refine ⟨3465368998411519593087923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9240983995764052248234461 3465368998411519593087923)
                      ·
                        rfl

theorem cell23_6748782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 4, 1, 1, 3].length) (baseStart_6748782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6748782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6748782 prefixEnd_6748782 := by exact prefixLift 6748782
  have htrace : WordTrace (prefixWord ++ tailWord_6748782) baseStart_6748782 baseEnd_6748782 := by
    simpa [prefixWord, tailWord_6748782, baseEnd_6748782] using wordTrace_append hprefix tailTrace_6748782
  have hstable : (prefixWord ++ tailWord_6748782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6748782).length < 2 ^ (prefixWord ++ tailWord_6748782).sum := by decide
  have hdescent : baseEnd_6748782 < baseStart_6748782 := by decide
  rcases family_descends (prefixWord ++ tailWord_6748782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6748791 : List Nat := [1, 1, 3, 1, 1, 3, 3, 2, 3, 2, 3]
def baseStart_6748791 : Nat := 118140960795 + 6748791 * 2 ^ 59
def prefixEnd_6748791 : Nat := 4983230072969 + 3 ^ 40 * 6748791 * 2
def baseEnd_6748791 : Nat := 3465373619737410057875381

theorem tailTrace_6748791 : CollatzResearch.WordTrace tailWord_6748791 prefixEnd_6748791 3465373619737410057875381 := by
  unfold tailWord_6748791
  simp only [CollatzResearch.WordTrace]
  refine ⟨246148629693290283584598227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164099086462193522389732151 246148629693290283584598227)
  ·
    refine ⟨369222944539935425376897341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246148629693290283584598227 369222944539935425376897341)
    ·
      refine ⟨138458604202475784516336503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 369222944539935425376897341 138458604202475784516336503)
      ·
        refine ⟨207687906303713676774504755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138458604202475784516336503 207687906303713676774504755)
        ·
          refine ⟨311531859455570515161757133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207687906303713676774504755 311531859455570515161757133)
          ·
            refine ⟨116824447295838943185658925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 311531859455570515161757133 116824447295838943185658925)
            ·
              refine ⟨43809167735939603694622097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116824447295838943185658925 43809167735939603694622097)
              ·
                refine ⟨32856875801954702770966573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43809167735939603694622097 32856875801954702770966573)
                ·
                  refine ⟨12321328425733013539112465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32856875801954702770966573 12321328425733013539112465)
                  ·
                    refine ⟨9240996319299760154334349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12321328425733013539112465 9240996319299760154334349)
                    ·
                      refine ⟨3465373619737410057875381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9240996319299760154334349 3465373619737410057875381)
                      ·
                        rfl

theorem cell23_6748791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 2, 3, 2, 3].length) (baseStart_6748791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6748791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6748791 prefixEnd_6748791 := by exact prefixLift 6748791
  have htrace : WordTrace (prefixWord ++ tailWord_6748791) baseStart_6748791 baseEnd_6748791 := by
    simpa [prefixWord, tailWord_6748791, baseEnd_6748791] using wordTrace_append hprefix tailTrace_6748791
  have hstable : (prefixWord ++ tailWord_6748791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6748791).length < 2 ^ (prefixWord ++ tailWord_6748791).sum := by decide
  have hdescent : baseEnd_6748791 < baseStart_6748791 := by decide
  rcases family_descends (prefixWord ++ tailWord_6748791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6748805 : List Nat := [1, 3, 1, 1, 4, 3, 1, 2, 3, 2, 2]
def baseStart_6748805 : Nat := 118140960795 + 6748805 * 2 ^ 59
def prefixEnd_6748805 : Nat := 4983230072969 + 3 ^ 40 * 6748805 * 2
def baseEnd_6748805 : Nat := 3465380808466573003100317

theorem tailTrace_6748805 : CollatzResearch.WordTrace tailWord_6748805 prefixEnd_6748805 3465380808466573003100317 := by
  unfold tailWord_6748805
  simp only [CollatzResearch.WordTrace]
  refine ⟨246149140315239563975607869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164099426876826375983738579 246149140315239563975607869)
  ·
    refine ⟨92305927618214836490852951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 246149140315239563975607869 92305927618214836490852951)
    ·
      refine ⟨138458891427322254736279427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92305927618214836490852951 138458891427322254736279427)
      ·
        refine ⟨207688337140983382104419141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138458891427322254736279427 207688337140983382104419141)
        ·
          refine ⟨38941563213934384144578589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 207688337140983382104419141 38941563213934384144578589)
          ·
            refine ⟨14603086205225394054216971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38941563213934384144578589 14603086205225394054216971)
            ·
              refine ⟨21904629307838091081325457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14603086205225394054216971 21904629307838091081325457)
              ·
                refine ⟨16428471980878568310994093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21904629307838091081325457 16428471980878568310994093)
                ·
                  refine ⟨6160676992829463116622785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16428471980878568310994093 6160676992829463116622785)
                  ·
                    refine ⟨4620507744622097337467089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6160676992829463116622785 4620507744622097337467089)
                    ·
                      refine ⟨3465380808466573003100317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4620507744622097337467089 3465380808466573003100317)
                      ·
                        rfl

theorem cell23_6748805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 2, 3, 2, 2].length) (baseStart_6748805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6748805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6748805 prefixEnd_6748805 := by exact prefixLift 6748805
  have htrace : WordTrace (prefixWord ++ tailWord_6748805) baseStart_6748805 baseEnd_6748805 := by
    simpa [prefixWord, tailWord_6748805, baseEnd_6748805] using wordTrace_append hprefix tailTrace_6748805
  have hstable : (prefixWord ++ tailWord_6748805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6748805).length < 2 ^ (prefixWord ++ tailWord_6748805).sum := by decide
  have hdescent : baseEnd_6748805 < baseStart_6748805 := by decide
  rcases family_descends (prefixWord ++ tailWord_6748805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6748818 : List Nat := [3, 2, 3, 1, 2, 1, 2, 2, 1, 2, 4]
def baseStart_6748818 : Nat := 118140960795 + 6748818 * 2 ^ 59
def prefixEnd_6748818 : Nat := 4983230072969 + 3 ^ 40 * 6748818 * 2
def baseEnd_6748818 : Nat := 3465387483715081452237757

theorem tailTrace_6748818 : CollatzResearch.WordTrace tailWord_6748818 prefixEnd_6748818 3465387483715081452237757 := by
  unfold tailWord_6748818
  simp only [CollatzResearch.WordTrace]
  refine ⟨61537403616048116798957777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164099742976128311463887405 61537403616048116798957777)
  ·
    refine ⟨46153052712036087599218333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61537403616048116798957777 46153052712036087599218333)
    ·
      refine ⟨17307394767013532849706875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46153052712036087599218333 17307394767013532849706875)
      ·
        refine ⟨25961092150520299274560313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17307394767013532849706875 25961092150520299274560313)
        ·
          refine ⟨19470819112890224455920235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25961092150520299274560313 19470819112890224455920235)
          ·
            refine ⟨29206228669335336683880353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19470819112890224455920235 29206228669335336683880353)
            ·
              refine ⟨21904671502001502512910265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29206228669335336683880353 21904671502001502512910265)
              ·
                refine ⟨16428503626501126884682699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21904671502001502512910265 16428503626501126884682699)
                ·
                  refine ⟨24642755439751690327024049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16428503626501126884682699 24642755439751690327024049)
                  ·
                    refine ⟨18482066579813767745268037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24642755439751690327024049 18482066579813767745268037)
                    ·
                      refine ⟨3465387483715081452237757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18482066579813767745268037 3465387483715081452237757)
                      ·
                        rfl

theorem cell23_6748818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_6748818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6748818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6748818 prefixEnd_6748818 := by exact prefixLift 6748818
  have htrace : WordTrace (prefixWord ++ tailWord_6748818) baseStart_6748818 baseEnd_6748818 := by
    simpa [prefixWord, tailWord_6748818, baseEnd_6748818] using wordTrace_append hprefix tailTrace_6748818
  have hstable : (prefixWord ++ tailWord_6748818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6748818).length < 2 ^ (prefixWord ++ tailWord_6748818).sum := by decide
  have hdescent : baseEnd_6748818 < baseStart_6748818 := by decide
  rcases family_descends (prefixWord ++ tailWord_6748818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6748832 : List Nat := [2, 1, 1, 4, 5, 1, 1, 2, 2, 4]
def baseStart_6748832 : Nat := 118140960795 + 6748832 * 2 ^ 59
def prefixEnd_6748832 : Nat := 4983230072969 + 3 ^ 40 * 6748832 * 2
def baseEnd_6748832 : Nat := 1155131557481414799154231

theorem tailTrace_6748832 : CollatzResearch.WordTrace tailWord_6748832 prefixEnd_6748832 1155131557481414799154231 := by
  unfold tailWord_6748832
  simp only [CollatzResearch.WordTrace]
  refine ⟨123075062543070873793420375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164100083390761165057893833 123075062543070873793420375)
  ·
    refine ⟨184612593814606310690130563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123075062543070873793420375 184612593814606310690130563)
    ·
      refine ⟨276918890721909466035195845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184612593814606310690130563 276918890721909466035195845)
      ·
        refine ⟨51922292010358024881599221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 276918890721909466035195845 51922292010358024881599221)
        ·
          refine ⟨4867714875971064832649927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 51922292010358024881599221 4867714875971064832649927)
          ·
            refine ⟨7301572313956597248974891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4867714875971064832649927 7301572313956597248974891)
            ·
              refine ⟨10952358470934895873462337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7301572313956597248974891 10952358470934895873462337)
              ·
                refine ⟨8214268853201171905096753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10952358470934895873462337 8214268853201171905096753)
                ·
                  refine ⟨6160701639900878928822565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8214268853201171905096753 6160701639900878928822565)
                  ·
                    refine ⟨1155131557481414799154231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6160701639900878928822565 1155131557481414799154231)
                    ·
                      rfl

theorem cell23_6748832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 2, 2, 4].length) (baseStart_6748832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6748832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6748832 prefixEnd_6748832 := by exact prefixLift 6748832
  have htrace : WordTrace (prefixWord ++ tailWord_6748832) baseStart_6748832 baseEnd_6748832 := by
    simpa [prefixWord, tailWord_6748832, baseEnd_6748832] using wordTrace_append hprefix tailTrace_6748832
  have hstable : (prefixWord ++ tailWord_6748832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6748832).length < 2 ^ (prefixWord ++ tailWord_6748832).sum := by decide
  have hdescent : baseEnd_6748832 < baseStart_6748832 := by decide
  rcases family_descends (prefixWord ++ tailWord_6748832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6748839 : List Nat := [1, 1, 6, 3, 1, 1, 2, 1, 3, 2, 2]
def baseStart_6748839 : Nat := 118140960795 + 6748839 * 2 ^ 59
def prefixEnd_6748839 : Nat := 4983230072969 + 3 ^ 40 * 6748839 * 2
def baseEnd_6748839 : Nat := 3465398266808825870075161

theorem tailTrace_6748839 : CollatzResearch.WordTrace tailWord_6748839 prefixEnd_6748839 3465398266808825870075161 := by
  unfold tailWord_6748839
  simp only [CollatzResearch.WordTrace]
  refine ⟨246150380397116387782345571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164100253598077591854897047 246150380397116387782345571)
  ·
    refine ⟨369225570595674581673518357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246150380397116387782345571 369225570595674581673518357)
    ·
      refine ⟨17307448621672246015946173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 369225570595674581673518357 17307448621672246015946173)
      ·
        refine ⟨6490293233127092255979815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17307448621672246015946173 6490293233127092255979815)
        ·
          refine ⟨9735439849690638383969723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6490293233127092255979815 9735439849690638383969723)
          ·
            refine ⟨14603159774535957575954585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9735439849690638383969723 14603159774535957575954585)
            ·
              refine ⟨10952369830901968181965939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14603159774535957575954585 10952369830901968181965939)
              ·
                refine ⟨16428554746352952272948909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10952369830901968181965939 16428554746352952272948909)
                ·
                  refine ⟨6160708029882357102355841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16428554746352952272948909 6160708029882357102355841)
                  ·
                    refine ⟨4620531022411767826766881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6160708029882357102355841 4620531022411767826766881)
                    ·
                      refine ⟨3465398266808825870075161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4620531022411767826766881 3465398266808825870075161)
                      ·
                        rfl

theorem cell23_6748839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_6748839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6748839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6748839 prefixEnd_6748839 := by exact prefixLift 6748839
  have htrace : WordTrace (prefixWord ++ tailWord_6748839) baseStart_6748839 baseEnd_6748839 := by
    simpa [prefixWord, tailWord_6748839, baseEnd_6748839] using wordTrace_append hprefix tailTrace_6748839
  have hstable : (prefixWord ++ tailWord_6748839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6748839).length < 2 ^ (prefixWord ++ tailWord_6748839).sum := by decide
  have hdescent : baseEnd_6748839 < baseStart_6748839 := by decide
  rcases family_descends (prefixWord ++ tailWord_6748839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6748855 : List Nat := [1, 1, 3, 1, 6, 2, 1, 1, 1, 3, 3]
def baseStart_6748855 : Nat := 118140960795 + 6748855 * 2 ^ 59
def prefixEnd_6748855 : Nat := 4983230072969 + 3 ^ 40 * 6748855 * 2
def baseEnd_6748855 : Nat := 3465406482499297807475087

theorem tailTrace_6748855 : CollatzResearch.WordTrace tailWord_6748855 prefixEnd_6748855 3465406482499297807475087 := by
  unfold tailWord_6748855
  simp only [CollatzResearch.WordTrace]
  refine ⟨246150963965058422514928019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164100642643372281676618679 246150963965058422514928019)
  ·
    refine ⟨369226445947587633772392029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246150963965058422514928019 369226445947587633772392029)
    ·
      refine ⟨138459917230345362664647011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 369226445947587633772392029 138459917230345362664647011)
      ·
        refine ⟨207689875845518043996970517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138459917230345362664647011 207689875845518043996970517)
        ·
          refine ⟨9735462930258658312357993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 207689875845518043996970517 9735462930258658312357993)
          ·
            refine ⟨7301597197693993734268495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9735462930258658312357993 7301597197693993734268495)
            ·
              refine ⟨10952395796540990601402743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7301597197693993734268495 10952395796540990601402743)
              ·
                refine ⟨16428593694811485902104115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10952395796540990601402743 16428593694811485902104115)
                ·
                  refine ⟨24642890542217228853156173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16428593694811485902104115 24642890542217228853156173)
                  ·
                    refine ⟨9241083953331460819933565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24642890542217228853156173 9241083953331460819933565)
                    ·
                      refine ⟨3465406482499297807475087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9241083953331460819933565 3465406482499297807475087)
                      ·
                        rfl

theorem cell23_6748855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 1, 1, 3, 3].length) (baseStart_6748855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6748855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6748855 prefixEnd_6748855 := by exact prefixLift 6748855
  have htrace : WordTrace (prefixWord ++ tailWord_6748855) baseStart_6748855 baseEnd_6748855 := by
    simpa [prefixWord, tailWord_6748855, baseEnd_6748855] using wordTrace_append hprefix tailTrace_6748855
  have hstable : (prefixWord ++ tailWord_6748855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6748855).length < 2 ^ (prefixWord ++ tailWord_6748855).sum := by decide
  have hdescent : baseEnd_6748855 < baseStart_6748855 := by decide
  rcases family_descends (prefixWord ++ tailWord_6748855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6748881 : List Nat := [1, 2, 2, 1, 2, 3, 3, 1, 2, 1, 5]
def baseStart_6748881 : Nat := 118140960795 + 6748881 * 2 ^ 59
def prefixEnd_6748881 : Nat := 4983230072969 + 3 ^ 40 * 6748881 * 2
def baseEnd_6748881 : Nat := 3465419832996314705749967

theorem tailTrace_6748881 : CollatzResearch.WordTrace tailWord_6748881 prefixEnd_6748881 3465419832996314705749967 := by
  unfold tailWord_6748881
  simp only [CollatzResearch.WordTrace]
  refine ⟨246151912262964228955374497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164101274841976152636916331 246151912262964228955374497)
  ·
    refine ⟨184613934197223171716530873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246151912262964228955374497 184613934197223171716530873)
    ·
      refine ⟨138460450647917378787398155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184613934197223171716530873 138460450647917378787398155)
      ·
        refine ⟨207690675971876068181097233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138460450647917378787398155 207690675971876068181097233)
        ·
          refine ⟨155768006978907051135822925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207690675971876068181097233 155768006978907051135822925)
          ·
            refine ⟨58413002617090144175933597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 155768006978907051135822925 58413002617090144175933597)
            ·
              refine ⟨21904875981408804065975099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58413002617090144175933597 21904875981408804065975099)
              ·
                refine ⟨32857313972113206098962649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21904875981408804065975099 32857313972113206098962649)
                ·
                  refine ⟨24642985479084904574221987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32857313972113206098962649 24642985479084904574221987)
                  ·
                    refine ⟨36964478218627356861332981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24642985479084904574221987 36964478218627356861332981)
                    ·
                      refine ⟨3465419832996314705749967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36964478218627356861332981 3465419832996314705749967)
                      ·
                        rfl

theorem cell23_6748881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 1, 2, 1, 5].length) (baseStart_6748881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6748881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6748881 prefixEnd_6748881 := by exact prefixLift 6748881
  have htrace : WordTrace (prefixWord ++ tailWord_6748881) baseStart_6748881 baseEnd_6748881 := by
    simpa [prefixWord, tailWord_6748881, baseEnd_6748881] using wordTrace_append hprefix tailTrace_6748881
  have hstable : (prefixWord ++ tailWord_6748881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6748881).length < 2 ^ (prefixWord ++ tailWord_6748881).sum := by decide
  have hdescent : baseEnd_6748881 < baseStart_6748881 := by decide
  rcases family_descends (prefixWord ++ tailWord_6748881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6748895 : List Nat := [1, 1, 2, 3, 2, 3, 2, 1, 4, 2, 2]
def baseStart_6748895 : Nat := 118140960795 + 6748895 * 2 ^ 59
def prefixEnd_6748895 : Nat := 4983230072969 + 3 ^ 40 * 6748895 * 2
def baseEnd_6748895 : Nat := 3465427021725477650974903

theorem tailTrace_6748895 : CollatzResearch.WordTrace tailWord_6748895 prefixEnd_6748895 3465427021725477650974903 := by
  unfold tailWord_6748895
  simp only [CollatzResearch.WordTrace]
  refine ⟨246152422884913509346384139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164101615256609006230922759 246152422884913509346384139)
  ·
    refine ⟨369228634327370264019576209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246152422884913509346384139 369228634327370264019576209)
    ·
      refine ⟨276921475745527698014682157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 369228634327370264019576209 276921475745527698014682157)
      ·
        refine ⟨103845553404572886755505809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 276921475745527698014682157 103845553404572886755505809)
        ·
          refine ⟨77884165053429665066629357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103845553404572886755505809 77884165053429665066629357)
          ·
            refine ⟨29206561895036124399986009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77884165053429665066629357 29206561895036124399986009)
            ·
              refine ⟨21904921421277093299989507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29206561895036124399986009 21904921421277093299989507)
              ·
                refine ⟨32857382131915639949984261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21904921421277093299989507 32857382131915639949984261)
                ·
                  refine ⟨6160759149734182490622049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32857382131915639949984261 6160759149734182490622049)
                  ·
                    refine ⟨4620569362300636867966537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6160759149734182490622049 4620569362300636867966537)
                    ·
                      refine ⟨3465427021725477650974903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4620569362300636867966537 3465427021725477650974903)
                      ·
                        rfl

theorem cell23_6748895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 1, 4, 2, 2].length) (baseStart_6748895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6748895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6748895 prefixEnd_6748895 := by exact prefixLift 6748895
  have htrace : WordTrace (prefixWord ++ tailWord_6748895) baseStart_6748895 baseEnd_6748895 := by
    simpa [prefixWord, tailWord_6748895, baseEnd_6748895] using wordTrace_append hprefix tailTrace_6748895
  have hstable : (prefixWord ++ tailWord_6748895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6748895).length < 2 ^ (prefixWord ++ tailWord_6748895).sum := by decide
  have hdescent : baseEnd_6748895 < baseStart_6748895 := by decide
  rcases family_descends (prefixWord ++ tailWord_6748895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6748946 : List Nat := [3, 2, 4, 1, 2, 1, 2, 2, 2, 2, 2]
def baseStart_6748946 : Nat := 118140960795 + 6748946 * 2 ^ 59
def prefixEnd_6748946 : Nat := 4983230072969 + 3 ^ 40 * 6748946 * 2
def baseEnd_6748946 : Nat := 3465453209238856951437169

theorem tailTrace_6748946 : CollatzResearch.WordTrace tailWord_6748946 prefixEnd_6748946 3465453209238856951437169 := by
  unfold tailWord_6748946
  simp only [CollatzResearch.WordTrace]
  refine ⟨61538570751932186264122673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164102855338485830037660461 61538570751932186264122673)
  ·
    refine ⟨46153928063949139698092005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61538570751932186264122673 46153928063949139698092005)
    ·
      refine ⟨8653861511990463693392251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46153928063949139698092005 8653861511990463693392251)
      ·
        refine ⟨12980792267985695540088377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8653861511990463693392251 12980792267985695540088377)
        ·
          refine ⟨9735594200989271655066283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12980792267985695540088377 9735594200989271655066283)
          ·
            refine ⟨14603391301483907482599425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9735594200989271655066283 14603391301483907482599425)
            ·
              refine ⟨10952543476112930611949569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14603391301483907482599425 10952543476112930611949569)
              ·
                refine ⟨8214407607084697958962177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10952543476112930611949569 8214407607084697958962177)
                ·
                  refine ⟨6160805705313523469221633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8214407607084697958962177 6160805705313523469221633)
                  ·
                    refine ⟨4620604278985142601916225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6160805705313523469221633 4620604278985142601916225)
                    ·
                      refine ⟨3465453209238856951437169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4620604278985142601916225 3465453209238856951437169)
                      ·
                        rfl

theorem cell23_6748946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 2, 2, 2, 2].length) (baseStart_6748946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6748946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6748946 prefixEnd_6748946 := by exact prefixLift 6748946
  have htrace : WordTrace (prefixWord ++ tailWord_6748946) baseStart_6748946 baseEnd_6748946 := by
    simpa [prefixWord, tailWord_6748946, baseEnd_6748946] using wordTrace_append hprefix tailTrace_6748946
  have hstable : (prefixWord ++ tailWord_6748946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6748946).length < 2 ^ (prefixWord ++ tailWord_6748946).sum := by decide
  have hdescent : baseEnd_6748946 < baseStart_6748946 := by decide
  rcases family_descends (prefixWord ++ tailWord_6748946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6748968 : List Nat := [2, 1, 5, 1, 1, 1, 2, 2, 1, 3, 4]
def baseStart_6748968 : Nat := 118140960795 + 6748968 * 2 ^ 59
def prefixEnd_6748968 : Nat := 4983230072969 + 3 ^ 40 * 6748968 * 2
def baseEnd_6748968 : Nat := 3465464505813255865362067

theorem tailTrace_6748968 : CollatzResearch.WordTrace tailWord_6748968 prefixEnd_6748968 3465464505813255865362067 := by
  unfold tailWord_6748968
  simp only [CollatzResearch.WordTrace]
  refine ⟨123077542706824521406895779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164103390275766028542527705 123077542706824521406895779)
  ·
    refine ⟨184616314060236782110343669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123077542706824521406895779 184616314060236782110343669)
    ·
      refine ⟨17307779443147198322844719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 184616314060236782110343669 17307779443147198322844719)
      ·
        refine ⟨25961669164720797484267079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17307779443147198322844719 25961669164720797484267079)
        ·
          refine ⟨38942503747081196226400619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25961669164720797484267079 38942503747081196226400619)
          ·
            refine ⟨58413755620621794339600929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38942503747081196226400619 58413755620621794339600929)
            ·
              refine ⟨43810316715466345754700697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58413755620621794339600929 43810316715466345754700697)
              ·
                refine ⟨32857737536599759316025523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43810316715466345754700697 32857737536599759316025523)
                ·
                  refine ⟨49286606304899638974038285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32857737536599759316025523 49286606304899638974038285)
                  ·
                    refine ⟨18482477364337364615264357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49286606304899638974038285 18482477364337364615264357)
                    ·
                      refine ⟨3465464505813255865362067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18482477364337364615264357 3465464505813255865362067)
                      ·
                        rfl

theorem cell23_6748968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_6748968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6748968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6748968 prefixEnd_6748968 := by exact prefixLift 6748968
  have htrace : WordTrace (prefixWord ++ tailWord_6748968) baseStart_6748968 baseEnd_6748968 := by
    simpa [prefixWord, tailWord_6748968, baseEnd_6748968] using wordTrace_append hprefix tailTrace_6748968
  have hstable : (prefixWord ++ tailWord_6748968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6748968).length < 2 ^ (prefixWord ++ tailWord_6748968).sum := by decide
  have hdescent : baseEnd_6748968 < baseStart_6748968 := by decide
  rcases family_descends (prefixWord ++ tailWord_6748968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6749008 : List Nat := [2, 1, 1, 1, 1, 4, 5, 2, 6]
def baseStart_6749008 : Nat := 118140960795 + 6749008 * 2 ^ 59
def prefixEnd_6749008 : Nat := 4983230072969 + 3 ^ 40 * 6749008 * 2
def baseEnd_6749008 : Nat := 385053893893270634317987

theorem tailTrace_6749008 : CollatzResearch.WordTrace tailWord_6749008 prefixEnd_6749008 385053893893270634317987 := by
  unfold tailWord_6749008
  simp only [CollatzResearch.WordTrace]
  refine ⟨123078272166752064822623839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164104362889002753096831785 123078272166752064822623839)
  ·
    refine ⟨184617408250128097233935759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123078272166752064822623839 184617408250128097233935759)
    ·
      refine ⟨276926112375192145850903639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184617408250128097233935759 276926112375192145850903639)
      ·
        refine ⟨415389168562788218776355459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276926112375192145850903639 415389168562788218776355459)
        ·
          refine ⟨623083752844182328164533189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 415389168562788218776355459 623083752844182328164533189)
          ·
            refine ⟨116828203658284186530849973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 623083752844182328164533189 116828203658284186530849973)
            ·
              refine ⟨10952644092964142487267185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 116828203658284186530849973 10952644092964142487267185)
              ·
                refine ⟨8214483069723106865450389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10952644092964142487267185 8214483069723106865450389)
                ·
                  refine ⟨385053893893270634317987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8214483069723106865450389 385053893893270634317987)
                  ·
                    rfl

theorem cell23_6749008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 2, 6].length) (baseStart_6749008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6749008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6749008 prefixEnd_6749008 := by exact prefixLift 6749008
  have htrace : WordTrace (prefixWord ++ tailWord_6749008) baseStart_6749008 baseEnd_6749008 := by
    simpa [prefixWord, tailWord_6749008, baseEnd_6749008] using wordTrace_append hprefix tailTrace_6749008
  have hstable : (prefixWord ++ tailWord_6749008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6749008).length < 2 ^ (prefixWord ++ tailWord_6749008).sum := by decide
  have hdescent : baseEnd_6749008 < baseStart_6749008 := by decide
  rcases family_descends (prefixWord ++ tailWord_6749008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6749012 : List Nat := [2, 4, 1, 1, 4, 1, 2, 1, 3, 4]
def baseStart_6749012 : Nat := 118140960795 + 6749012 * 2 ^ 59
def prefixEnd_6749012 : Nat := 4983230072969 + 3 ^ 40 * 6749012 * 2
def baseEnd_6749012 : Nat := 1155162366320684564403955

theorem tailTrace_6749012 : CollatzResearch.WordTrace tailWord_6749012 prefixEnd_6749012 1155162366320684564403955 := by
  unfold tailWord_6749012
  simp only [CollatzResearch.WordTrace]
  refine ⟨123078345112744819164196645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164104460150326425552262193 123078345112744819164196645)
  ·
    refine ⟨23077189708639653593286871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123078345112744819164196645 23077189708639653593286871)
    ·
      refine ⟨34615784562959480389930307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23077189708639653593286871 34615784562959480389930307)
      ·
        refine ⟨51923676844439220584895461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34615784562959480389930307 51923676844439220584895461)
        ·
          refine ⟨9735689408332353859667899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51923676844439220584895461 9735689408332353859667899)
          ·
            refine ⟨14603534112498530789501849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9735689408332353859667899 14603534112498530789501849)
            ·
              refine ⟨10952650584373898092126387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14603534112498530789501849 10952650584373898092126387)
              ·
                refine ⟨16428975876560847138189581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10952650584373898092126387 16428975876560847138189581)
                ·
                  refine ⟨6160865953710317676821093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16428975876560847138189581 6160865953710317676821093)
                  ·
                    refine ⟨1155162366320684564403955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6160865953710317676821093 1155162366320684564403955)
                    ·
                      rfl

theorem cell23_6749012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 1, 3, 4].length) (baseStart_6749012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6749012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6749012 prefixEnd_6749012 := by exact prefixLift 6749012
  have htrace : WordTrace (prefixWord ++ tailWord_6749012) baseStart_6749012 baseEnd_6749012 := by
    simpa [prefixWord, tailWord_6749012, baseEnd_6749012] using wordTrace_append hprefix tailTrace_6749012
  have hstable : (prefixWord ++ tailWord_6749012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6749012).length < 2 ^ (prefixWord ++ tailWord_6749012).sum := by decide
  have hdescent : baseEnd_6749012 < baseStart_6749012 := by decide
  rcases family_descends (prefixWord ++ tailWord_6749012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6749035 : List Nat := [1, 1, 1, 1, 2, 2, 6, 2, 3, 1, 3]
def baseStart_6749035 : Nat := 118140960795 + 6749035 * 2 ^ 59
def prefixEnd_6749035 : Nat := 4983230072969 + 3 ^ 40 * 6749035 * 2
def baseEnd_6749035 : Nat := 3465498909017107103224259

theorem tailTrace_6749035 : CollatzResearch.WordTrace tailWord_6749035 prefixEnd_6749035 3465498909017107103224259 := by
  unfold tailWord_6749035
  simp only [CollatzResearch.WordTrace]
  refine ⟨246157529104406313256480559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164105019402937542170987039 246157529104406313256480559)
  ·
    refine ⟨369236293656609469884720839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246157529104406313256480559 369236293656609469884720839)
    ·
      refine ⟨553854440484914204827081259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369236293656609469884720839 553854440484914204827081259)
      ·
        refine ⟨830781660727371307240621889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 553854440484914204827081259 830781660727371307240621889)
        ·
          refine ⟨623086245545528480430466417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 830781660727371307240621889 623086245545528480430466417)
          ·
            refine ⟨467314684159146360322849813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 623086245545528480430466417 467314684159146360322849813)
            ·
              refine ⟨21905375819959985640133585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 467314684159146360322849813 21905375819959985640133585)
              ·
                refine ⟨16429031864969989230100189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21905375819959985640133585 16429031864969989230100189)
                ·
                  refine ⟨6160886949363745961287571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16429031864969989230100189 6160886949363745961287571)
                  ·
                    refine ⟨9241330424045618941931357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6160886949363745961287571 9241330424045618941931357)
                    ·
                      refine ⟨3465498909017107103224259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9241330424045618941931357 3465498909017107103224259)
                      ·
                        rfl

theorem cell23_6749035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 2, 3, 1, 3].length) (baseStart_6749035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6749035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6749035 prefixEnd_6749035 := by exact prefixLift 6749035
  have htrace : WordTrace (prefixWord ++ tailWord_6749035) baseStart_6749035 baseEnd_6749035 := by
    simpa [prefixWord, tailWord_6749035, baseEnd_6749035] using wordTrace_append hprefix tailTrace_6749035
  have hstable : (prefixWord ++ tailWord_6749035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6749035).length < 2 ^ (prefixWord ++ tailWord_6749035).sum := by decide
  have hdescent : baseEnd_6749035 < baseStart_6749035 := by decide
  rcases family_descends (prefixWord ++ tailWord_6749035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6749046 : List Nat := [5, 1, 1, 3, 1, 3, 1, 3, 1, 4]
def baseStart_6749046 : Nat := 118140960795 + 6749046 * 2 ^ 59
def prefixEnd_6749046 : Nat := 4983230072969 + 3 ^ 40 * 6749046 * 2
def baseEnd_6749046 : Nat := 1155168185768102186728903

theorem tailTrace_6749046 : CollatzResearch.WordTrace tailWord_6749046 prefixEnd_6749046 1155168185768102186728903 := by
  unfold tailWord_6749046
  simp only [CollatzResearch.WordTrace]
  refine ⟨15384870644210403883445687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 164105286871577641423420661 15384870644210403883445687)
  ·
    refine ⟨23077305966315605825168531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15384870644210403883445687 23077305966315605825168531)
    ·
      refine ⟨34615958949473408737752797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23077305966315605825168531 34615958949473408737752797)
      ·
        refine ⟨12980984606052528276657299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34615958949473408737752797 12980984606052528276657299)
        ·
          refine ⟨19471476909078792414985949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12980984606052528276657299 19471476909078792414985949)
          ·
            refine ⟨7301803840904547155619731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19471476909078792414985949 7301803840904547155619731)
            ·
              refine ⟨10952705761356820733429597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7301803840904547155619731 10952705761356820733429597)
              ·
                refine ⟨4107264660508807775036099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10952705761356820733429597 4107264660508807775036099)
                ·
                  refine ⟨6160896990763211662554149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4107264660508807775036099 6160896990763211662554149)
                  ·
                    refine ⟨1155168185768102186728903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6160896990763211662554149 1155168185768102186728903)
                    ·
                      rfl

theorem cell23_6749046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 3, 1, 4].length) (baseStart_6749046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6749046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6749046 prefixEnd_6749046 := by exact prefixLift 6749046
  have htrace : WordTrace (prefixWord ++ tailWord_6749046) baseStart_6749046 baseEnd_6749046 := by
    simpa [prefixWord, tailWord_6749046, baseEnd_6749046] using wordTrace_append hprefix tailTrace_6749046
  have hstable : (prefixWord ++ tailWord_6749046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6749046).length < 2 ^ (prefixWord ++ tailWord_6749046).sum := by decide
  have hdescent : baseEnd_6749046 < baseStart_6749046 := by decide
  rcases family_descends (prefixWord ++ tailWord_6749046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6749088 : List Nat := [2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 6]
def baseStart_6749088 : Nat := 118140960795 + 6749088 * 2 ^ 59
def prefixEnd_6749088 : Nat := 4983230072969 + 3 ^ 40 * 6749088 * 2
def baseEnd_6749088 : Nat := 3465526123491795395861515

theorem tailTrace_6749088 : CollatzResearch.WordTrace tailWord_6749088 prefixEnd_6749088 3465526123491795395861515 := by
  unfold tailWord_6749088
  simp only [CollatzResearch.WordTrace]
  refine ⟨123079731086607151654079959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164106308115476202205439945 123079731086607151654079959)
  ·
    refine ⟨184619596629910727481119939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123079731086607151654079959 184619596629910727481119939)
    ·
      refine ⟨276929394944866091221679909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184619596629910727481119939 276929394944866091221679909)
      ·
        refine ⟨51924261552162392104064983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 276929394944866091221679909 51924261552162392104064983)
        ·
          refine ⟨77886392328243588156097475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51924261552162392104064983 77886392328243588156097475)
          ·
            refine ⟨116829588492365382234146213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77886392328243588156097475 116829588492365382234146213)
            ·
              refine ⟨21905547842318509168902415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 116829588492365382234146213 21905547842318509168902415)
              ·
                refine ⟨32858321763477763753353623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21905547842318509168902415 32858321763477763753353623)
                ·
                  refine ⟨49287482645216645630030435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32858321763477763753353623 49287482645216645630030435)
                  ·
                    refine ⟨73931223967824968445045653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49287482645216645630030435 73931223967824968445045653)
                    ·
                      refine ⟨3465526123491795395861515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73931223967824968445045653 3465526123491795395861515)
                      ·
                        rfl

theorem cell23_6749088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 6].length) (baseStart_6749088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6749088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6749088 prefixEnd_6749088 := by exact prefixLift 6749088
  have htrace : WordTrace (prefixWord ++ tailWord_6749088) baseStart_6749088 baseEnd_6749088 := by
    simpa [prefixWord, tailWord_6749088, baseEnd_6749088] using wordTrace_append hprefix tailTrace_6749088
  have hstable : (prefixWord ++ tailWord_6749088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6749088).length < 2 ^ (prefixWord ++ tailWord_6749088).sum := by decide
  have hdescent : baseEnd_6749088 < baseStart_6749088 := by decide
  rcases family_descends (prefixWord ++ tailWord_6749088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6749092 : List Nat := [2, 3, 1, 2, 1, 2, 2, 1, 5, 2, 2]
def baseStart_6749092 : Nat := 118140960795 + 6749092 * 2 ^ 59
def prefixEnd_6749092 : Nat := 4983230072969 + 3 ^ 40 * 6749092 * 2
def baseEnd_6749092 : Nat := 3465528177414413380211497

theorem tailTrace_6749092 : CollatzResearch.WordTrace tailWord_6749092 prefixEnd_6749092 3465528177414413380211497 := by
  unfold tailWord_6749092
  simp only [CollatzResearch.WordTrace]
  refine ⟨123079804032599905995652765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164106405376799874660870353 123079804032599905995652765)
  ·
    refine ⟨46154926512224964748369787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123079804032599905995652765 46154926512224964748369787)
    ·
      refine ⟨69232389768337447122554681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46154926512224964748369787 69232389768337447122554681)
      ·
        refine ⟨51924292326253085341916011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69232389768337447122554681 51924292326253085341916011)
        ·
          refine ⟨77886438489379628012874017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51924292326253085341916011 77886438489379628012874017)
          ·
            refine ⟨58414828867034721009655513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77886438489379628012874017 58414828867034721009655513)
            ·
              refine ⟨43811121650276040757241635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58414828867034721009655513 43811121650276040757241635)
              ·
                refine ⟨65716682475414061135862453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43811121650276040757241635 65716682475414061135862453)
                ·
                  refine ⟨6160938982070068231487105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65716682475414061135862453 6160938982070068231487105)
                  ·
                    refine ⟨4620704236552551173615329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6160938982070068231487105 4620704236552551173615329)
                    ·
                      refine ⟨3465528177414413380211497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4620704236552551173615329 3465528177414413380211497)
                      ·
                        rfl

theorem cell23_6749092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 1, 5, 2, 2].length) (baseStart_6749092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6749092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6749092 prefixEnd_6749092 := by exact prefixLift 6749092
  have htrace : WordTrace (prefixWord ++ tailWord_6749092) baseStart_6749092 baseEnd_6749092 := by
    simpa [prefixWord, tailWord_6749092, baseEnd_6749092] using wordTrace_append hprefix tailTrace_6749092
  have hstable : (prefixWord ++ tailWord_6749092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6749092).length < 2 ^ (prefixWord ++ tailWord_6749092).sum := by decide
  have hdescent : baseEnd_6749092 < baseStart_6749092 := by decide
  rcases family_descends (prefixWord ++ tailWord_6749092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6749125 : List Nat := [1, 3, 1, 1, 1, 1, 1, 2, 8, 1, 3]
def baseStart_6749125 : Nat := 118140960795 + 6749125 * 2 ^ 59
def prefixEnd_6749125 : Nat := 4983230072969 + 3 ^ 40 * 6749125 * 2
def baseEnd_6749125 : Nat := 3465545122276011751098845

theorem tailTrace_6749125 : CollatzResearch.WordTrace tailWord_6749125 prefixEnd_6749125 3465545122276011751098845 := by
  unfold tailWord_6749125
  simp only [CollatzResearch.WordTrace]
  refine ⟨246160811674080258627256829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164107207782720172418171219 246160811674080258627256829)
  ·
    refine ⟨92310304377780096985221311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 246160811674080258627256829 92310304377780096985221311)
    ·
      refine ⟨138465456566670145477831967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92310304377780096985221311 138465456566670145477831967)
      ·
        refine ⟨207698184850005218216747951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138465456566670145477831967 207698184850005218216747951)
        ·
          refine ⟨311547277275007827325121927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207698184850005218216747951 311547277275007827325121927)
          ·
            refine ⟨467320915912511740987682891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 311547277275007827325121927 467320915912511740987682891)
            ·
              refine ⟨700981373868767611481524337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 467320915912511740987682891 700981373868767611481524337)
              ·
                refine ⟨525736030401575708611143253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 700981373868767611481524337 525736030401575708611143253)
                ·
                  refine ⟨6160969106268465335286835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 525736030401575708611143253 6160969106268465335286835)
                  ·
                    refine ⟨9241453659402698002930253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6160969106268465335286835 9241453659402698002930253)
                    ·
                      refine ⟨3465545122276011751098845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9241453659402698002930253 3465545122276011751098845)
                      ·
                        rfl

theorem cell23_6749125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 8, 1, 3].length) (baseStart_6749125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6749125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6749125 prefixEnd_6749125 := by exact prefixLift 6749125
  have htrace : WordTrace (prefixWord ++ tailWord_6749125) baseStart_6749125 baseEnd_6749125 := by
    simpa [prefixWord, tailWord_6749125, baseEnd_6749125] using wordTrace_append hprefix tailTrace_6749125
  have hstable : (prefixWord ++ tailWord_6749125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6749125).length < 2 ^ (prefixWord ++ tailWord_6749125).sum := by decide
  have hdescent : baseEnd_6749125 < baseStart_6749125 := by decide
  rcases family_descends (prefixWord ++ tailWord_6749125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6749168 : List Nat := [2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 5]
def baseStart_6749168 : Nat := 118140960795 + 6749168 * 2 ^ 59
def prefixEnd_6749168 : Nat := 4983230072969 + 3 ^ 40 * 6749168 * 2
def baseEnd_6749168 : Nat := 3465567201944155082861147

theorem tailTrace_6749168 : CollatzResearch.WordTrace tailWord_6749168 prefixEnd_6749168 3465567201944155082861147 := by
  unfold tailWord_6749168
  simp only [CollatzResearch.WordTrace]
  refine ⟨123081190006462238485536079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164108253341949651314048105 123081190006462238485536079)
  ·
    refine ⟨184621785009693357728304119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123081190006462238485536079 184621785009693357728304119)
    ·
      refine ⟨276932677514540036592456179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184621785009693357728304119 276932677514540036592456179)
      ·
        refine ⟨415399016271810054888684269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276932677514540036592456179 415399016271810054888684269)
        ·
          refine ⟨155774631101928770583256601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 415399016271810054888684269 155774631101928770583256601)
          ·
            refine ⟨116830973326446577937442451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155774631101928770583256601 116830973326446577937442451)
            ·
              refine ⟨175246459989669866906163677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116830973326446577937442451 175246459989669866906163677)
              ·
                refine ⟨65717422496126200089811379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 175246459989669866906163677 65717422496126200089811379)
                ·
                  refine ⟨98576133744189300134717069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65717422496126200089811379 98576133744189300134717069)
                  ·
                    refine ⟨36966050154070987550518901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 98576133744189300134717069 36966050154070987550518901)
                    ·
                      refine ⟨3465567201944155082861147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36966050154070987550518901 3465567201944155082861147)
                      ·
                        rfl

theorem cell23_6749168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 5].length) (baseStart_6749168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6749168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6749168 prefixEnd_6749168 := by exact prefixLift 6749168
  have htrace : WordTrace (prefixWord ++ tailWord_6749168) baseStart_6749168 baseEnd_6749168 := by
    simpa [prefixWord, tailWord_6749168, baseEnd_6749168] using wordTrace_append hprefix tailTrace_6749168
  have hstable : (prefixWord ++ tailWord_6749168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6749168).length < 2 ^ (prefixWord ++ tailWord_6749168).sum := by decide
  have hdescent : baseEnd_6749168 < baseStart_6749168 := by decide
  rcases family_descends (prefixWord ++ tailWord_6749168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6749169 : List Nat := [1, 2, 2, 2, 4, 2, 1, 3, 1, 3, 2]
def baseStart_6749169 : Nat := 118140960795 + 6749169 * 2 ^ 59
def prefixEnd_6749169 : Nat := 4983230072969 + 3 ^ 40 * 6749169 * 2
def baseEnd_6749169 : Nat := 3465567715424809578948643

theorem tailTrace_6749169 : CollatzResearch.WordTrace tailWord_6749169 prefixEnd_6749169 3465567715424809578948643 := by
  unfold tailWord_6749169
  simp only [CollatzResearch.WordTrace]
  refine ⟨246162416485920854141858561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164108277657280569427905707 246162416485920854141858561)
  ·
    refine ⟨184621812364440640606393921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246162416485920854141858561 184621812364440640606393921)
    ·
      refine ⟨138466359273330480454795441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184621812364440640606393921 138466359273330480454795441)
      ·
        refine ⟨103849769454997860341096581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138466359273330480454795441 103849769454997860341096581)
        ·
          refine ⟨19471831772812098813955609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103849769454997860341096581 19471831772812098813955609)
          ·
            refine ⟨14603873829609074110466707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19471831772812098813955609 14603873829609074110466707)
            ·
              refine ⟨21905810744413611165700061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14603873829609074110466707 21905810744413611165700061)
              ·
                refine ⟨8214679029155104187137523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21905810744413611165700061 8214679029155104187137523)
                ·
                  refine ⟨12322018543732656280706285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8214679029155104187137523 12322018543732656280706285)
                  ·
                    refine ⟨4620756953899746105264857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12322018543732656280706285 4620756953899746105264857)
                    ·
                      refine ⟨3465567715424809578948643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4620756953899746105264857 3465567715424809578948643)
                      ·
                        rfl

theorem cell23_6749169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 3, 1, 3, 2].length) (baseStart_6749169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6749169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6749169 prefixEnd_6749169 := by exact prefixLift 6749169
  have htrace : WordTrace (prefixWord ++ tailWord_6749169) baseStart_6749169 baseEnd_6749169 := by
    simpa [prefixWord, tailWord_6749169, baseEnd_6749169] using wordTrace_append hprefix tailTrace_6749169
  have hstable : (prefixWord ++ tailWord_6749169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6749169).length < 2 ^ (prefixWord ++ tailWord_6749169).sum := by decide
  have hdescent : baseEnd_6749169 < baseStart_6749169 := by decide
  rcases family_descends (prefixWord ++ tailWord_6749169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6749195 : List Nat := [1, 1, 1, 1, 6, 2, 2, 1, 2, 2, 4]
def baseStart_6749195 : Nat := 118140960795 + 6749195 * 2 ^ 59
def prefixEnd_6749195 : Nat := 4983230072969 + 3 ^ 40 * 6749195 * 2
def baseEnd_6749195 : Nat := 3465581065921826477223523

theorem tailTrace_6749195 : CollatzResearch.WordTrace tailWord_6749195 prefixEnd_6749195 3465581065921826477223523 := by
  unfold tailWord_6749195
  simp only [CollatzResearch.WordTrace]
  refine ⟨246163364783826660582305039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164108909855884440388203359 246163364783826660582305039)
  ·
    refine ⟨369245047175739990873457559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246163364783826660582305039 369245047175739990873457559)
    ·
      refine ⟨553867570763609986310186339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369245047175739990873457559 553867570763609986310186339)
      ·
        refine ⟨830801356145414979465279509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 553867570763609986310186339 830801356145414979465279509)
        ·
          refine ⟨38943813569316327162434977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 830801356145414979465279509 38943813569316327162434977)
          ·
            refine ⟨29207860176987245371826233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38943813569316327162434977 29207860176987245371826233)
            ·
              refine ⟨21905895132740434028869675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29207860176987245371826233 21905895132740434028869675)
              ·
                refine ⟨32858842699110651043304513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21905895132740434028869675 32858842699110651043304513)
                ·
                  refine ⟨24644132024332988282478385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32858842699110651043304513 24644132024332988282478385)
                  ·
                    refine ⟨18483099018249741211858789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24644132024332988282478385 18483099018249741211858789)
                    ·
                      refine ⟨3465581065921826477223523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18483099018249741211858789 3465581065921826477223523)
                      ·
                        rfl

theorem cell23_6749195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 1, 2, 2, 4].length) (baseStart_6749195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6749195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6749195 prefixEnd_6749195 := by exact prefixLift 6749195
  have htrace : WordTrace (prefixWord ++ tailWord_6749195) baseStart_6749195 baseEnd_6749195 := by
    simpa [prefixWord, tailWord_6749195, baseEnd_6749195] using wordTrace_append hprefix tailTrace_6749195
  have hstable : (prefixWord ++ tailWord_6749195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6749195).length < 2 ^ (prefixWord ++ tailWord_6749195).sum := by decide
  have hdescent : baseEnd_6749195 < baseStart_6749195 := by decide
  rcases family_descends (prefixWord ++ tailWord_6749195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6749205 : List Nat := [1, 3, 2, 1, 4, 1, 2, 2, 7]
def baseStart_6749205 : Nat := 118140960795 + 6749205 * 2 ^ 59
def prefixEnd_6749205 : Nat := 4983230072969 + 3 ^ 40 * 6749205 * 2
def baseEnd_6749205 : Nat := 385065133414263493122053

theorem tailTrace_6749205 : CollatzResearch.WordTrace tailWord_6749205 prefixEnd_6749205 385065133414263493122053 := by
  unfold tailWord_6749205
  simp only [CollatzResearch.WordTrace]
  refine ⟨246163729513790432290169069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164109153009193621526779379 246163729513790432290169069)
  ·
    refine ⟨92311398567671412108813401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 246163729513790432290169069 92311398567671412108813401)
    ·
      refine ⟨69233548925753559081610051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92311398567671412108813401 69233548925753559081610051)
      ·
        refine ⟨103850323388630338622415077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69233548925753559081610051 103850323388630338622415077)
        ·
          refine ⟨19471935635368188491702827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103850323388630338622415077 19471935635368188491702827)
          ·
            refine ⟨29207903453052282737554241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19471935635368188491702827 29207903453052282737554241)
            ·
              refine ⟨21905927589789212053165681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29207903453052282737554241 21905927589789212053165681)
              ·
                refine ⟨16429445692341909039874261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21905927589789212053165681 16429445692341909039874261)
                ·
                  refine ⟨385065133414263493122053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16429445692341909039874261 385065133414263493122053)
                  ·
                    rfl

theorem cell23_6749205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 2, 7].length) (baseStart_6749205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6749205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6749205 prefixEnd_6749205 := by exact prefixLift 6749205
  have htrace : WordTrace (prefixWord ++ tailWord_6749205) baseStart_6749205 baseEnd_6749205 := by
    simpa [prefixWord, tailWord_6749205, baseEnd_6749205] using wordTrace_append hprefix tailTrace_6749205
  have hstable : (prefixWord ++ tailWord_6749205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6749205).length < 2 ^ (prefixWord ++ tailWord_6749205).sum := by decide
  have hdescent : baseEnd_6749205 < baseStart_6749205 := by decide
  rcases family_descends (prefixWord ++ tailWord_6749205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6749245 : List Nat := [1, 4, 1, 3, 1, 2, 1, 1, 1, 1, 7]
def baseStart_6749245 : Nat := 118140960795 + 6749245 * 2 ^ 59
def prefixEnd_6749245 : Nat := 4983230072969 + 3 ^ 40 * 6749245 * 2
def baseEnd_6749245 : Nat := 3465606739954551281598293

theorem tailTrace_6749245 : CollatzResearch.WordTrace tailWord_6749245 prefixEnd_6749245 3465606739954551281598293 := by
  unfold tailWord_6749245
  simp only [CollatzResearch.WordTrace]
  refine ⟨246165188433645519121625189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164110125622430346081083459 246165188433645519121625189)
  ·
    refine ⟨46155972831308534835304723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 246165188433645519121625189 46155972831308534835304723)
    ·
      refine ⟨69233959246962802252957085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46155972831308534835304723 69233959246962802252957085)
      ·
        refine ⟨25962734717611050844858907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69233959246962802252957085 25962734717611050844858907)
        ·
          refine ⟨38944102076416576267288361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25962734717611050844858907 38944102076416576267288361)
          ·
            refine ⟨29208076557312432200466271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38944102076416576267288361 29208076557312432200466271)
            ·
              refine ⟨43812114835968648300699407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29208076557312432200466271 43812114835968648300699407)
              ·
                refine ⟨65718172253952972451049111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43812114835968648300699407 65718172253952972451049111)
                ·
                  refine ⟨98577258380929458676573667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65718172253952972451049111 98577258380929458676573667)
                  ·
                    refine ⟨147865887571394188014860501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 98577258380929458676573667 147865887571394188014860501)
                    ·
                      refine ⟨3465606739954551281598293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 147865887571394188014860501 3465606739954551281598293)
                      ·
                        rfl

theorem cell23_6749245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_6749245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6749245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6749245 prefixEnd_6749245 := by exact prefixLift 6749245
  have htrace : WordTrace (prefixWord ++ tailWord_6749245) baseStart_6749245 baseEnd_6749245 := by
    simpa [prefixWord, tailWord_6749245, baseEnd_6749245] using wordTrace_append hprefix tailTrace_6749245
  have hstable : (prefixWord ++ tailWord_6749245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6749245).length < 2 ^ (prefixWord ++ tailWord_6749245).sum := by decide
  have hdescent : baseEnd_6749245 < baseStart_6749245 := by decide
  rcases family_descends (prefixWord ++ tailWord_6749245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6749272 : List Nat := [2, 1, 2, 2, 1, 3, 4, 1, 2, 1, 4]
def baseStart_6749272 : Nat := 118140960795 + 6749272 * 2 ^ 59
def prefixEnd_6749272 : Nat := 4983230072969 + 3 ^ 40 * 6749272 * 2
def baseEnd_6749272 : Nat := 3465620603932222675960669

theorem tailTrace_6749272 : CollatzResearch.WordTrace tailWord_6749272 prefixEnd_6749272 3465620603932222675960669 := by
  unfold tailWord_6749272
  simp only [CollatzResearch.WordTrace]
  refine ⟨123083086602273851366429035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164110782136365135155238713 123083086602273851366429035)
  ·
    refine ⟨184624629903410777049643553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123083086602273851366429035 184624629903410777049643553)
    ·
      refine ⟨138468472427558082787232665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184624629903410777049643553 138468472427558082787232665)
      ·
        refine ⟨103851354320668562090424499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138468472427558082787232665 103851354320668562090424499)
        ·
          refine ⟨155777031481002843135636749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103851354320668562090424499 155777031481002843135636749)
          ·
            refine ⟨58416386805376066175863781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 155777031481002843135636749 58416386805376066175863781)
            ·
              refine ⟨10953072526008012407974459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58416386805376066175863781 10953072526008012407974459)
              ·
                refine ⟨16429608789012018611961689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10953072526008012407974459 16429608789012018611961689)
                ·
                  refine ⟨12322206591759013958971267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16429608789012018611961689 12322206591759013958971267)
                  ·
                    refine ⟨18483309887638520938456901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12322206591759013958971267 18483309887638520938456901)
                    ·
                      refine ⟨3465620603932222675960669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18483309887638520938456901 3465620603932222675960669)
                      ·
                        rfl

theorem cell23_6749272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 1, 2, 1, 4].length) (baseStart_6749272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6749272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6749272 prefixEnd_6749272 := by exact prefixLift 6749272
  have htrace : WordTrace (prefixWord ++ tailWord_6749272) baseStart_6749272 baseEnd_6749272 := by
    simpa [prefixWord, tailWord_6749272, baseEnd_6749272] using wordTrace_append hprefix tailTrace_6749272
  have hstable : (prefixWord ++ tailWord_6749272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6749272).length < 2 ^ (prefixWord ++ tailWord_6749272).sum := by decide
  have hdescent : baseEnd_6749272 < baseStart_6749272 := by decide
  rcases family_descends (prefixWord ++ tailWord_6749272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6749285 : List Nat := [1, 3, 1, 3, 2, 1, 2, 1, 2, 1, 6]
def baseStart_6749285 : Nat := 118140960795 + 6749285 * 2 ^ 59
def prefixEnd_6749285 : Nat := 4983230072969 + 3 ^ 40 * 6749285 * 2
def baseEnd_6749285 : Nat := 3465627279180731125098109

theorem tailTrace_6749285 : CollatzResearch.WordTrace tailWord_6749285 prefixEnd_6749285 3465627279180731125098109 := by
  unfold tailWord_6749285
  simp only [CollatzResearch.WordTrace]
  refine ⟨246166647353500605953081309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164111098235667070635387539 246166647353500605953081309)
  ·
    refine ⟨92312492757562727232405491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 246166647353500605953081309 92312492757562727232405491)
    ·
      refine ⟨138468739136344090848608237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92312492757562727232405491 138468739136344090848608237)
      ·
        refine ⟨51925777176129034068228089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138468739136344090848608237 51925777176129034068228089)
        ·
          refine ⟨38944332882096775551171067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51925777176129034068228089 38944332882096775551171067)
          ·
            refine ⟨58416499323145163326756601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38944332882096775551171067 58416499323145163326756601)
            ·
              refine ⟨43812374492358872495067451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58416499323145163326756601 43812374492358872495067451)
              ·
                refine ⟨65718561738538308742601177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43812374492358872495067451 65718561738538308742601177)
                ·
                  refine ⟨49288921303903731556950883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65718561738538308742601177 49288921303903731556950883)
                  ·
                    refine ⟨73933381955855597335426325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49288921303903731556950883 73933381955855597335426325)
                    ·
                      refine ⟨3465627279180731125098109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73933381955855597335426325 3465627279180731125098109)
                      ·
                        rfl

theorem cell23_6749285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_6749285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6749285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6749285 prefixEnd_6749285 := by exact prefixLift 6749285
  have htrace : WordTrace (prefixWord ++ tailWord_6749285) baseStart_6749285 baseEnd_6749285 := by
    simpa [prefixWord, tailWord_6749285, baseEnd_6749285] using wordTrace_append hprefix tailTrace_6749285
  have hstable : (prefixWord ++ tailWord_6749285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6749285).length < 2 ^ (prefixWord ++ tailWord_6749285).sum := by decide
  have hdescent : baseEnd_6749285 < baseStart_6749285 := by decide
  rcases family_descends (prefixWord ++ tailWord_6749285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6749292 : List Nat := [2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 3]
def baseStart_6749292 : Nat := 118140960795 + 6749292 * 2 ^ 59
def prefixEnd_6749292 : Nat := 4983230072969 + 3 ^ 40 * 6749292 * 2
def baseEnd_6749292 : Nat := 3465630873545312597710577

theorem tailTrace_6749292 : CollatzResearch.WordTrace tailWord_6749292 prefixEnd_6749292 3465630873545312597710577 := by
  unfold tailWord_6749292
  simp only [CollatzResearch.WordTrace]
  refine ⟨123083451332237623074293065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164111268442983497432390753 123083451332237623074293065)
  ·
    refine ⟨92312588499178217305719799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123083451332237623074293065 92312588499178217305719799)
    ·
      refine ⟨138468882748767325958579699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92312588499178217305719799 138468882748767325958579699)
      ·
        refine ⟨207703324123150988937869549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138468882748767325958579699 207703324123150988937869549)
        ·
          refine ⟨77888746546181620851701081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 207703324123150988937869549 77888746546181620851701081)
          ·
            refine ⟨58416559909636215638775811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77888746546181620851701081 58416559909636215638775811)
            ·
              refine ⟨87624839864454323458163717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58416559909636215638775811 87624839864454323458163717)
              ·
                refine ⟨16429657474585185648405697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87624839864454323458163717 16429657474585185648405697)
                ·
                  refine ⟨12322243105938889236304273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16429657474585185648405697 12322243105938889236304273)
                  ·
                    refine ⟨9241682329454166927228205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12322243105938889236304273 9241682329454166927228205)
                    ·
                      refine ⟨3465630873545312597710577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9241682329454166927228205 3465630873545312597710577)
                      ·
                        rfl

theorem cell23_6749292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 3].length) (baseStart_6749292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6749292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6749292 prefixEnd_6749292 := by exact prefixLift 6749292
  have htrace : WordTrace (prefixWord ++ tailWord_6749292) baseStart_6749292 baseEnd_6749292 := by
    simpa [prefixWord, tailWord_6749292, baseEnd_6749292] using wordTrace_append hprefix tailTrace_6749292
  have hstable : (prefixWord ++ tailWord_6749292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6749292).length < 2 ^ (prefixWord ++ tailWord_6749292).sum := by decide
  have hdescent : baseEnd_6749292 < baseStart_6749292 := by decide
  rcases family_descends (prefixWord ++ tailWord_6749292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6749326 : List Nat := [4, 1, 1, 3, 2, 3, 1, 1, 2, 2, 3]
def baseStart_6749326 : Nat := 118140960795 + 6749326 * 2 ^ 59
def prefixEnd_6749326 : Nat := 4983230072969 + 3 ^ 40 * 6749326 * 2
def baseEnd_6749326 : Nat := 3465648331887565464685421

theorem tailTrace_6749326 : CollatzResearch.WordTrace tailWord_6749326 prefixEnd_6749326 3465648331887565464685421 := by
  unfold tailWord_6749326
  simp only [CollatzResearch.WordTrace]
  refine ⟨30771017843294008744415479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164112095164234713303549221 30771017843294008744415479)
  ·
    refine ⟨46156526764941013116623219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30771017843294008744415479 46156526764941013116623219)
    ·
      refine ⟨69234790147411519674934829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46156526764941013116623219 69234790147411519674934829)
      ·
        refine ⟨25963046305279319878100561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69234790147411519674934829 25963046305279319878100561)
        ·
          refine ⟨19472284728959489908575421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25963046305279319878100561 19472284728959489908575421)
          ·
            refine ⟨7302106773359808715715783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19472284728959489908575421 7302106773359808715715783)
            ·
              refine ⟨10953160160039713073573675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7302106773359808715715783 10953160160039713073573675)
              ·
                refine ⟨16429740240059569610360513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10953160160039713073573675 16429740240059569610360513)
                ·
                  refine ⟨12322305180044677207770385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16429740240059569610360513 12322305180044677207770385)
                  ·
                    refine ⟨9241728885033507905827789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12322305180044677207770385 9241728885033507905827789)
                    ·
                      refine ⟨3465648331887565464685421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9241728885033507905827789 3465648331887565464685421)
                      ·
                        rfl

theorem cell23_6749326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 1, 2, 2, 3].length) (baseStart_6749326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6749326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6749326 prefixEnd_6749326 := by exact prefixLift 6749326
  have htrace : WordTrace (prefixWord ++ tailWord_6749326) baseStart_6749326 baseEnd_6749326 := by
    simpa [prefixWord, tailWord_6749326, baseEnd_6749326] using wordTrace_append hprefix tailTrace_6749326
  have hstable : (prefixWord ++ tailWord_6749326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6749326).length < 2 ^ (prefixWord ++ tailWord_6749326).sum := by decide
  have hdescent : baseEnd_6749326 < baseStart_6749326 := by decide
  rcases family_descends (prefixWord ++ tailWord_6749326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6749346 : List Nat := [3, 3, 1, 3, 2, 2, 1, 2, 6]
def baseStart_6749346 : Nat := 118140960795 + 6749346 * 2 ^ 59
def prefixEnd_6749346 : Nat := 4983230072969 + 3 ^ 40 * 6749346 * 2
def baseEnd_6749346 : Nat := 385073177944517265159481

theorem tailTrace_6749346 : CollatzResearch.WordTrace tailWord_6749346 prefixEnd_6749346 385073177944517265159481 := by
  unfold tailWord_6749346
  simp only [CollatzResearch.WordTrace]
  refine ⟨61542218051569903342762973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164112581470853075580701261 61542218051569903342762973)
  ·
    refine ⟨23078331769338713753536115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61542218051569903342762973 23078331769338713753536115)
    ·
      refine ⟨34617497654008070630304173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23078331769338713753536115 34617497654008070630304173)
      ·
        refine ⟨12981561620253026486364065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34617497654008070630304173 12981561620253026486364065)
        ·
          refine ⟨9736171215189769864773049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12981561620253026486364065 9736171215189769864773049)
          ·
            refine ⟨7302128411392327398579787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9736171215189769864773049 7302128411392327398579787)
            ·
              refine ⟨10953192617088491097869681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7302128411392327398579787 10953192617088491097869681)
              ·
                refine ⟨8214894462816368323402261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10953192617088491097869681 8214894462816368323402261)
                ·
                  refine ⟨385073177944517265159481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8214894462816368323402261 385073177944517265159481)
                  ·
                    rfl

theorem cell23_6749346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 2, 6].length) (baseStart_6749346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6749346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6749346 prefixEnd_6749346 := by exact prefixLift 6749346
  have htrace : WordTrace (prefixWord ++ tailWord_6749346) baseStart_6749346 baseEnd_6749346 := by
    simpa [prefixWord, tailWord_6749346, baseEnd_6749346] using wordTrace_append hprefix tailTrace_6749346
  have hstable : (prefixWord ++ tailWord_6749346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6749346).length < 2 ^ (prefixWord ++ tailWord_6749346).sum := by decide
  have hdescent : baseEnd_6749346 < baseStart_6749346 := by decide
  rcases family_descends (prefixWord ++ tailWord_6749346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6749379 : List Nat := [1, 1, 1, 3, 1, 1, 1, 5, 5, 2, 2]
def baseStart_6749379 : Nat := 118140960795 + 6749379 * 2 ^ 59
def prefixEnd_6749379 : Nat := 4983230072969 + 3 ^ 40 * 6749379 * 2
def baseEnd_6749379 : Nat := 3465675546362253757322677

theorem tailTrace_6749379 : CollatzResearch.WordTrace tailWord_6749379 prefixEnd_6749379 3465675546362253757322677 := by
  unfold tailWord_6749379
  simp only [CollatzResearch.WordTrace]
  refine ⟨246170075815160060007003191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164113383876773373338002127 246170075815160060007003191)
  ·
    refine ⟨369255113722740090010504787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246170075815160060007003191 369255113722740090010504787)
    ·
      refine ⟨553882670584110135015757181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369255113722740090010504787 553882670584110135015757181)
      ·
        refine ⟨207706001469041300630908943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 553882670584110135015757181 207706001469041300630908943)
        ·
          refine ⟨311559002203561950946363415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207706001469041300630908943 311559002203561950946363415)
          ·
            refine ⟨467338503305342926419545123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 311559002203561950946363415 467338503305342926419545123)
            ·
              refine ⟨701007754958014389629317685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 467338503305342926419545123 701007754958014389629317685)
              ·
                refine ⟨65719477027313849027748533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 701007754958014389629317685 65719477027313849027748533)
                ·
                  refine ⟨6161200971310673346351425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65719477027313849027748533 6161200971310673346351425)
                  ·
                    refine ⟨4620900728483005009763569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6161200971310673346351425 4620900728483005009763569)
                    ·
                      refine ⟨3465675546362253757322677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4620900728483005009763569 3465675546362253757322677)
                      ·
                        rfl

theorem cell23_6749379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 5, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 5, 5, 2, 2].length) (baseStart_6749379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6749379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6749379 prefixEnd_6749379 := by exact prefixLift 6749379
  have htrace : WordTrace (prefixWord ++ tailWord_6749379) baseStart_6749379 baseEnd_6749379 := by
    simpa [prefixWord, tailWord_6749379, baseEnd_6749379] using wordTrace_append hprefix tailTrace_6749379
  have hstable : (prefixWord ++ tailWord_6749379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6749379).length < 2 ^ (prefixWord ++ tailWord_6749379).sum := by decide
  have hdescent : baseEnd_6749379 < baseStart_6749379 := by decide
  rcases family_descends (prefixWord ++ tailWord_6749379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6749390 : List Nat := [4, 1, 1, 1, 5, 2, 1, 3, 1, 1, 3]
def baseStart_6749390 : Nat := 118140960795 + 6749390 * 2 ^ 59
def prefixEnd_6749390 : Nat := 4983230072969 + 3 ^ 40 * 6749390 * 2
def baseEnd_6749390 : Nat := 3465681194649453214285127

theorem tailTrace_6749390 : CollatzResearch.WordTrace tailWord_6749390 prefixEnd_6749390 3465681194649453214285127 := by
  unfold tailWord_6749390
  simp only [CollatzResearch.WordTrace]
  refine ⟨30771309627265026110706703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164113651345413472590435749 30771309627265026110706703)
  ·
    refine ⟨46156964440897539166060055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30771309627265026110706703 46156964440897539166060055)
    ·
      refine ⟨69235446661346308749090083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46156964440897539166060055 69235446661346308749090083)
      ·
        refine ⟨103853169992019463123635125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69235446661346308749090083 103853169992019463123635125)
        ·
          refine ⟨9736234686751824667840793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 103853169992019463123635125 9736234686751824667840793)
          ·
            refine ⟨7302176015063868500880595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9736234686751824667840793 7302176015063868500880595)
            ·
              refine ⟨10953264022595802751320893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7302176015063868500880595 10953264022595802751320893)
              ·
                refine ⟨4107474008473426031745335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10953264022595802751320893 4107474008473426031745335)
                ·
                  refine ⟨6161211012710139047618003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4107474008473426031745335 6161211012710139047618003)
                  ·
                    refine ⟨9241816519065208571427005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6161211012710139047618003 9241816519065208571427005)
                    ·
                      refine ⟨3465681194649453214285127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9241816519065208571427005 3465681194649453214285127)
                      ·
                        rfl

theorem cell23_6749390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 3, 1, 1, 3].length) (baseStart_6749390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6749390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6749390 prefixEnd_6749390 := by exact prefixLift 6749390
  have htrace : WordTrace (prefixWord ++ tailWord_6749390) baseStart_6749390 baseEnd_6749390 := by
    simpa [prefixWord, tailWord_6749390, baseEnd_6749390] using wordTrace_append hprefix tailTrace_6749390
  have hstable : (prefixWord ++ tailWord_6749390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6749390).length < 2 ^ (prefixWord ++ tailWord_6749390).sum := by decide
  have hdescent : baseEnd_6749390 < baseStart_6749390 := by decide
  rcases family_descends (prefixWord ++ tailWord_6749390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6749399 : List Nat := [1, 1, 3, 2, 1, 2, 4, 3, 1, 2, 3]
def baseStart_6749399 : Nat := 118140960795 + 6749399 * 2 ^ 59
def prefixEnd_6749399 : Nat := 4983230072969 + 3 ^ 40 * 6749399 * 2
def baseEnd_6749399 : Nat := 3465685815975343679072585

theorem tailTrace_6749399 : CollatzResearch.WordTrace tailWord_6749399 prefixEnd_6749399 3465685815975343679072585 := by
  unfold tailWord_6749399
  simp only [CollatzResearch.WordTrace]
  refine ⟨246170805275087603422731251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164113870183391735615154167 246170805275087603422731251)
  ·
    refine ⟨369256207912631405134096877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246170805275087603422731251 369256207912631405134096877)
    ·
      refine ⟨138471077967236776925286329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 369256207912631405134096877 138471077967236776925286329)
      ·
        refine ⟨103853308475427582693964747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138471077967236776925286329 103853308475427582693964747)
        ·
          refine ⟨155779962713141374040947121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103853308475427582693964747 155779962713141374040947121)
          ·
            refine ⟨116834972034856030530710341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155779962713141374040947121 116834972034856030530710341)
            ·
              refine ⟨21906557256535505724508189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 116834972034856030530710341 21906557256535505724508189)
              ·
                refine ⟨8214958971200814646690571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21906557256535505724508189 8214958971200814646690571)
                ·
                  refine ⟨12322438456801221970035857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8214958971200814646690571 12322438456801221970035857)
                  ·
                    refine ⟨9241828842600916477526893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12322438456801221970035857 9241828842600916477526893)
                    ·
                      refine ⟨3465685815975343679072585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9241828842600916477526893 3465685815975343679072585)
                      ·
                        rfl

theorem cell23_6749399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 3, 1, 2, 3].length) (baseStart_6749399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6749399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6749399 prefixEnd_6749399 := by exact prefixLift 6749399
  have htrace : WordTrace (prefixWord ++ tailWord_6749399) baseStart_6749399 baseEnd_6749399 := by
    simpa [prefixWord, tailWord_6749399, baseEnd_6749399] using wordTrace_append hprefix tailTrace_6749399
  have hstable : (prefixWord ++ tailWord_6749399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6749399).length < 2 ^ (prefixWord ++ tailWord_6749399).sum := by decide
  have hdescent : baseEnd_6749399 < baseStart_6749399 := by decide
  rcases family_descends (prefixWord ++ tailWord_6749399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6749423 : List Nat := [1, 1, 2, 1, 7, 2, 2, 1, 2, 4]
def baseStart_6749423 : Nat := 118140960795 + 6749423 * 2 ^ 59
def prefixEnd_6749423 : Nat := 4983230072969 + 3 ^ 40 * 6749423 * 2
def baseEnd_6749423 : Nat := 1155232713170350528390825

theorem tailTrace_6749423 : CollatzResearch.WordTrace tailWord_6749423 prefixEnd_6749423 1155232713170350528390825 := by
  unfold tailWord_6749423
  simp only [CollatzResearch.WordTrace]
  refine ⟨246171680627000655521604923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164114453751333770347736615 246171680627000655521604923)
  ·
    refine ⟨369257520940500983282407385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246171680627000655521604923 369257520940500983282407385)
    ·
      refine ⟨276943140705375737461805539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 369257520940500983282407385 276943140705375737461805539)
      ·
        refine ⟨415414711058063606192708309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276943140705375737461805539 415414711058063606192708309)
        ·
          refine ⟨9736282290423365770141601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 415414711058063606192708309 9736282290423365770141601)
          ·
            refine ⟨7302211717817524327606201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9736282290423365770141601 7302211717817524327606201)
            ·
              refine ⟨5476658788363143245704651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7302211717817524327606201 5476658788363143245704651)
              ·
                refine ⟨8214988182544714868556977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5476658788363143245704651 8214988182544714868556977)
                ·
                  refine ⟨6161241136908536151417733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8214988182544714868556977 6161241136908536151417733)
                  ·
                    refine ⟨1155232713170350528390825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6161241136908536151417733 1155232713170350528390825)
                    ·
                      rfl

theorem cell23_6749423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 2, 1, 2, 4].length) (baseStart_6749423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6749423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6749423 prefixEnd_6749423 := by exact prefixLift 6749423
  have htrace : WordTrace (prefixWord ++ tailWord_6749423) baseStart_6749423 baseEnd_6749423 := by
    simpa [prefixWord, tailWord_6749423, baseEnd_6749423] using wordTrace_append hprefix tailTrace_6749423
  have hstable : (prefixWord ++ tailWord_6749423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6749423).length < 2 ^ (prefixWord ++ tailWord_6749423).sum := by decide
  have hdescent : baseEnd_6749423 < baseStart_6749423 := by decide
  rcases family_descends (prefixWord ++ tailWord_6749423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6749469 : List Nat := [1, 4, 2, 3, 1, 1, 1, 1, 2, 3, 4]
def baseStart_6749469 : Nat := 118140960795 + 6749469 * 2 ^ 59
def prefixEnd_6749469 : Nat := 4983230072969 + 3 ^ 40 * 6749469 * 2
def baseEnd_6749469 : Nat := 3465721759621158405197263

theorem tailTrace_6749469 : CollatzResearch.WordTrace tailWord_6749469 prefixEnd_6749469 3465721759621158405197263 := by
  unfold tailWord_6749469
  simp only [CollatzResearch.WordTrace]
  refine ⟨246173358384834005377779461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164115572256556003585186307 246173358384834005377779461)
  ·
    refine ⟨46157504697156376008333649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 246173358384834005377779461 46157504697156376008333649)
    ·
      refine ⟨34618128522867282006250237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46157504697156376008333649 34618128522867282006250237)
      ·
        refine ⟨12981798196075230752343839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34618128522867282006250237 12981798196075230752343839)
        ·
          refine ⟨19472697294112846128515759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12981798196075230752343839 19472697294112846128515759)
          ·
            refine ⟨29209045941169269192773639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19472697294112846128515759 29209045941169269192773639)
            ·
              refine ⟨43813568911753903789160459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29209045941169269192773639 43813568911753903789160459)
              ·
                refine ⟨65720353367630855683740689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43813568911753903789160459 65720353367630855683740689)
                ·
                  refine ⟨49290265025723141762805517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65720353367630855683740689 49290265025723141762805517)
                  ·
                    refine ⟨18483849384646178161052069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49290265025723141762805517 18483849384646178161052069)
                    ·
                      refine ⟨3465721759621158405197263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18483849384646178161052069 3465721759621158405197263)
                      ·
                        rfl

theorem cell23_6749469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_6749469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6749469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6749469 prefixEnd_6749469 := by exact prefixLift 6749469
  have htrace : WordTrace (prefixWord ++ tailWord_6749469) baseStart_6749469 baseEnd_6749469 := by
    simpa [prefixWord, tailWord_6749469, baseEnd_6749469] using wordTrace_append hprefix tailTrace_6749469
  have hstable : (prefixWord ++ tailWord_6749469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6749469).length < 2 ^ (prefixWord ++ tailWord_6749469).sum := by decide
  have hdescent : baseEnd_6749469 < baseStart_6749469 := by decide
  rcases family_descends (prefixWord ++ tailWord_6749469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6749529 : List Nat := [1, 2, 1, 2, 2, 2, 2, 1, 1, 7, 2]
def baseStart_6749529 : Nat := 118140960795 + 6749529 * 2 ^ 59
def prefixEnd_6749529 : Nat := 4983230072969 + 3 ^ 40 * 6749529 * 2
def baseEnd_6749529 : Nat := 3465752568460428170446987

theorem tailTrace_6749529 : CollatzResearch.WordTrace tailWord_6749529 prefixEnd_6749529 3465752568460428170446987 := by
  unfold tailWord_6749529
  simp only [CollatzResearch.WordTrace]
  refine ⟨246175546764616635624963641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164117031176411090416642427 246175546764616635624963641)
  ·
    refine ⟨184631660073462476718722731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246175546764616635624963641 184631660073462476718722731)
    ·
      refine ⟨276947490110193715078084097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184631660073462476718722731 276947490110193715078084097)
      ·
        refine ⟨207710617582645286308563073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 276947490110193715078084097 207710617582645286308563073)
        ·
          refine ⟨155782963186983964731422305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207710617582645286308563073 155782963186983964731422305)
          ·
            refine ⟨116837222390237973548566729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155782963186983964731422305 116837222390237973548566729)
            ·
              refine ⟨87627916792678480161425047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116837222390237973548566729 87627916792678480161425047)
              ·
                refine ⟨131441875189017720242137571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87627916792678480161425047 131441875189017720242137571)
                ·
                  refine ⟨197162812783526580363206357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 131441875189017720242137571 197162812783526580363206357)
                  ·
                    refine ⟨4621003424613904227262649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 197162812783526580363206357 4621003424613904227262649)
                    ·
                      refine ⟨3465752568460428170446987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4621003424613904227262649 3465752568460428170446987)
                      ·
                        rfl

theorem cell23_6749529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 7, 2].length) (baseStart_6749529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6749529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6749529 prefixEnd_6749529 := by exact prefixLift 6749529
  have htrace : WordTrace (prefixWord ++ tailWord_6749529) baseStart_6749529 baseEnd_6749529 := by
    simpa [prefixWord, tailWord_6749529, baseEnd_6749529] using wordTrace_append hprefix tailTrace_6749529
  have hstable : (prefixWord ++ tailWord_6749529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6749529).length < 2 ^ (prefixWord ++ tailWord_6749529).sum := by decide
  have hdescent : baseEnd_6749529 < baseStart_6749529 := by decide
  rcases family_descends (prefixWord ++ tailWord_6749529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6749552 : List Nat := [2, 1, 1, 1, 4, 2, 1, 1, 2, 8]
def baseStart_6749552 : Nat := 118140960795 + 6749552 * 2 ^ 59
def prefixEnd_6749552 : Nat := 4983230072969 + 3 ^ 40 * 6749552 * 2
def baseEnd_6749552 : Nat := 1155254792838493860153127

theorem tailTrace_6749552 : CollatzResearch.WordTrace tailWord_6749552 prefixEnd_6749552 1155254792838493860153127 := by
  unfold tailWord_6749552
  simp only [CollatzResearch.WordTrace]
  refine ⟨123088192821766655276525455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164117590429022207035367273 123088192821766655276525455)
  ·
    refine ⟨184632289232649982914788183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123088192821766655276525455 184632289232649982914788183)
    ·
      refine ⟨276948433848974974372182275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184632289232649982914788183 276948433848974974372182275)
      ·
        refine ⟨415422650773462461558273413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276948433848974974372182275 415422650773462461558273413)
        ·
          refine ⟨77891747020024211542176265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 415422650773462461558273413 77891747020024211542176265)
          ·
            refine ⟨58418810265018158656632199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77891747020024211542176265 58418810265018158656632199)
            ·
              refine ⟨87628215397527237984948299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58418810265018158656632199 87628215397527237984948299)
              ·
                refine ⟨131442323096290856977422449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87628215397527237984948299 131442323096290856977422449)
                ·
                  refine ⟨98581742322218142733066837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 131442323096290856977422449 98581742322218142733066837)
                  ·
                    refine ⟨1155254792838493860153127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 98581742322218142733066837 1155254792838493860153127)
                    ·
                      rfl

theorem cell23_6749552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 2, 8].length) (baseStart_6749552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6749552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6749552 prefixEnd_6749552 := by exact prefixLift 6749552
  have htrace : WordTrace (prefixWord ++ tailWord_6749552) baseStart_6749552 baseEnd_6749552 := by
    simpa [prefixWord, tailWord_6749552, baseEnd_6749552] using wordTrace_append hprefix tailTrace_6749552
  have hstable : (prefixWord ++ tailWord_6749552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6749552).length < 2 ^ (prefixWord ++ tailWord_6749552).sum := by decide
  have hdescent : baseEnd_6749552 < baseStart_6749552 := by decide
  rcases family_descends (prefixWord ++ tailWord_6749552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6749559 : List Nat := [1, 1, 3, 1, 1, 2, 4, 3, 2, 1, 4]
def baseStart_6749559 : Nat := 118140960795 + 6749559 * 2 ^ 59
def prefixEnd_6749559 : Nat := 4983230072969 + 3 ^ 40 * 6749559 * 2
def baseEnd_6749559 : Nat := 3465767972880063053071849

theorem tailTrace_6749559 : CollatzResearch.WordTrace tailWord_6749559 prefixEnd_6749559 3465767972880063053071849 := by
  unfold tailWord_6749559
  simp only [CollatzResearch.WordTrace]
  refine ⟨246176640954507950748555731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164117760636338633832370487 246176640954507950748555731)
  ·
    refine ⟨369264961431761926122833597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246176640954507950748555731 369264961431761926122833597)
    ·
      refine ⟨138474360536910722296062599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 369264961431761926122833597 138474360536910722296062599)
      ·
        refine ⟨207711540805366083444093899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138474360536910722296062599 207711540805366083444093899)
        ·
          refine ⟨311567311208049125166140849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207711540805366083444093899 311567311208049125166140849)
          ·
            refine ⟨233675483406036843874605637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 311567311208049125166140849 233675483406036843874605637)
            ·
              refine ⟨43814153138631908226488557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 233675483406036843874605637 43814153138631908226488557)
              ·
                refine ⟨16430307426986965584933209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43814153138631908226488557 16430307426986965584933209)
                ·
                  refine ⟨12322730570240224188699907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16430307426986965584933209 12322730570240224188699907)
                  ·
                    refine ⟨18484095855360336283049861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12322730570240224188699907 18484095855360336283049861)
                    ·
                      refine ⟨3465767972880063053071849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18484095855360336283049861 3465767972880063053071849)
                      ·
                        rfl

theorem cell23_6749559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 2, 1, 4].length) (baseStart_6749559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6749559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6749559 prefixEnd_6749559 := by exact prefixLift 6749559
  have htrace : WordTrace (prefixWord ++ tailWord_6749559) baseStart_6749559 baseEnd_6749559 := by
    simpa [prefixWord, tailWord_6749559, baseEnd_6749559] using wordTrace_append hprefix tailTrace_6749559
  have hstable : (prefixWord ++ tailWord_6749559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6749559).length < 2 ^ (prefixWord ++ tailWord_6749559).sum := by decide
  have hdescent : baseEnd_6749559 < baseStart_6749559 := by decide
  rcases family_descends (prefixWord ++ tailWord_6749559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6749576 : List Nat := [2, 1, 3, 3, 1, 3, 1, 2, 2, 1, 4]
def baseStart_6749576 : Nat := 118140960795 + 6749576 * 2 ^ 59
def prefixEnd_6749576 : Nat := 4983230072969 + 3 ^ 40 * 6749576 * 2
def baseEnd_6749576 : Nat := 3465776702051189486559271

theorem tailTrace_6749576 : CollatzResearch.WordTrace tailWord_6749576 prefixEnd_6749576 3465776702051189486559271 := by
  unfold tailWord_6749576
  simp only [CollatzResearch.WordTrace]
  refine ⟨123088630497723181325962291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164118173996964241767949721 123088630497723181325962291)
  ·
    refine ⟨184632945746584771988943437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123088630497723181325962291 184632945746584771988943437)
    ·
      refine ⟨69237354654969289495853789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184632945746584771988943437 69237354654969289495853789)
      ·
        refine ⟨25964007995613483560945171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69237354654969289495853789 25964007995613483560945171)
        ·
          refine ⟨38946011993420225341417757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25964007995613483560945171 38946011993420225341417757)
          ·
            refine ⟨14604754497532584503031659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38946011993420225341417757 14604754497532584503031659)
            ·
              refine ⟨21907131746298876754547489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14604754497532584503031659 21907131746298876754547489)
              ·
                refine ⟨16430348809724157565910617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21907131746298876754547489 16430348809724157565910617)
                ·
                  refine ⟨12322761607293118174432963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16430348809724157565910617 12322761607293118174432963)
                  ·
                    refine ⟨18484142410939677261649445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12322761607293118174432963 18484142410939677261649445)
                    ·
                      refine ⟨3465776702051189486559271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18484142410939677261649445 3465776702051189486559271)
                      ·
                        rfl

theorem cell23_6749576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_6749576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6749576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6749576 prefixEnd_6749576 := by exact prefixLift 6749576
  have htrace : WordTrace (prefixWord ++ tailWord_6749576) baseStart_6749576 baseEnd_6749576 := by
    simpa [prefixWord, tailWord_6749576, baseEnd_6749576] using wordTrace_append hprefix tailTrace_6749576
  have hstable : (prefixWord ++ tailWord_6749576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6749576).length < 2 ^ (prefixWord ++ tailWord_6749576).sum := by decide
  have hdescent : baseEnd_6749576 < baseStart_6749576 := by decide
  rcases family_descends (prefixWord ++ tailWord_6749576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6749613 : List Nat := [1, 5, 2, 2, 1, 1, 1, 3, 2, 2, 3]
def baseStart_6749613 : Nat := 118140960795 + 6749613 * 2 ^ 59
def prefixEnd_6749613 : Nat := 4983230072969 + 3 ^ 40 * 6749613 * 2
def baseEnd_6749613 : Nat := 3465795700835405841796601

theorem tailTrace_6749613 : CollatzResearch.WordTrace tailWord_6749613 prefixEnd_6749613 3465795700835405841796601 := by
  unfold tailWord_6749613
  simp only [CollatzResearch.WordTrace]
  refine ⟨246178610496312317971021493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164119073664208211980680995 246178610496312317971021493)
  ·
    refine ⟨23079244734029279809783265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 246178610496312317971021493 23079244734029279809783265)
    ·
      refine ⟨17309433550521959857337449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23079244734029279809783265 17309433550521959857337449)
      ·
        refine ⟨12982075162891469893003087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17309433550521959857337449 12982075162891469893003087)
        ·
          refine ⟨19473112744337204839504631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12982075162891469893003087 19473112744337204839504631)
          ·
            refine ⟨29209669116505807259256947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19473112744337204839504631 29209669116505807259256947)
            ·
              refine ⟨43814503674758710888885421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29209669116505807259256947 43814503674758710888885421)
              ·
                refine ⟨16430438878034516583332033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43814503674758710888885421 16430438878034516583332033)
                ·
                  refine ⟨12322829158525887437499025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16430438878034516583332033 12322829158525887437499025)
                  ·
                    refine ⟨9242121868894415578124269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12322829158525887437499025 9242121868894415578124269)
                    ·
                      refine ⟨3465795700835405841796601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9242121868894415578124269 3465795700835405841796601)
                      ·
                        rfl

theorem cell23_6749613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_6749613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6749613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6749613 prefixEnd_6749613 := by exact prefixLift 6749613
  have htrace : WordTrace (prefixWord ++ tailWord_6749613) baseStart_6749613 baseEnd_6749613 := by
    simpa [prefixWord, tailWord_6749613, baseEnd_6749613] using wordTrace_append hprefix tailTrace_6749613
  have hstable : (prefixWord ++ tailWord_6749613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6749613).length < 2 ^ (prefixWord ++ tailWord_6749613).sum := by decide
  have hdescent : baseEnd_6749613 < baseStart_6749613 := by decide
  rcases family_descends (prefixWord ++ tailWord_6749613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6749693 : List Nat := [1, 4, 1, 1, 1, 4, 3, 2, 2, 4]
def baseStart_6749693 : Nat := 118140960795 + 6749693 * 2 ^ 59
def prefixEnd_6749693 : Nat := 4983230072969 + 3 ^ 40 * 6749693 * 2
def baseEnd_6749693 : Nat := 1155278926429255176265411

theorem tailTrace_6749693 : CollatzResearch.WordTrace tailWord_6749693 prefixEnd_6749693 1155278926429255176265411 := by
  unfold tailWord_6749693
  simp only [CollatzResearch.WordTrace]
  refine ⟨246181528336022491633933733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164121018890681661089289155 246181528336022491633933733)
  ·
    refine ⟨46159036563004217181362575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 246181528336022491633933733 46159036563004217181362575)
    ·
      refine ⟨69238554844506325772043863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46159036563004217181362575 69238554844506325772043863)
      ·
        refine ⟨103857832266759488658065795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69238554844506325772043863 103857832266759488658065795)
        ·
          refine ⟨155786748400139232987098693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103857832266759488658065795 155786748400139232987098693)
          ·
            refine ⟨29210015325026106185081005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 155786748400139232987098693 29210015325026106185081005)
            ·
              refine ⟨10953755746884789819405377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29210015325026106185081005 10953755746884789819405377)
              ·
                refine ⟨8215316810163592364554033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10953755746884789819405377 8215316810163592364554033)
                ·
                  refine ⟨6161487607622694273415525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8215316810163592364554033 6161487607622694273415525)
                  ·
                    refine ⟨1155278926429255176265411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6161487607622694273415525 1155278926429255176265411)
                    ·
                      rfl

theorem cell23_6749693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 2, 2, 4].length) (baseStart_6749693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6749693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6749693 prefixEnd_6749693 := by exact prefixLift 6749693
  have htrace : WordTrace (prefixWord ++ tailWord_6749693) baseStart_6749693 baseEnd_6749693 := by
    simpa [prefixWord, tailWord_6749693, baseEnd_6749693] using wordTrace_append hprefix tailTrace_6749693
  have hstable : (prefixWord ++ tailWord_6749693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6749693).length < 2 ^ (prefixWord ++ tailWord_6749693).sum := by decide
  have hdescent : baseEnd_6749693 < baseStart_6749693 := by decide
  rcases family_descends (prefixWord ++ tailWord_6749693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6749710 : List Nat := [4, 1, 1, 2, 5, 1, 1, 1, 1, 6]
def baseStart_6749710 : Nat := 118140960795 + 6749710 * 2 ^ 59
def prefixEnd_6749710 : Nat := 4983230072969 + 3 ^ 40 * 6749710 * 2
def baseEnd_6749710 : Nat := 1155281836152963987427885

theorem tailTrace_6749710 : CollatzResearch.WordTrace tailWord_6749710 prefixEnd_6749710 1155281836152963987427885 := by
  unfold tailWord_6749710
  simp only [CollatzResearch.WordTrace]
  refine ⟨30772768547120112942162823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164121432251307269024868389 30772768547120112942162823)
  ·
    refine ⟨46159152820680169413244235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30772768547120112942162823 46159152820680169413244235)
    ·
      refine ⟨69238729231020254119866353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46159152820680169413244235 69238729231020254119866353)
      ·
        refine ⟨51929046923265190589899765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69238729231020254119866353 51929046923265190589899765)
        ·
          refine ⟨4868348149056111617803103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 51929046923265190589899765 4868348149056111617803103)
          ·
            refine ⟨7302522223584167426704655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4868348149056111617803103 7302522223584167426704655)
            ·
              refine ⟨10953783335376251140056983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7302522223584167426704655 10953783335376251140056983)
              ·
                refine ⟨16430675003064376710085475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10953783335376251140056983 16430675003064376710085475)
                ·
                  refine ⟨24646012504596565065128213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16430675003064376710085475 24646012504596565065128213)
                  ·
                    refine ⟨1155281836152963987427885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24646012504596565065128213 1155281836152963987427885)
                    ·
                      rfl

theorem cell23_6749710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 1, 1, 6].length) (baseStart_6749710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6749710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6749710 prefixEnd_6749710 := by exact prefixLift 6749710
  have htrace : WordTrace (prefixWord ++ tailWord_6749710) baseStart_6749710 baseEnd_6749710 := by
    simpa [prefixWord, tailWord_6749710, baseEnd_6749710] using wordTrace_append hprefix tailTrace_6749710
  have hstable : (prefixWord ++ tailWord_6749710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6749710).length < 2 ^ (prefixWord ++ tailWord_6749710).sum := by decide
  have hdescent : baseEnd_6749710 < baseStart_6749710 := by decide
  rcases family_descends (prefixWord ++ tailWord_6749710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6749720 : List Nat := [2, 1, 2, 3, 4, 1, 2, 2, 1, 2, 3]
def baseStart_6749720 : Nat := 118140960795 + 6749720 * 2 ^ 59
def prefixEnd_6749720 : Nat := 4983230072969 + 3 ^ 40 * 6749720 * 2
def baseEnd_6749720 : Nat := 3465850643265436923158609

theorem tailTrace_6749720 : CollatzResearch.WordTrace tailWord_6749720 prefixEnd_6749720 3465850643265436923158609 := by
  unfold tailWord_6749720
  simp only [CollatzResearch.WordTrace]
  refine ⟨123091256553462337622583307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164121675404616450163444409 123091256553462337622583307)
  ·
    refine ⟨184636884830193506433874961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123091256553462337622583307 184636884830193506433874961)
    ·
      refine ⟨138477663622645129825406221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184636884830193506433874961 138477663622645129825406221)
      ·
        refine ⟨51929123858491923684527333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138477663622645129825406221 51929123858491923684527333)
        ·
          refine ⟨9736710723467235690848875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51929123858491923684527333 9736710723467235690848875)
          ·
            refine ⟨14605066085200853536273313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9736710723467235690848875 14605066085200853536273313)
            ·
              refine ⟨10953799563900640152204985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14605066085200853536273313 10953799563900640152204985)
              ·
                refine ⟨8215349672925480114153739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10953799563900640152204985 8215349672925480114153739)
                ·
                  refine ⟨12323024509388220171230609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8215349672925480114153739 12323024509388220171230609)
                  ·
                    refine ⟨9242268382041165128422957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12323024509388220171230609 9242268382041165128422957)
                    ·
                      refine ⟨3465850643265436923158609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9242268382041165128422957 3465850643265436923158609)
                      ·
                        rfl

theorem cell23_6749720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 2, 1, 2, 3].length) (baseStart_6749720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6749720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6749720 prefixEnd_6749720 := by exact prefixLift 6749720
  have htrace : WordTrace (prefixWord ++ tailWord_6749720) baseStart_6749720 baseEnd_6749720 := by
    simpa [prefixWord, tailWord_6749720, baseEnd_6749720] using wordTrace_append hprefix tailTrace_6749720
  have hstable : (prefixWord ++ tailWord_6749720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6749720).length < 2 ^ (prefixWord ++ tailWord_6749720).sum := by decide
  have hdescent : baseEnd_6749720 < baseStart_6749720 := by decide
  rcases family_descends (prefixWord ++ tailWord_6749720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6749739 : List Nat := [1, 1, 1, 1, 2, 1, 3, 1, 3, 5, 4]
def baseStart_6749739 : Nat := 118140960795 + 6749739 * 2 ^ 59
def prefixEnd_6749739 : Nat := 4983230072969 + 3 ^ 40 * 6749739 * 2
def baseEnd_6749739 : Nat := 3465860399397872348821021

theorem tailTrace_6749739 : CollatzResearch.WordTrace tailWord_6749739 prefixEnd_6749739 3465860399397872348821021 := by
  unfold tailWord_6749739
  simp only [CollatzResearch.WordTrace]
  refine ⟨246183206093855841490108271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164122137395903894326738847 246183206093855841490108271)
  ·
    refine ⟨369274809140783762235162407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246183206093855841490108271 369274809140783762235162407)
    ·
      refine ⟨553912213711175643352743611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369274809140783762235162407 553912213711175643352743611)
      ·
        refine ⟨830868320566763465029115417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 553912213711175643352743611 830868320566763465029115417)
        ·
          refine ⟨623151240425072598771836563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 830868320566763465029115417 623151240425072598771836563)
          ·
            refine ⟨934726860637608898157754845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 623151240425072598771836563 934726860637608898157754845)
            ·
              refine ⟨350522572739103336809158067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 934726860637608898157754845 350522572739103336809158067)
              ·
                refine ⟨525783859108655005213737101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 350522572739103336809158067 525783859108655005213737101)
                ·
                  refine ⟨197168947165745626955151413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 525783859108655005213737101 197168947165745626955151413)
                  ·
                    refine ⟨18484588796788652527045445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 197168947165745626955151413 18484588796788652527045445)
                    ·
                      refine ⟨3465860399397872348821021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18484588796788652527045445 3465860399397872348821021)
                      ·
                        rfl

theorem cell23_6749739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 5, 4].length) (baseStart_6749739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6749739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6749739 prefixEnd_6749739 := by exact prefixLift 6749739
  have htrace : WordTrace (prefixWord ++ tailWord_6749739) baseStart_6749739 baseEnd_6749739 := by
    simpa [prefixWord, tailWord_6749739, baseEnd_6749739] using wordTrace_append hprefix tailTrace_6749739
  have hstable : (prefixWord ++ tailWord_6749739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6749739).length < 2 ^ (prefixWord ++ tailWord_6749739).sum := by decide
  have hdescent : baseEnd_6749739 < baseStart_6749739 := by decide
  rcases family_descends (prefixWord ++ tailWord_6749739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6749769 : List Nat := [1, 2, 1, 1, 2, 2, 1, 2, 2, 3, 6]
def baseStart_6749769 : Nat := 118140960795 + 6749769 * 2 ^ 59
def prefixEnd_6749769 : Nat := 4983230072969 + 3 ^ 40 * 6749769 * 2
def baseEnd_6749769 : Nat := 3465875803817507231445883

theorem tailTrace_6749769 : CollatzResearch.WordTrace tailWord_6749769 prefixEnd_6749769 3465875803817507231445883 := by
  unfold tailWord_6749769
  simp only [CollatzResearch.WordTrace]
  refine ⟨246184300283747156613700361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164122866855831437742466907 246184300283747156613700361)
  ·
    refine ⟨184638225212810367460275271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246184300283747156613700361 184638225212810367460275271)
    ·
      refine ⟨276957337819215551190412907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184638225212810367460275271 276957337819215551190412907)
      ·
        refine ⟨415436006728823326785619361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276957337819215551190412907 415436006728823326785619361)
        ·
          refine ⟨311577005046617495089214521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 415436006728823326785619361 311577005046617495089214521)
          ·
            refine ⟨233682753784963121316910891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 311577005046617495089214521 233682753784963121316910891)
            ·
              refine ⟨350524130677444681975366337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 233682753784963121316910891 350524130677444681975366337)
              ·
                refine ⟨262893098008083511481524753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 350524130677444681975366337 262893098008083511481524753)
                ·
                  refine ⟨197169823506062633611143565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 262893098008083511481524753 197169823506062633611143565)
                  ·
                    refine ⟨73938683814773487604178837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 197169823506062633611143565 73938683814773487604178837)
                    ·
                      refine ⟨3465875803817507231445883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73938683814773487604178837 3465875803817507231445883)
                      ·
                        rfl

theorem cell23_6749769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 3, 6].length) (baseStart_6749769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6749769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6749769 prefixEnd_6749769 := by exact prefixLift 6749769
  have htrace : WordTrace (prefixWord ++ tailWord_6749769) baseStart_6749769 baseEnd_6749769 := by
    simpa [prefixWord, tailWord_6749769, baseEnd_6749769] using wordTrace_append hprefix tailTrace_6749769
  have hstable : (prefixWord ++ tailWord_6749769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6749769).length < 2 ^ (prefixWord ++ tailWord_6749769).sum := by decide
  have hdescent : baseEnd_6749769 < baseStart_6749769 := by decide
  rcases family_descends (prefixWord ++ tailWord_6749769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6749858 : List Nat := [3, 3, 1, 4, 2, 1, 1, 2, 2, 2, 2]
def baseStart_6749858 : Nat := 118140960795 + 6749858 * 2 ^ 59
def prefixEnd_6749858 : Nat := 4983230072969 + 3 ^ 40 * 6749858 * 2
def baseEnd_6749858 : Nat := 3465921503595757383232975

theorem tailTrace_6749858 : CollatzResearch.WordTrace tailWord_6749858 prefixEnd_6749858 3465921503595757383232975 := by
  unfold tailWord_6749858
  simp only [CollatzResearch.WordTrace]
  refine ⟨61546886595106181203422557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164125030920283149875793485 61546886595106181203422557)
  ·
    refine ⟨23080082473164817951283459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61546886595106181203422557 23080082473164817951283459)
    ·
      refine ⟨34620123709747226926925189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23080082473164817951283459 34620123709747226926925189)
      ·
        refine ⟨6491273195577605048798473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34620123709747226926925189 6491273195577605048798473)
        ·
          refine ⟨4868454896683203786598855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6491273195577605048798473 4868454896683203786598855)
          ·
            refine ⟨7302682345024805679898283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4868454896683203786598855 7302682345024805679898283)
            ·
              refine ⟨10954023517537208519847425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7302682345024805679898283 10954023517537208519847425)
              ·
                refine ⟨8215517638152906389885569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10954023517537208519847425 8215517638152906389885569)
                ·
                  refine ⟨6161638228614679792414177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8215517638152906389885569 6161638228614679792414177)
                  ·
                    refine ⟨4621228671461009844310633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6161638228614679792414177 4621228671461009844310633)
                    ·
                      refine ⟨3465921503595757383232975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4621228671461009844310633 3465921503595757383232975)
                      ·
                        rfl

theorem cell23_6749858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_6749858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6749858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6749858 prefixEnd_6749858 := by exact prefixLift 6749858
  have htrace : WordTrace (prefixWord ++ tailWord_6749858) baseStart_6749858 baseEnd_6749858 := by
    simpa [prefixWord, tailWord_6749858, baseEnd_6749858] using wordTrace_append hprefix tailTrace_6749858
  have hstable : (prefixWord ++ tailWord_6749858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6749858).length < 2 ^ (prefixWord ++ tailWord_6749858).sum := by decide
  have hdescent : baseEnd_6749858 < baseStart_6749858 := by decide
  rcases family_descends (prefixWord ++ tailWord_6749858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6749963 : List Nat := [1, 1, 1, 1, 5, 1, 2, 1, 6, 4]
def baseStart_6749963 : Nat := 118140960795 + 6749963 * 2 ^ 59
def prefixEnd_6749963 : Nat := 4983230072969 + 3 ^ 40 * 6749963 * 2
def baseEnd_6749963 : Nat := 1155325139688159824139997

theorem tailTrace_6749963 : CollatzResearch.WordTrace tailWord_6749963 prefixEnd_6749963 1155325139688159824139997 := by
  unfold tailWord_6749963
  simp only [CollatzResearch.WordTrace]
  refine ⟨246191376045044327746262543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164127584030029551830841695 246191376045044327746262543)
  ·
    refine ⟨369287064067566491619393815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246191376045044327746262543 369287064067566491619393815)
    ·
      refine ⟨553930596101349737429090723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369287064067566491619393815 553930596101349737429090723)
      ·
        refine ⟨830895894152024606143636085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 553930596101349737429090723 830895894152024606143636085)
        ·
          refine ⟨77896490076752306825965883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 830895894152024606143636085 77896490076752306825965883)
          ·
            refine ⟨116844735115128460238948825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77896490076752306825965883 116844735115128460238948825)
            ·
              refine ⟨87633551336346345179211619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116844735115128460238948825 87633551336346345179211619)
              ·
                refine ⟨131450327004519517768817429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87633551336346345179211619 131450327004519517768817429)
                ·
                  refine ⟨6161734078336852395413317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 131450327004519517768817429 6161734078336852395413317)
                  ·
                    refine ⟨1155325139688159824139997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6161734078336852395413317 1155325139688159824139997)
                    ·
                      rfl

theorem cell23_6749963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 6, 4].length) (baseStart_6749963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6749963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6749963 prefixEnd_6749963 := by exact prefixLift 6749963
  have htrace : WordTrace (prefixWord ++ tailWord_6749963) baseStart_6749963 baseEnd_6749963 := by
    simpa [prefixWord, tailWord_6749963, baseEnd_6749963] using wordTrace_append hprefix tailTrace_6749963
  have hstable : (prefixWord ++ tailWord_6749963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6749963).length < 2 ^ (prefixWord ++ tailWord_6749963).sum := by decide
  have hdescent : baseEnd_6749963 < baseStart_6749963 := by decide
  rcases family_descends (prefixWord ++ tailWord_6749963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6749983 : List Nat := [1, 1, 2, 4, 2, 1, 1, 2, 3, 2, 4]
def baseStart_6749983 : Nat := 118140960795 + 6749983 * 2 ^ 59
def prefixEnd_6749983 : Nat := 4983230072969 + 3 ^ 40 * 6749983 * 2
def baseEnd_6749983 : Nat := 3465985688677569394169899

theorem tailTrace_6749983 : CollatzResearch.WordTrace tailWord_6749983 prefixEnd_6749983 3465985688677569394169899 := by
  unfold tailWord_6749983
  simp only [CollatzResearch.WordTrace]
  refine ⟨246192105504971871161990603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164128070336647914107993735 246192105504971871161990603)
  ·
    refine ⟨369288158257457806742985905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246192105504971871161990603 369288158257457806742985905)
    ·
      refine ⟨276966118693093355057239429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 369288158257457806742985905 276966118693093355057239429)
      ·
        refine ⟨51931147254955004073232393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 276966118693093355057239429 51931147254955004073232393)
        ·
          refine ⟨38948360441216253054924295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51931147254955004073232393 38948360441216253054924295)
          ·
            refine ⟨58422540661824379582386443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38948360441216253054924295 58422540661824379582386443)
            ·
              refine ⟨87633810992736569373579665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58422540661824379582386443 87633810992736569373579665)
              ·
                refine ⟨65725358244552427030184749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87633810992736569373579665 65725358244552427030184749)
                ·
                  refine ⟨24647009341707160136319281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65725358244552427030184749 24647009341707160136319281)
                  ·
                    refine ⟨18485257006280370102239461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24647009341707160136319281 18485257006280370102239461)
                    ·
                      refine ⟨3465985688677569394169899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18485257006280370102239461 3465985688677569394169899)
                      ·
                        rfl

theorem cell23_6749983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 2, 3, 2, 4].length) (baseStart_6749983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6749983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6749983 prefixEnd_6749983 := by exact prefixLift 6749983
  have htrace : WordTrace (prefixWord ++ tailWord_6749983) baseStart_6749983 baseEnd_6749983 := by
    simpa [prefixWord, tailWord_6749983, baseEnd_6749983] using wordTrace_append hprefix tailTrace_6749983
  have hstable : (prefixWord ++ tailWord_6749983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6749983).length < 2 ^ (prefixWord ++ tailWord_6749983).sum := by decide
  have hdescent : baseEnd_6749983 < baseStart_6749983 := by decide
  rcases family_descends (prefixWord ++ tailWord_6749983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6750004 : List Nat := [2, 5, 1, 1, 2, 1, 1, 1, 5, 2, 2]
def baseStart_6750004 : Nat := 118140960795 + 6750004 * 2 ^ 59
def prefixEnd_6750004 : Nat := 4983230072969 + 3 ^ 40 * 6750004 * 2
def baseEnd_6750004 : Nat := 3465996471771313812007303

theorem tailTrace_6750004 : CollatzResearch.WordTrace tailWord_6750004 prefixEnd_6750004 3465996471771313812007303 := by
  unfold tailWord_6750004
  simp only [CollatzResearch.WordTrace]
  refine ⟨123096435718947895874252533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164128580958597194499003377 123096435718947895874252533)
  ·
    refine ⟨11540290848651365238211175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 123096435718947895874252533 11540290848651365238211175)
    ·
      refine ⟨17310436272977047857316763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11540290848651365238211175 17310436272977047857316763)
      ·
        refine ⟨25965654409465571785975145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17310436272977047857316763 25965654409465571785975145)
        ·
          refine ⟨19474240807099178839481359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25965654409465571785975145 19474240807099178839481359)
          ·
            refine ⟨29211361210648768259222039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19474240807099178839481359 29211361210648768259222039)
            ·
              refine ⟨43817041815973152388833059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29211361210648768259222039 43817041815973152388833059)
              ·
                refine ⟨65725562723959728583249589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43817041815973152388833059 65725562723959728583249589)
                ·
                  refine ⟨6161771505371224554679649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65725562723959728583249589 6161771505371224554679649)
                  ·
                    refine ⟨4621328629028418416009737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6161771505371224554679649 4621328629028418416009737)
                    ·
                      refine ⟨3465996471771313812007303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4621328629028418416009737 3465996471771313812007303)
                      ·
                        rfl

theorem cell23_6750004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 1, 5, 2, 2].length) (baseStart_6750004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6750004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6750004 prefixEnd_6750004 := by exact prefixLift 6750004
  have htrace : WordTrace (prefixWord ++ tailWord_6750004) baseStart_6750004 baseEnd_6750004 := by
    simpa [prefixWord, tailWord_6750004, baseEnd_6750004] using wordTrace_append hprefix tailTrace_6750004
  have hstable : (prefixWord ++ tailWord_6750004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6750004).length < 2 ^ (prefixWord ++ tailWord_6750004).sum := by decide
  have hdescent : baseEnd_6750004 < baseStart_6750004 := by decide
  rcases family_descends (prefixWord ++ tailWord_6750004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6750010 : List Nat := [3, 1, 1, 1, 5, 2, 3, 7]
def baseStart_6750010 : Nat := 118140960795 + 6750010 * 2 ^ 59
def prefixEnd_6750010 : Nat := 4983230072969 + 3 ^ 40 * 6750010 * 2
def baseEnd_6750010 : Nat := 128370353802045955130825

theorem tailTrace_6750010 : CollatzResearch.WordTrace tailWord_6750010 prefixEnd_6750010 128370353802045955130825 := by
  unfold tailWord_6750010
  simp only [CollatzResearch.WordTrace]
  refine ⟨61548272568968513693305871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164128726850582703182148989 61548272568968513693305871)
  ·
    refine ⟨92322408853452770539958807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61548272568968513693305871 92322408853452770539958807)
    ·
      refine ⟨138483613280179155809938211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92322408853452770539958807 138483613280179155809938211)
      ·
        refine ⟨207725419920268733714907317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138483613280179155809938211 207725419920268733714907317)
        ·
          refine ⟨19474258117525193785772561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 207725419920268733714907317 19474258117525193785772561)
          ·
            refine ⟨14605693588143895339329421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19474258117525193785772561 14605693588143895339329421)
            ·
              refine ⟨5477135095553960752248533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14605693588143895339329421 5477135095553960752248533)
              ·
                refine ⟨128370353802045955130825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5477135095553960752248533 128370353802045955130825)
                ·
                  rfl

theorem cell23_6750010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 3, 7].length) (baseStart_6750010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6750010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6750010 prefixEnd_6750010 := by exact prefixLift 6750010
  have htrace : WordTrace (prefixWord ++ tailWord_6750010) baseStart_6750010 baseEnd_6750010 := by
    simpa [prefixWord, tailWord_6750010, baseEnd_6750010] using wordTrace_append hprefix tailTrace_6750010
  have hstable : (prefixWord ++ tailWord_6750010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6750010).length < 2 ^ (prefixWord ++ tailWord_6750010).sum := by decide
  have hdescent : baseEnd_6750010 < baseStart_6750010 := by decide
  rcases family_descends (prefixWord ++ tailWord_6750010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6750024 : List Nat := [2, 1, 3, 1, 1, 6, 2, 1, 1, 2, 3]
def baseStart_6750024 : Nat := 118140960795 + 6750024 * 2 ^ 59
def prefixEnd_6750024 : Nat := 4983230072969 + 3 ^ 40 * 6750024 * 2
def baseEnd_6750024 : Nat := 3466006741384403733757211

theorem tailTrace_6750024 : CollatzResearch.WordTrace tailWord_6750024 prefixEnd_6750024 3466006741384403733757211 := by
  unfold tailWord_6750024
  simp only [CollatzResearch.WordTrace]
  refine ⟨123096800448911667582116563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164129067265215556776155417 123096800448911667582116563)
  ·
    refine ⟨184645200673367501373174845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123096800448911667582116563 184645200673367501373174845)
    ·
      refine ⟨69241950252512813014940567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184645200673367501373174845 69241950252512813014940567)
      ·
        refine ⟨103862925378769219522410851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69241950252512813014940567 103862925378769219522410851)
        ·
          refine ⟨155794388068153829283616277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103862925378769219522410851 155794388068153829283616277)
          ·
            refine ⟨7302861940694710747669513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 155794388068153829283616277 7302861940694710747669513)
            ·
              refine ⟨5477146455521033060752135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7302861940694710747669513 5477146455521033060752135)
              ·
                refine ⟨8215719683281549591128203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5477146455521033060752135 8215719683281549591128203)
                ·
                  refine ⟨12323579524922324386692305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8215719683281549591128203 12323579524922324386692305)
                  ·
                    refine ⟨9242684643691743290019229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12323579524922324386692305 9242684643691743290019229)
                    ·
                      refine ⟨3466006741384403733757211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9242684643691743290019229 3466006741384403733757211)
                      ·
                        rfl

theorem cell23_6750024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 2, 1, 1, 2, 3].length) (baseStart_6750024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6750024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6750024 prefixEnd_6750024 := by exact prefixLift 6750024
  have htrace : WordTrace (prefixWord ++ tailWord_6750024) baseStart_6750024 baseEnd_6750024 := by
    simpa [prefixWord, tailWord_6750024, baseEnd_6750024] using wordTrace_append hprefix tailTrace_6750024
  have hstable : (prefixWord ++ tailWord_6750024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6750024).length < 2 ^ (prefixWord ++ tailWord_6750024).sum := by decide
  have hdescent : baseEnd_6750024 < baseStart_6750024 := by decide
  rcases family_descends (prefixWord ++ tailWord_6750024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6750037 : List Nat := [1, 3, 2, 2, 2, 3, 1, 1, 4, 1, 3]
def baseStart_6750037 : Nat := 118140960795 + 6750037 * 2 ^ 59
def prefixEnd_6750037 : Nat := 4983230072969 + 3 ^ 40 * 6750037 * 2
def baseEnd_6750037 : Nat := 3466013416632912182894651

theorem tailTrace_6750037 : CollatzResearch.WordTrace tailWord_6750037 prefixEnd_6750037 3466013416632912182894651 := by
  unfold tailWord_6750037
  simp only [CollatzResearch.WordTrace]
  refine ⟨246194075046776238384456365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164129383364517492256304243 246194075046776238384456365)
  ·
    refine ⟨92322778142541089394171137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 246194075046776238384456365 92322778142541089394171137)
    ·
      refine ⟨69242083606905817045628353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92322778142541089394171137 69242083606905817045628353)
      ·
        refine ⟨51931562705179362784221265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69242083606905817045628353 51931562705179362784221265)
        ·
          refine ⟨38948672028884522088165949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51931562705179362784221265 38948672028884522088165949)
          ·
            refine ⟨14605752010831695783062231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38948672028884522088165949 14605752010831695783062231)
            ·
              refine ⟨21908628016247543674593347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14605752010831695783062231 21908628016247543674593347)
              ·
                refine ⟨32862942024371315511890021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21908628016247543674593347 32862942024371315511890021)
                ·
                  refine ⟨6161801629569621658479379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32862942024371315511890021 6161801629569621658479379)
                  ·
                    refine ⟨9242702444354432487719069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6161801629569621658479379 9242702444354432487719069)
                    ·
                      refine ⟨3466013416632912182894651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9242702444354432487719069 3466013416632912182894651)
                      ·
                        rfl

theorem cell23_6750037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 1, 4, 1, 3].length) (baseStart_6750037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6750037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6750037 prefixEnd_6750037 := by exact prefixLift 6750037
  have htrace : WordTrace (prefixWord ++ tailWord_6750037) baseStart_6750037 baseEnd_6750037 := by
    simpa [prefixWord, tailWord_6750037, baseEnd_6750037] using wordTrace_append hprefix tailTrace_6750037
  have hstable : (prefixWord ++ tailWord_6750037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6750037).length < 2 ^ (prefixWord ++ tailWord_6750037).sum := by decide
  have hdescent : baseEnd_6750037 < baseStart_6750037 := by decide
  rcases family_descends (prefixWord ++ tailWord_6750037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6750111 : List Nat := [1, 1, 2, 5, 3, 1, 1, 3, 2, 2, 2]
def baseStart_6750111 : Nat := 118140960795 + 6750111 * 2 ^ 59
def prefixEnd_6750111 : Nat := 4983230072969 + 3 ^ 40 * 6750111 * 2
def baseEnd_6750111 : Nat := 3466051414201344893369311

theorem tailTrace_6750111 : CollatzResearch.WordTrace tailWord_6750111 prefixEnd_6750111 3466051414201344893369311 := by
  unfold tailWord_6750111
  simp only [CollatzResearch.WordTrace]
  refine ⟨246196774048508149022650187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164131182699005432681766791 246196774048508149022650187)
  ·
    refine ⟨369295161072762223533975281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246196774048508149022650187 369295161072762223533975281)
    ·
      refine ⟨276971370804571667650481461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 369295161072762223533975281 276971370804571667650481461)
      ·
        refine ⟨25966066012928593842232637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 276971370804571667650481461 25966066012928593842232637)
        ·
          refine ⟨9737274754848222690837239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25966066012928593842232637 9737274754848222690837239)
          ·
            refine ⟨14605912132272334036255859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9737274754848222690837239 14605912132272334036255859)
            ·
              refine ⟨21908868198408501054383789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14605912132272334036255859 21908868198408501054383789)
              ·
                refine ⟨8215825574403187895393921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21908868198408501054383789 8215825574403187895393921)
                ·
                  refine ⟨6161869180802390921545441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8215825574403187895393921 6161869180802390921545441)
                  ·
                    refine ⟨4621401885601793191159081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6161869180802390921545441 4621401885601793191159081)
                    ·
                      refine ⟨3466051414201344893369311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4621401885601793191159081 3466051414201344893369311)
                      ·
                        rfl

theorem cell23_6750111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 3, 2, 2, 2].length) (baseStart_6750111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6750111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6750111 prefixEnd_6750111 := by exact prefixLift 6750111
  have htrace : WordTrace (prefixWord ++ tailWord_6750111) baseStart_6750111 baseEnd_6750111 := by
    simpa [prefixWord, tailWord_6750111, baseEnd_6750111] using wordTrace_append hprefix tailTrace_6750111
  have hstable : (prefixWord ++ tailWord_6750111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6750111).length < 2 ^ (prefixWord ++ tailWord_6750111).sum := by decide
  have hdescent : baseEnd_6750111 < baseStart_6750111 := by decide
  rcases family_descends (prefixWord ++ tailWord_6750111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6750123 : List Nat := [1, 1, 1, 1, 2, 1, 1, 3, 5, 2, 5]
def baseStart_6750123 : Nat := 118140960795 + 6750123 * 2 ^ 59
def prefixEnd_6750123 : Nat := 4983230072969 + 3 ^ 40 * 6750123 * 2
def baseEnd_6750123 : Nat := 3466057575969198846419255

theorem tailTrace_6750123 : CollatzResearch.WordTrace tailWord_6750123 prefixEnd_6750123 3466057575969198846419255 := by
  unfold tailWord_6750123
  simp only [CollatzResearch.WordTrace]
  refine ⟨246197211724464675072087023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164131474482976450048058015 246197211724464675072087023)
  ·
    refine ⟨369295817586697012608130535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246197211724464675072087023 369295817586697012608130535)
    ·
      refine ⟨553943726380045518912195803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369295817586697012608130535 553943726380045518912195803)
      ·
        refine ⟨830915589570068278368293705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 553943726380045518912195803 830915589570068278368293705)
        ·
          refine ⟨623186692177551208776220279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 830915589570068278368293705 623186692177551208776220279)
          ·
            refine ⟨934780038266326813164330419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 623186692177551208776220279 934780038266326813164330419)
            ·
              refine ⟨1402170057399490219746495629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 934780038266326813164330419 1402170057399490219746495629)
              ·
                refine ⟨525813771524808832404935861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1402170057399490219746495629 525813771524808832404935861)
                ·
                  refine ⟨49295041080450828037962737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 525813771524808832404935861 49295041080450828037962737)
                  ·
                    refine ⟨36971280810338121028472053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49295041080450828037962737 36971280810338121028472053)
                    ·
                      refine ⟨3466057575969198846419255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36971280810338121028472053 3466057575969198846419255)
                      ·
                        rfl

theorem cell23_6750123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 5, 2, 5].length) (baseStart_6750123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6750123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6750123 prefixEnd_6750123 := by exact prefixLift 6750123
  have htrace : WordTrace (prefixWord ++ tailWord_6750123) baseStart_6750123 baseEnd_6750123 := by
    simpa [prefixWord, tailWord_6750123, baseEnd_6750123] using wordTrace_append hprefix tailTrace_6750123
  have hstable : (prefixWord ++ tailWord_6750123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6750123).length < 2 ^ (prefixWord ++ tailWord_6750123).sum := by decide
  have hdescent : baseEnd_6750123 < baseStart_6750123 := by decide
  rcases family_descends (prefixWord ++ tailWord_6750123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6750167 : List Nat := [1, 1, 3, 2, 1, 1, 5, 1, 2, 4, 2]
def baseStart_6750167 : Nat := 118140960795 + 6750167 * 2 ^ 59
def prefixEnd_6750167 : Nat := 4983230072969 + 3 ^ 40 * 6750167 * 2
def baseEnd_6750167 : Nat := 3466080169117996674269053

theorem tailTrace_6750167 : CollatzResearch.WordTrace tailWord_6750167 prefixEnd_6750167 3466080169117996674269053 := by
  unfold tailWord_6750167
  simp only [CollatzResearch.WordTrace]
  refine ⟨246198816536305270586688755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164132544357536847057792503 246198816536305270586688755)
  ·
    refine ⟨369298224804457905880033133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246198816536305270586688755 369298224804457905880033133)
    ·
      refine ⟨138486834301671714705012425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 369298224804457905880033133 138486834301671714705012425)
      ·
        refine ⟨103865125726253786028759319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138486834301671714705012425 103865125726253786028759319)
        ·
          refine ⟨155797688589380679043138979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103865125726253786028759319 155797688589380679043138979)
          ·
            refine ⟨233696532884071018564708469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155797688589380679043138979 233696532884071018564708469)
            ·
              refine ⟨21909049957881657990441419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 233696532884071018564708469 21909049957881657990441419)
              ·
                refine ⟨32863574936822486985662129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21909049957881657990441419 32863574936822486985662129)
                ·
                  refine ⟨24647681202616865239246597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32863574936822486985662129 24647681202616865239246597)
                  ·
                    refine ⟨4621440225490662232358737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24647681202616865239246597 4621440225490662232358737)
                    ·
                      refine ⟨3466080169117996674269053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4621440225490662232358737 3466080169117996674269053)
                      ·
                        rfl

theorem cell23_6750167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 1, 2, 4, 2].length) (baseStart_6750167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6750167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6750167 prefixEnd_6750167 := by exact prefixLift 6750167
  have htrace : WordTrace (prefixWord ++ tailWord_6750167) baseStart_6750167 baseEnd_6750167 := by
    simpa [prefixWord, tailWord_6750167, baseEnd_6750167] using wordTrace_append hprefix tailTrace_6750167
  have hstable : (prefixWord ++ tailWord_6750167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6750167).length < 2 ^ (prefixWord ++ tailWord_6750167).sum := by decide
  have hdescent : baseEnd_6750167 < baseStart_6750167 := by decide
  rcases family_descends (prefixWord ++ tailWord_6750167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6750227 : List Nat := [1, 1, 1, 2, 1, 4, 3, 2, 1, 5, 2]
def baseStart_6750227 : Nat := 118140960795 + 6750227 * 2 ^ 59
def prefixEnd_6750227 : Nat := 4983230072969 + 3 ^ 40 * 6750227 * 2
def baseEnd_6750227 : Nat := 3466110977957266439518777

theorem tailTrace_6750227 : CollatzResearch.WordTrace tailWord_6750227 prefixEnd_6750227 3466110977957266439518777 := by
  unfold tailWord_6750227
  simp only [CollatzResearch.WordTrace]
  refine ⟨246201004916087900833872935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164134003277391933889248623 246201004916087900833872935)
  ·
    refine ⟨369301507374131851250809403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246201004916087900833872935 369301507374131851250809403)
    ·
      refine ⟨553952261061197776876214105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369301507374131851250809403 553952261061197776876214105)
      ·
        refine ⟨415464195795898332657160579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 553952261061197776876214105 415464195795898332657160579)
        ·
          refine ⟨623196293693847498985740869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 415464195795898332657160579 623196293693847498985740869)
          ·
            refine ⟨116849305067596406059826413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 623196293693847498985740869 116849305067596406059826413)
            ·
              refine ⟨43818489400348652272434905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116849305067596406059826413 43818489400348652272434905)
              ·
                refine ⟨32863867050261489204326179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43818489400348652272434905 32863867050261489204326179)
                ·
                  refine ⟨49295800575392233806489269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32863867050261489204326179 49295800575392233806489269)
                  ·
                    refine ⟨4621481303943021919358369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49295800575392233806489269 4621481303943021919358369)
                    ·
                      refine ⟨3466110977957266439518777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4621481303943021919358369 3466110977957266439518777)
                      ·
                        rfl

theorem cell23_6750227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 2, 1, 5, 2].length) (baseStart_6750227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6750227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6750227 prefixEnd_6750227 := by exact prefixLift 6750227
  have htrace : WordTrace (prefixWord ++ tailWord_6750227) baseStart_6750227 baseEnd_6750227 := by
    simpa [prefixWord, tailWord_6750227, baseEnd_6750227] using wordTrace_append hprefix tailTrace_6750227
  have hstable : (prefixWord ++ tailWord_6750227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6750227).length < 2 ^ (prefixWord ++ tailWord_6750227).sum := by decide
  have hdescent : baseEnd_6750227 < baseStart_6750227 := by decide
  rcases family_descends (prefixWord ++ tailWord_6750227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6750234 : List Nat := [3, 1, 1, 3, 1, 3, 2, 2, 3, 1, 3]
def baseStart_6750234 : Nat := 118140960795 + 6750234 * 2 ^ 59
def prefixEnd_6750234 : Nat := 4983230072969 + 3 ^ 40 * 6750234 * 2
def baseEnd_6750234 : Nat := 3466114572321847912131245

theorem tailTrace_6750234 : CollatzResearch.WordTrace tailWord_6750234 prefixEnd_6750234 3466114572321847912131245 := by
  unfold tailWord_6750234
  simp only [CollatzResearch.WordTrace]
  refine ⟨61550315056765635257344439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164134173484708360686251837 61550315056765635257344439)
  ·
    refine ⟨92325472585148452886016659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61550315056765635257344439 92325472585148452886016659)
    ·
      refine ⟨138488208877722679329024989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92325472585148452886016659 138488208877722679329024989)
      ·
        refine ⟨51933078329146004748384371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138488208877722679329024989 51933078329146004748384371)
        ·
          refine ⟨77899617493719007122576557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51933078329146004748384371 77899617493719007122576557)
          ·
            refine ⟨29212356560144627670966209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77899617493719007122576557 29212356560144627670966209)
            ·
              refine ⟨21909267420108470753224657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29212356560144627670966209 21909267420108470753224657)
              ·
                refine ⟨16431950565081353064918493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21909267420108470753224657 16431950565081353064918493)
                ·
                  refine ⟨6161981461905507399344435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16431950565081353064918493 6161981461905507399344435)
                  ·
                    refine ⟨9242972192858261099016653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6161981461905507399344435 9242972192858261099016653)
                    ·
                      refine ⟨3466114572321847912131245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9242972192858261099016653 3466114572321847912131245)
                      ·
                        rfl

theorem cell23_6750234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 2, 3, 1, 3].length) (baseStart_6750234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6750234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6750234 prefixEnd_6750234 := by exact prefixLift 6750234
  have htrace : WordTrace (prefixWord ++ tailWord_6750234) baseStart_6750234 baseEnd_6750234 := by
    simpa [prefixWord, tailWord_6750234, baseEnd_6750234] using wordTrace_append hprefix tailTrace_6750234
  have hstable : (prefixWord ++ tailWord_6750234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6750234).length < 2 ^ (prefixWord ++ tailWord_6750234).sum := by decide
  have hdescent : baseEnd_6750234 < baseStart_6750234 := by decide
  rcases family_descends (prefixWord ++ tailWord_6750234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6750254 : List Nat := [4, 1, 3, 1, 1, 2, 2, 3, 1, 5]
def baseStart_6750254 : Nat := 118140960795 + 6750254 * 2 ^ 59
def prefixEnd_6750254 : Nat := 4983230072969 + 3 ^ 40 * 6750254 * 2
def baseEnd_6750254 : Nat := 1155374947311645944627051

theorem tailTrace_6750254 : CollatzResearch.WordTrace tailWord_6750254 prefixEnd_6750254 1155374947311645944627051 := by
  unfold tailWord_6750254
  simp only [CollatzResearch.WordTrace]
  refine ⟨30775248710873760555638227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164134659791326722963403877 30775248710873760555638227)
  ·
    refine ⟨46162873066310640833457341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30775248710873760555638227 46162873066310640833457341)
    ·
      refine ⟨17311077399866490312546503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46162873066310640833457341 17311077399866490312546503)
      ·
        refine ⟨25966616099799735468819755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17311077399866490312546503 25966616099799735468819755)
        ·
          refine ⟨38949924149699603203229633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25966616099799735468819755 38949924149699603203229633)
          ·
            refine ⟨29212443112274702402422225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38949924149699603203229633 29212443112274702402422225)
            ·
              refine ⟨21909332334206026801816669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29212443112274702402422225 21909332334206026801816669)
              ·
                refine ⟨8215999625327260050681251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21909332334206026801816669 8215999625327260050681251)
                ·
                  refine ⟨12323999437990890076021877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8215999625327260050681251 12323999437990890076021877)
                  ·
                    refine ⟨1155374947311645944627051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12323999437990890076021877 1155374947311645944627051)
                    ·
                      rfl

theorem cell23_6750254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 3, 1, 5].length) (baseStart_6750254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6750254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6750254 prefixEnd_6750254 := by exact prefixLift 6750254
  have htrace : WordTrace (prefixWord ++ tailWord_6750254) baseStart_6750254 baseEnd_6750254 := by
    simpa [prefixWord, tailWord_6750254, baseEnd_6750254] using wordTrace_append hprefix tailTrace_6750254
  have hstable : (prefixWord ++ tailWord_6750254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6750254).length < 2 ^ (prefixWord ++ tailWord_6750254).sum := by decide
  have hdescent : baseEnd_6750254 < baseStart_6750254 := by decide
  rcases family_descends (prefixWord ++ tailWord_6750254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6750268 : List Nat := [2, 2, 2, 2, 2, 1, 5, 2, 1, 1, 3]
def baseStart_6750268 : Nat := 118140960795 + 6750268 * 2 ^ 59
def prefixEnd_6750268 : Nat := 4983230072969 + 3 ^ 40 * 6750268 * 2
def baseEnd_6750268 : Nat := 3466132030664100779106089

theorem tailTrace_6750268 : CollatzResearch.WordTrace tailWord_6750268 prefixEnd_6750268 3466132030664100779106089 := by
  unfold tailWord_6750268
  simp only [CollatzResearch.WordTrace]
  refine ⟨123101250154469682418057729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164135000205959576557410305 123101250154469682418057729)
  ·
    refine ⟨92325937615852261813543297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123101250154469682418057729 92325937615852261813543297)
    ·
      refine ⟨69244453211889196360157473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92325937615852261813543297 69244453211889196360157473)
      ·
        refine ⟨51933339908916897270118105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69244453211889196360157473 51933339908916897270118105)
        ·
          refine ⟨38950004931687672952588579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51933339908916897270118105 38950004931687672952588579)
          ·
            refine ⟨58425007397531509428882869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38950004931687672952588579 58425007397531509428882869)
            ·
              refine ⟨5477344443518579008957769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58425007397531509428882869 5477344443518579008957769)
              ·
                refine ⟨4108008332638934256718327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5477344443518579008957769 4108008332638934256718327)
                ·
                  refine ⟨6162012498958401385077491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4108008332638934256718327 6162012498958401385077491)
                  ·
                    refine ⟨9243018748437602077616237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6162012498958401385077491 9243018748437602077616237)
                    ·
                      refine ⟨3466132030664100779106089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9243018748437602077616237 3466132030664100779106089)
                      ·
                        rfl

theorem cell23_6750268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 5, 2, 1, 1, 3].length) (baseStart_6750268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6750268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6750268 prefixEnd_6750268 := by exact prefixLift 6750268
  have htrace : WordTrace (prefixWord ++ tailWord_6750268) baseStart_6750268 baseEnd_6750268 := by
    simpa [prefixWord, tailWord_6750268, baseEnd_6750268] using wordTrace_append hprefix tailTrace_6750268
  have hstable : (prefixWord ++ tailWord_6750268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6750268).length < 2 ^ (prefixWord ++ tailWord_6750268).sum := by decide
  have hdescent : baseEnd_6750268 < baseStart_6750268 := by decide
  rcases family_descends (prefixWord ++ tailWord_6750268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6750277 : List Nat := [1, 3, 1, 1, 1, 3, 1, 4, 3, 2, 3]
def baseStart_6750277 : Nat := 118140960795 + 6750277 * 2 ^ 59
def prefixEnd_6750277 : Nat := 4983230072969 + 3 ^ 40 * 6750277 * 2
def baseEnd_6750277 : Nat := 3466136651989991243893547

theorem tailTrace_6750277 : CollatzResearch.WordTrace tailWord_6750277 prefixEnd_6750277 3466136651989991243893547 := by
  unfold tailWord_6750277
  simp only [CollatzResearch.WordTrace]
  refine ⟨246202828565906759373193085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164135219043937839582128723 246202828565906759373193085)
  ·
    refine ⟨92326060712215034764947407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 246202828565906759373193085 92326060712215034764947407)
    ·
      refine ⟨138489091068322552147421111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92326060712215034764947407 138489091068322552147421111)
      ·
        refine ⟨207733636602483828221131667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138489091068322552147421111 207733636602483828221131667)
        ·
          refine ⟨311600454903725742331697501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207733636602483828221131667 311600454903725742331697501)
          ·
            refine ⟨116850170588897153374386563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 311600454903725742331697501 116850170588897153374386563)
            ·
              refine ⟨175275255883345730061579845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116850170588897153374386563 175275255883345730061579845)
              ·
                refine ⟨32864110478127324386546221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 175275255883345730061579845 32864110478127324386546221)
                ·
                  refine ⟨12324041429297746644954833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32864110478127324386546221 12324041429297746644954833)
                  ·
                    refine ⟨9243031071973309983716125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12324041429297746644954833 9243031071973309983716125)
                    ·
                      refine ⟨3466136651989991243893547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9243031071973309983716125 3466136651989991243893547)
                      ·
                        rfl

theorem cell23_6750277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 4, 3, 2, 3].length) (baseStart_6750277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6750277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6750277 prefixEnd_6750277 := by exact prefixLift 6750277
  have htrace : WordTrace (prefixWord ++ tailWord_6750277) baseStart_6750277 baseEnd_6750277 := by
    simpa [prefixWord, tailWord_6750277, baseEnd_6750277] using wordTrace_append hprefix tailTrace_6750277
  have hstable : (prefixWord ++ tailWord_6750277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6750277).length < 2 ^ (prefixWord ++ tailWord_6750277).sum := by decide
  have hdescent : baseEnd_6750277 < baseStart_6750277 := by decide
  rcases family_descends (prefixWord ++ tailWord_6750277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6750307 : List Nat := [1, 1, 1, 5, 1, 1, 3, 1, 3, 3, 3]
def baseStart_6750307 : Nat := 118140960795 + 6750307 * 2 ^ 59
def prefixEnd_6750307 : Nat := 4983230072969 + 3 ^ 40 * 6750307 * 2
def baseEnd_6750307 : Nat := 3466152056409626126518409

theorem tailTrace_6750307 : CollatzResearch.WordTrace tailWord_6750307 prefixEnd_6750307 3466152056409626126518409 := by
  unfold tailWord_6750307
  simp only [CollatzResearch.WordTrace]
  refine ⟨246203922755798074496785175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164135948503865382997856783 246203922755798074496785175)
  ·
    refine ⟨369305884133697111745177763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246203922755798074496785175 369305884133697111745177763)
    ·
      refine ⟨553958826200545667617766645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369305884133697111745177763 553958826200545667617766645)
      ·
        refine ⟨51933639956301156339165623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 553958826200545667617766645 51933639956301156339165623)
        ·
          refine ⟨77900459934451734508748435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51933639956301156339165623 77900459934451734508748435)
          ·
            refine ⟨116850689901677601763122653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77900459934451734508748435 116850689901677601763122653)
            ·
              refine ⟨43819008713129100661170995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116850689901677601763122653 43819008713129100661170995)
              ·
                refine ⟨65728513069693650991756493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43819008713129100661170995 65728513069693650991756493)
                ·
                  refine ⟨24648192401135119121908685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65728513069693650991756493 24648192401135119121908685)
                  ·
                    refine ⟨9243072150425669670715757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24648192401135119121908685 9243072150425669670715757)
                    ·
                      refine ⟨3466152056409626126518409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9243072150425669670715757 3466152056409626126518409)
                      ·
                        rfl

theorem cell23_6750307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 1, 3, 3, 3].length) (baseStart_6750307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6750307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6750307 prefixEnd_6750307 := by exact prefixLift 6750307
  have htrace : WordTrace (prefixWord ++ tailWord_6750307) baseStart_6750307 baseEnd_6750307 := by
    simpa [prefixWord, tailWord_6750307, baseEnd_6750307] using wordTrace_append hprefix tailTrace_6750307
  have hstable : (prefixWord ++ tailWord_6750307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6750307).length < 2 ^ (prefixWord ++ tailWord_6750307).sum := by decide
  have hdescent : baseEnd_6750307 < baseStart_6750307 := by decide
  rcases family_descends (prefixWord ++ tailWord_6750307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6750311 : List Nat := [1, 1, 5, 1, 1, 2, 5, 1, 1, 2, 3]
def baseStart_6750311 : Nat := 118140960795 + 6750311 * 2 ^ 59
def prefixEnd_6750311 : Nat := 4983230072969 + 3 ^ 40 * 6750311 * 2
def baseEnd_6750311 : Nat := 3466154110332244110868391

theorem tailTrace_6750311 : CollatzResearch.WordTrace tailWord_6750311 prefixEnd_6750311 3466154110332244110868391 := by
  unfold tailWord_6750311
  simp only [CollatzResearch.WordTrace]
  refine ⟨246204068647783583179930787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164136045765189055453287191 246204068647783583179930787)
  ·
    refine ⟨369306102971675374769896181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246204068647783583179930787 369306102971675374769896181)
    ·
      refine ⟨34622447153594566384677767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 369306102971675374769896181 34622447153594566384677767)
      ·
        refine ⟨51933670730391849577016651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34622447153594566384677767 51933670730391849577016651)
        ·
          refine ⟨77900506095587774365524977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51933670730391849577016651 77900506095587774365524977)
          ·
            refine ⟨58425379571690830774143733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77900506095587774365524977 58425379571690830774143733)
            ·
              refine ⟨5477379334846015385075975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58425379571690830774143733 5477379334846015385075975)
              ·
                refine ⟨8216069002269023077613963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5477379334846015385075975 8216069002269023077613963)
                ·
                  refine ⟨12324103503403534616420945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8216069002269023077613963 12324103503403534616420945)
                  ·
                    refine ⟨9243077627552650962315709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12324103503403534616420945 9243077627552650962315709)
                    ·
                      refine ⟨3466154110332244110868391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9243077627552650962315709 3466154110332244110868391)
                      ·
                        rfl

theorem cell23_6750311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 5, 1, 1, 2, 3].length) (baseStart_6750311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6750311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6750311 prefixEnd_6750311 := by exact prefixLift 6750311
  have htrace : WordTrace (prefixWord ++ tailWord_6750311) baseStart_6750311 baseEnd_6750311 := by
    simpa [prefixWord, tailWord_6750311, baseEnd_6750311] using wordTrace_append hprefix tailTrace_6750311
  have hstable : (prefixWord ++ tailWord_6750311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6750311).length < 2 ^ (prefixWord ++ tailWord_6750311).sum := by decide
  have hdescent : baseEnd_6750311 < baseStart_6750311 := by decide
  rcases family_descends (prefixWord ++ tailWord_6750311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6750341 : List Nat := [1, 3, 1, 1, 5, 1, 2, 3, 2, 1, 3]
def baseStart_6750341 : Nat := 118140960795 + 6750341 * 2 ^ 59
def prefixEnd_6750341 : Nat := 4983230072969 + 3 ^ 40 * 6750341 * 2
def baseEnd_6750341 : Nat := 3466169514751878993493253

theorem tailTrace_6750341 : CollatzResearch.WordTrace tailWord_6750341 prefixEnd_6750341 3466169514751878993493253 := by
  unfold tailWord_6750341
  simp only [CollatzResearch.WordTrace]
  refine ⟨246205162837674898303522877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164136775225116598869015251 246205162837674898303522877)
  ·
    refine ⟨92326936064128086863821079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 246205162837674898303522877 92326936064128086863821079)
    ·
      refine ⟨138490404096192130295731619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92326936064128086863821079 138490404096192130295731619)
      ·
        refine ⟨207735606144288195443597429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138490404096192130295731619 207735606144288195443597429)
        ·
          refine ⟨19475213076027018322837259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 207735606144288195443597429 19475213076027018322837259)
          ·
            refine ⟨29212819614040527484255889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19475213076027018322837259 29212819614040527484255889)
            ·
              refine ⟨21909614710530395613191917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29212819614040527484255889 21909614710530395613191917)
              ·
                refine ⟨8216105516448898354946969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21909614710530395613191917 8216105516448898354946969)
                ·
                  refine ⟨6162079137336673766210227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8216105516448898354946969 6162079137336673766210227)
                  ·
                    refine ⟨9243118706005010649315341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6162079137336673766210227 9243118706005010649315341)
                    ·
                      refine ⟨3466169514751878993493253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9243118706005010649315341 3466169514751878993493253)
                      ·
                        rfl

theorem cell23_6750341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 3, 2, 1, 3].length) (baseStart_6750341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6750341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6750341 prefixEnd_6750341 := by exact prefixLift 6750341
  have htrace : WordTrace (prefixWord ++ tailWord_6750341) baseStart_6750341 baseEnd_6750341 := by
    simpa [prefixWord, tailWord_6750341, baseEnd_6750341] using wordTrace_append hprefix tailTrace_6750341
  have hstable : (prefixWord ++ tailWord_6750341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6750341).length < 2 ^ (prefixWord ++ tailWord_6750341).sum := by decide
  have hdescent : baseEnd_6750341 < baseStart_6750341 := by decide
  rcases family_descends (prefixWord ++ tailWord_6750341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6750368 : List Nat := [2, 1, 1, 4, 2, 2, 4, 1, 1, 3, 2]
def baseStart_6750368 : Nat := 118140960795 + 6750368 * 2 ^ 59
def prefixEnd_6750368 : Nat := 4983230072969 + 3 ^ 40 * 6750368 * 2
def baseEnd_6750368 : Nat := 3466183378729550387855629

theorem tailTrace_6750368 : CollatzResearch.WordTrace tailWord_6750368 prefixEnd_6750368 3466183378729550387855629 := by
  unfold tailWord_6750368
  simp only [CollatzResearch.WordTrace]
  refine ⟨123103073804288540957377879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164137431739051387943170505 123103073804288540957377879)
  ·
    refine ⟨184654610706432811436066819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123103073804288540957377879 184654610706432811436066819)
    ·
      refine ⟨276981916059649217154100229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184654610706432811436066819 276981916059649217154100229)
      ·
        refine ⟨51934109261184228216393793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 276981916059649217154100229 51934109261184228216393793)
        ·
          refine ⟨38950581945888171162295345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51934109261184228216393793 38950581945888171162295345)
          ·
            refine ⟨29212936459416128371721509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38950581945888171162295345 29212936459416128371721509)
            ·
              refine ⟨5477425586140524069697783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29212936459416128371721509 5477425586140524069697783)
              ·
                refine ⟨8216138379210786104546675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5477425586140524069697783 8216138379210786104546675)
                ·
                  refine ⟨12324207568816179156820013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8216138379210786104546675 12324207568816179156820013)
                  ·
                    refine ⟨4621577838306067183807505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12324207568816179156820013 4621577838306067183807505)
                    ·
                      refine ⟨3466183378729550387855629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4621577838306067183807505 3466183378729550387855629)
                      ·
                        rfl

theorem cell23_6750368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 4, 1, 1, 3, 2].length) (baseStart_6750368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6750368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6750368 prefixEnd_6750368 := by exact prefixLift 6750368
  have htrace : WordTrace (prefixWord ++ tailWord_6750368) baseStart_6750368 baseEnd_6750368 := by
    simpa [prefixWord, tailWord_6750368, baseEnd_6750368] using wordTrace_append hprefix tailTrace_6750368
  have hstable : (prefixWord ++ tailWord_6750368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6750368).length < 2 ^ (prefixWord ++ tailWord_6750368).sum := by decide
  have hdescent : baseEnd_6750368 < baseStart_6750368 := by decide
  rcases family_descends (prefixWord ++ tailWord_6750368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6750375 : List Nat := [1, 1, 6, 2, 2, 2, 1, 2, 2, 1, 3]
def baseStart_6750375 : Nat := 118140960795 + 6750375 * 2 ^ 59
def prefixEnd_6750375 : Nat := 4983230072969 + 3 ^ 40 * 6750375 * 2
def baseEnd_6750375 : Nat := 3466186973094131860468097

theorem tailTrace_6750375 : CollatzResearch.WordTrace tailWord_6750375 prefixEnd_6750375 3466186973094131860468097 := by
  unfold tailWord_6750375
  simp only [CollatzResearch.WordTrace]
  refine ⟨246206402919551722110260579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164137601946367814740173719 246206402919551722110260579)
  ·
    refine ⟨369309604379327583165390869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246206402919551722110260579 369309604379327583165390869)
    ·
      refine ⟨17311387705280980460877697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 369309604379327583165390869 17311387705280980460877697)
      ·
        refine ⟨12983540778960735345658273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17311387705280980460877697 12983540778960735345658273)
        ·
          refine ⟨9737655584220551509243705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12983540778960735345658273 9737655584220551509243705)
          ·
            refine ⟨7303241688165413631932779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9737655584220551509243705 7303241688165413631932779)
            ·
              refine ⟨10954862532248120447899169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7303241688165413631932779 10954862532248120447899169)
              ·
                refine ⟨8216146899186090335924377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10954862532248120447899169 8216146899186090335924377)
                ·
                  refine ⟨6162110174389567751943283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8216146899186090335924377 6162110174389567751943283)
                  ·
                    refine ⟨9243165261584351627914925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6162110174389567751943283 9243165261584351627914925)
                    ·
                      refine ⟨3466186973094131860468097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9243165261584351627914925 3466186973094131860468097)
                      ·
                        rfl

theorem cell23_6750375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_6750375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6750375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6750375 prefixEnd_6750375 := by exact prefixLift 6750375
  have htrace : WordTrace (prefixWord ++ tailWord_6750375) baseStart_6750375 baseEnd_6750375 := by
    simpa [prefixWord, tailWord_6750375, baseEnd_6750375] using wordTrace_append hprefix tailTrace_6750375
  have hstable : (prefixWord ++ tailWord_6750375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6750375).length < 2 ^ (prefixWord ++ tailWord_6750375).sum := by decide
  have hdescent : baseEnd_6750375 < baseStart_6750375 := by decide
  rcases family_descends (prefixWord ++ tailWord_6750375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6750402 : List Nat := [3, 5, 1, 1, 1, 2, 2, 2, 1, 3, 2]
def baseStart_6750402 : Nat := 118140960795 + 6750402 * 2 ^ 59
def prefixEnd_6750402 : Nat := 4983230072969 + 3 ^ 40 * 6750402 * 2
def baseEnd_6750402 : Nat := 3466200837071803254830473

theorem tailTrace_6750402 : CollatzResearch.WordTrace tailWord_6750402 prefixEnd_6750402 3466200837071803254830473 := by
  unfold tailWord_6750402
  simp only [CollatzResearch.WordTrace]
  refine ⟨61551846922613476430373365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164138258460302603814328973 61551846922613476430373365)
  ·
    refine ⟨5770485648995013415347503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 61551846922613476430373365 5770485648995013415347503)
    ·
      refine ⟨8655728473492520123021255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5770485648995013415347503 8655728473492520123021255)
      ·
        refine ⟨12983592710238780184531883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8655728473492520123021255 12983592710238780184531883)
        ·
          refine ⟨19475389065358170276797825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12983592710238780184531883 19475389065358170276797825)
          ·
            refine ⟨14606541799018627707598369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19475389065358170276797825 14606541799018627707598369)
            ·
              refine ⟨10954906349263970780698777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14606541799018627707598369 10954906349263970780698777)
              ·
                refine ⟨8216179761947978085524083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10954906349263970780698777 8216179761947978085524083)
                ·
                  refine ⟨12324269642921967128286125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8216179761947978085524083 12324269642921967128286125)
                  ·
                    refine ⟨4621601116095737673107297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12324269642921967128286125 4621601116095737673107297)
                    ·
                      refine ⟨3466200837071803254830473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4621601116095737673107297 3466200837071803254830473)
                      ·
                        rfl

theorem cell23_6750402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 2, 1, 3, 2].length) (baseStart_6750402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6750402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6750402 prefixEnd_6750402 := by exact prefixLift 6750402
  have htrace : WordTrace (prefixWord ++ tailWord_6750402) baseStart_6750402 baseEnd_6750402 := by
    simpa [prefixWord, tailWord_6750402, baseEnd_6750402] using wordTrace_append hprefix tailTrace_6750402
  have hstable : (prefixWord ++ tailWord_6750402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6750402).length < 2 ^ (prefixWord ++ tailWord_6750402).sum := by decide
  have hdescent : baseEnd_6750402 < baseStart_6750402 := by decide
  rcases family_descends (prefixWord ++ tailWord_6750402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6750404 : List Nat := [2, 3, 3, 1, 2, 1, 2, 2, 7]
def baseStart_6750404 : Nat := 118140960795 + 6750404 * 2 ^ 59
def prefixEnd_6750404 : Nat := 4983230072969 + 3 ^ 40 * 6750404 * 2
def baseEnd_6750404 : Nat := 385133540448123583000607

theorem tailTrace_6750404 : CollatzResearch.WordTrace tailWord_6750404 prefixEnd_6750404 385133540448123583000607 := by
  unfold tailWord_6750404
  simp only [CollatzResearch.WordTrace]
  refine ⟨123103730318223330031533133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164138307090964440042044177 123103730318223330031533133)
  ·
    refine ⟨46163898869333748761824925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123103730318223330031533133 46163898869333748761824925)
    ·
      refine ⟨17311462076000155785684347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46163898869333748761824925 17311462076000155785684347)
      ·
        refine ⟨25967193114000233678526521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17311462076000155785684347 25967193114000233678526521)
        ·
          refine ⟨19475394835500175258894891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25967193114000233678526521 19475394835500175258894891)
          ·
            refine ⟨29213092253250262888342337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19475394835500175258894891 29213092253250262888342337)
            ·
              refine ⟨21909819189937697166256753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29213092253250262888342337 21909819189937697166256753)
              ·
                refine ⟨16432364392453272874692565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21909819189937697166256753 16432364392453272874692565)
                ·
                  refine ⟨385133540448123583000607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16432364392453272874692565 385133540448123583000607)
                  ·
                    rfl

theorem cell23_6750404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 2, 7].length) (baseStart_6750404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6750404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6750404 prefixEnd_6750404 := by exact prefixLift 6750404
  have htrace : WordTrace (prefixWord ++ tailWord_6750404) baseStart_6750404 baseEnd_6750404 := by
    simpa [prefixWord, tailWord_6750404, baseEnd_6750404] using wordTrace_append hprefix tailTrace_6750404
  have hstable : (prefixWord ++ tailWord_6750404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6750404).length < 2 ^ (prefixWord ++ tailWord_6750404).sum := by decide
  have hdescent : baseEnd_6750404 < baseStart_6750404 := by decide
  rcases family_descends (prefixWord ++ tailWord_6750404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6750417 : List Nat := [1, 2, 2, 1, 2, 2, 4, 1, 1, 7]
def baseStart_6750417 : Nat := 118140960795 + 6750417 * 2 ^ 59
def prefixEnd_6750417 : Nat := 4983230072969 + 3 ^ 40 * 6750417 * 2
def baseEnd_6750417 : Nat := 1155402846427206898714301

theorem tailTrace_6750417 : CollatzResearch.WordTrace tailWord_6750417 prefixEnd_6750417 1155402846427206898714301 := by
  unfold tailWord_6750417
  simp only [CollatzResearch.WordTrace]
  refine ⟨246207934785399563283289505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164138623190266375522193003 246207934785399563283289505)
  ·
    refine ⟨184655951089049672462467129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246207934785399563283289505 184655951089049672462467129)
    ·
      refine ⟨138491963316787254346850347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184655951089049672462467129 138491963316787254346850347)
      ·
        refine ⟨207737944975180881520275521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138491963316787254346850347 207737944975180881520275521)
        ·
          refine ⟨155803458731385661140206641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207737944975180881520275521 155803458731385661140206641)
          ·
            refine ⟨116852594048539245855154981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155803458731385661140206641 116852594048539245855154981)
            ·
              refine ⟨21909861384101108597841559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 116852594048539245855154981 21909861384101108597841559)
              ·
                refine ⟨32864792076151662896762339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21909861384101108597841559 32864792076151662896762339)
                ·
                  refine ⟨49297188114227494345143509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32864792076151662896762339 49297188114227494345143509)
                  ·
                    refine ⟨1155402846427206898714301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49297188114227494345143509 1155402846427206898714301)
                    ·
                      rfl

theorem cell23_6750417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 1, 1, 7].length) (baseStart_6750417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6750417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6750417 prefixEnd_6750417 := by exact prefixLift 6750417
  have htrace : WordTrace (prefixWord ++ tailWord_6750417) baseStart_6750417 baseEnd_6750417 := by
    simpa [prefixWord, tailWord_6750417, baseEnd_6750417] using wordTrace_append hprefix tailTrace_6750417
  have hstable : (prefixWord ++ tailWord_6750417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6750417).length < 2 ^ (prefixWord ++ tailWord_6750417).sum := by decide
  have hdescent : baseEnd_6750417 < baseStart_6750417 := by decide
  rcases family_descends (prefixWord ++ tailWord_6750417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6750454 : List Nat := [5, 1, 1, 1, 1, 1, 2, 1, 3, 3, 4]
def baseStart_6750454 : Nat := 118140960795 + 6750454 * 2 ^ 59
def prefixEnd_6750454 : Nat := 4983230072969 + 3 ^ 40 * 6750454 * 2
def baseEnd_6750454 : Nat := 3466227538065837051380233

theorem tailTrace_6750454 : CollatzResearch.WordTrace tailWord_6750454 prefixEnd_6750454 3466227538065837051380233 := by
  unfold tailWord_6750454
  simp only [CollatzResearch.WordTrace]
  refine ⟨15388080267891594912649151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 164139522857510345734924277 15388080267891594912649151)
  ·
    refine ⟨23082120401837392368973727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15388080267891594912649151 23082120401837392368973727)
    ·
      refine ⟨34623180602756088553460591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23082120401837392368973727 34623180602756088553460591)
      ·
        refine ⟨51934770904134132830190887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34623180602756088553460591 51934770904134132830190887)
        ·
          refine ⟨77902156356201199245286331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51934770904134132830190887 77902156356201199245286331)
          ·
            refine ⟨116853234534301798867929497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77902156356201199245286331 116853234534301798867929497)
            ·
              refine ⟨87639925900726349150947123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116853234534301798867929497 87639925900726349150947123)
              ·
                refine ⟨131459888851089523726420685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87639925900726349150947123 131459888851089523726420685)
                ·
                  refine ⟨49297458319158571397407757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 131459888851089523726420685 49297458319158571397407757)
                  ·
                    refine ⟨18486546869684464274027909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49297458319158571397407757 18486546869684464274027909)
                    ·
                      refine ⟨3466227538065837051380233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18486546869684464274027909 3466227538065837051380233)
                      ·
                        rfl

theorem cell23_6750454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 3, 3, 4].length) (baseStart_6750454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6750454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6750454 prefixEnd_6750454 := by exact prefixLift 6750454
  have htrace : WordTrace (prefixWord ++ tailWord_6750454) baseStart_6750454 baseEnd_6750454 := by
    simpa [prefixWord, tailWord_6750454, baseEnd_6750454] using wordTrace_append hprefix tailTrace_6750454
  have hstable : (prefixWord ++ tailWord_6750454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6750454).length < 2 ^ (prefixWord ++ tailWord_6750454).sum := by decide
  have hdescent : baseEnd_6750454 < baseStart_6750454 := by decide
  rcases family_descends (prefixWord ++ tailWord_6750454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6750464 : List Nat := [2, 1, 1, 2, 1, 1, 4, 4, 3, 4]
def baseStart_6750464 : Nat := 118140960795 + 6750464 * 2 ^ 59
def prefixEnd_6750464 : Nat := 4983230072969 + 3 ^ 40 * 6750464 * 2
def baseEnd_6750464 : Nat := 1155410890957460670751729

theorem tailTrace_6750464 : CollatzResearch.WordTrace tailWord_6750464 prefixEnd_6750464 1155410890957460670751729 := by
  unfold tailWord_6750464
  simp only [CollatzResearch.WordTrace]
  refine ⟨123104824508114645155125223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164139766010819526873500297 123104824508114645155125223)
  ·
    refine ⟨184657236762171967732687835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123104824508114645155125223 184657236762171967732687835)
    ·
      refine ⟨276985855143257951599031753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184657236762171967732687835 276985855143257951599031753)
      ·
        refine ⟨207739391357443463699273815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 276985855143257951599031753 207739391357443463699273815)
        ·
          refine ⟨311609087036165195548910723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207739391357443463699273815 311609087036165195548910723)
          ·
            refine ⟨467413630554247793323366085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 311609087036165195548910723 467413630554247793323366085)
            ·
              refine ⟨87640055728921461248131141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 467413630554247793323366085 87640055728921461248131141)
              ·
                refine ⟨16432510449172773984024589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87640055728921461248131141 16432510449172773984024589)
                ·
                  refine ⟨6162191418439790244009221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16432510449172773984024589 6162191418439790244009221)
                  ·
                    refine ⟨1155410890957460670751729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6162191418439790244009221 1155410890957460670751729)
                    ·
                      rfl

theorem cell23_6750464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 4, 3, 4].length) (baseStart_6750464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6750464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6750464 prefixEnd_6750464 := by exact prefixLift 6750464
  have htrace : WordTrace (prefixWord ++ tailWord_6750464) baseStart_6750464 baseEnd_6750464 := by
    simpa [prefixWord, tailWord_6750464, baseEnd_6750464] using wordTrace_append hprefix tailTrace_6750464
  have hstable : (prefixWord ++ tailWord_6750464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6750464).length < 2 ^ (prefixWord ++ tailWord_6750464).sum := by decide
  have hdescent : baseEnd_6750464 < baseStart_6750464 := by decide
  rcases family_descends (prefixWord ++ tailWord_6750464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6750474 : List Nat := [3, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3]
def baseStart_6750474 : Nat := 118140960795 + 6750474 * 2 ^ 59
def prefixEnd_6750474 : Nat := 4983230072969 + 3 ^ 40 * 6750474 * 2
def baseEnd_6750474 : Nat := 3466237807678926973130141

theorem tailTrace_6750474 : CollatzResearch.WordTrace tailWord_6750474 prefixEnd_6750474 3466237807678926973130141 := by
  unfold tailWord_6750474
  simp only [CollatzResearch.WordTrace]
  refine ⟨61552503436548265504528619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164140009164128708012076317 61552503436548265504528619)
  ·
    refine ⟨92328755154822398256792929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61552503436548265504528619 92328755154822398256792929)
    ·
      refine ⟨69246566366116798692594697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92328755154822398256792929 69246566366116798692594697)
      ·
        refine ⟨51934924774587599019446023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69246566366116798692594697 51934924774587599019446023)
        ·
          refine ⟨77902387161881398529169035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51934924774587599019446023 77902387161881398529169035)
          ·
            refine ⟨116853580742822097793753553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77902387161881398529169035 116853580742822097793753553)
            ·
              refine ⟨87640185557116573345315165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116853580742822097793753553 87640185557116573345315165)
              ·
                refine ⟨32865069583918715004493187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87640185557116573345315165 32865069583918715004493187)
                ·
                  refine ⟨49297604375878072506739781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32865069583918715004493187 49297604375878072506739781)
                  ·
                    refine ⟨9243300820477138595013709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49297604375878072506739781 9243300820477138595013709)
                    ·
                      refine ⟨3466237807678926973130141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9243300820477138595013709 3466237807678926973130141)
                      ·
                        rfl

theorem cell23_6750474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3].length) (baseStart_6750474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6750474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6750474 prefixEnd_6750474 := by exact prefixLift 6750474
  have htrace : WordTrace (prefixWord ++ tailWord_6750474) baseStart_6750474 baseEnd_6750474 := by
    simpa [prefixWord, tailWord_6750474, baseEnd_6750474] using wordTrace_append hprefix tailTrace_6750474
  have hstable : (prefixWord ++ tailWord_6750474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6750474).length < 2 ^ (prefixWord ++ tailWord_6750474).sum := by decide
  have hdescent : baseEnd_6750474 < baseStart_6750474 := by decide
  rcases family_descends (prefixWord ++ tailWord_6750474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6750524 : List Nat := [2, 2, 2, 2, 1, 2, 1, 3, 3, 5]
def baseStart_6750524 : Nat := 118140960795 + 6750524 * 2 ^ 59
def prefixEnd_6750524 : Nat := 4983230072969 + 3 ^ 40 * 6750524 * 2
def baseEnd_6750524 : Nat := 1155421160570550592501637

theorem tailTrace_6750524 : CollatzResearch.WordTrace tailWord_6750524 prefixEnd_6750524 1155421160570550592501637 := by
  unfold tailWord_6750524
  simp only [CollatzResearch.WordTrace]
  refine ⟨123105918698005960278717313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164141224930674613704956417 123105918698005960278717313)
  ·
    refine ⟨92329439023504470209037985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123105918698005960278717313 92329439023504470209037985)
    ·
      refine ⟨69247079267628352656778489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92329439023504470209037985 69247079267628352656778489)
      ·
        refine ⟨51935309450721264492583867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69247079267628352656778489 51935309450721264492583867)
        ·
          refine ⟨77902964176081896738875801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51935309450721264492583867 77902964176081896738875801)
          ·
            refine ⟨58427223132061422554156851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77902964176081896738875801 58427223132061422554156851)
            ·
              refine ⟨87640834698092133831235277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58427223132061422554156851 87640834698092133831235277)
              ·
                refine ⟨32865313011784550186713229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87640834698092133831235277 32865313011784550186713229)
                ·
                  refine ⟨12324492379419206320017461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32865313011784550186713229 12324492379419206320017461)
                  ·
                    refine ⟨1155421160570550592501637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12324492379419206320017461 1155421160570550592501637)
                    ·
                      rfl

theorem cell23_6750524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 3, 3, 5].length) (baseStart_6750524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6750524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6750524 prefixEnd_6750524 := by exact prefixLift 6750524
  have htrace : WordTrace (prefixWord ++ tailWord_6750524) baseStart_6750524 baseEnd_6750524 := by
    simpa [prefixWord, tailWord_6750524, baseEnd_6750524] using wordTrace_append hprefix tailTrace_6750524
  have hstable : (prefixWord ++ tailWord_6750524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6750524).length < 2 ^ (prefixWord ++ tailWord_6750524).sum := by decide
  have hdescent : baseEnd_6750524 < baseStart_6750524 := by decide
  rcases family_descends (prefixWord ++ tailWord_6750524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6750532 : List Nat := [2, 3, 4, 1, 2, 1, 2, 3, 1, 4]
def baseStart_6750532 : Nat := 118140960795 + 6750532 * 2 ^ 59
def prefixEnd_6750532 : Nat := 4983230072969 + 3 ^ 40 * 6750532 * 2
def baseEnd_6750532 : Nat := 1155422529852295915401625

theorem tailTrace_6750532 : CollatzResearch.WordTrace tailWord_6750532 prefixEnd_6750532 1155422529852295915401625 := by
  unfold tailWord_6750532
  simp only [CollatzResearch.WordTrace]
  refine ⟨123106064589991468961862925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164141419453321958615817233 123106064589991468961862925)
  ·
    refine ⟨46164774221246800860698597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123106064589991468961862925 46164774221246800860698597)
    ·
      refine ⟨8655895166483775161380987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46164774221246800860698597 8655895166483775161380987)
      ·
        refine ⟨12983842749725662742071481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8655895166483775161380987 12983842749725662742071481)
        ·
          refine ⟨9737882062294247056553611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12983842749725662742071481 9737882062294247056553611)
          ·
            refine ⟨14606823093441370584830417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9737882062294247056553611 14606823093441370584830417)
            ·
              refine ⟨10955117320081027938622813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14606823093441370584830417 10955117320081027938622813)
              ·
                refine ⟨4108168995030385476983555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10955117320081027938622813 4108168995030385476983555)
                ·
                  refine ⟨6162253492545578215475333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4108168995030385476983555 6162253492545578215475333)
                  ·
                    refine ⟨1155422529852295915401625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6162253492545578215475333 1155422529852295915401625)
                    ·
                      rfl

theorem cell23_6750532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_6750532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6750532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6750532 prefixEnd_6750532 := by exact prefixLift 6750532
  have htrace : WordTrace (prefixWord ++ tailWord_6750532) baseStart_6750532 baseEnd_6750532 := by
    simpa [prefixWord, tailWord_6750532, baseEnd_6750532] using wordTrace_append hprefix tailTrace_6750532
  have hstable : (prefixWord ++ tailWord_6750532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6750532).length < 2 ^ (prefixWord ++ tailWord_6750532).sum := by decide
  have hdescent : baseEnd_6750532 < baseStart_6750532 := by decide
  rcases family_descends (prefixWord ++ tailWord_6750532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6750578 : List Nat := [3, 2, 1, 2, 1, 4, 2, 2, 1, 1, 4]
def baseStart_6750578 : Nat := 118140960795 + 6750578 * 2 ^ 59
def prefixEnd_6750578 : Nat := 4983230072969 + 3 ^ 40 * 6750578 * 2
def baseEnd_6750578 : Nat := 3466291209666994566229663

theorem tailTrace_6750578 : CollatzResearch.WordTrace tailWord_6750578 prefixEnd_6750578 3466291209666994566229663 := by
  unfold tailWord_6750578
  simp only [CollatzResearch.WordTrace]
  refine ⟨61553451734454071944975097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164142537958544191853266925 61553451734454071944975097)
  ·
    refine ⟨46165088800840553958731323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61553451734454071944975097 46165088800840553958731323)
    ·
      refine ⟨69247633201260830938096985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46165088800840553958731323 69247633201260830938096985)
      ·
        refine ⟨51935724900945623203572739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69247633201260830938096985 51935724900945623203572739)
        ·
          refine ⟨77903587351418434805359109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51935724900945623203572739 77903587351418434805359109)
          ·
            refine ⟨14606922628390956526004833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77903587351418434805359109 14606922628390956526004833)
            ·
              refine ⟨10955191971293217394503625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14606922628390956526004833 10955191971293217394503625)
              ·
                refine ⟨8216393978469913045877719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10955191971293217394503625 8216393978469913045877719)
                ·
                  refine ⟨12324590967704869568816579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8216393978469913045877719 12324590967704869568816579)
                  ·
                    refine ⟨18486886451557304353224869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12324590967704869568816579 18486886451557304353224869)
                    ·
                      refine ⟨3466291209666994566229663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18486886451557304353224869 3466291209666994566229663)
                      ·
                        rfl

theorem cell23_6750578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 2, 1, 1, 4].length) (baseStart_6750578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6750578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6750578 prefixEnd_6750578 := by exact prefixLift 6750578
  have htrace : WordTrace (prefixWord ++ tailWord_6750578) baseStart_6750578 baseEnd_6750578 := by
    simpa [prefixWord, tailWord_6750578, baseEnd_6750578] using wordTrace_append hprefix tailTrace_6750578
  have hstable : (prefixWord ++ tailWord_6750578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6750578).length < 2 ^ (prefixWord ++ tailWord_6750578).sum := by decide
  have hdescent : baseEnd_6750578 < baseStart_6750578 := by decide
  rcases family_descends (prefixWord ++ tailWord_6750578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6750622 : List Nat := [4, 3, 1, 2, 1, 1, 4, 1, 2, 4]
def baseStart_6750622 : Nat := 118140960795 + 6750622 * 2 ^ 59
def prefixEnd_6750622 : Nat := 4983230072969 + 3 ^ 40 * 6750622 * 2
def baseEnd_6750622 : Nat := 1155437934271930798026487

theorem tailTrace_6750622 : CollatzResearch.WordTrace tailWord_6750622 prefixEnd_6750622 1155437934271930798026487 := by
  unfold tailWord_6750622
  simp only [CollatzResearch.WordTrace]
  refine ⟨30776926468707110411812765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164143607833104588863001413 30776926468707110411812765)
  ·
    refine ⟨11541347425765166404429787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30776926468707110411812765 11541347425765166404429787)
    ·
      refine ⟨17312021138647749606644681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11541347425765166404429787 17312021138647749606644681)
      ·
        refine ⟨12984015853985812204983511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17312021138647749606644681 12984015853985812204983511)
        ·
          refine ⟨19476023780978718307475267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12984015853985812204983511 19476023780978718307475267)
          ·
            refine ⟨29214035671468077461212901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19476023780978718307475267 29214035671468077461212901)
            ·
              refine ⟨5477631688400264523977419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29214035671468077461212901 5477631688400264523977419)
              ·
                refine ⟨8216447532600396785966129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5477631688400264523977419 8216447532600396785966129)
                ·
                  refine ⟨6162335649450297589474597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8216447532600396785966129 6162335649450297589474597)
                  ·
                    refine ⟨1155437934271930798026487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6162335649450297589474597 1155437934271930798026487)
                    ·
                      rfl

theorem cell23_6750622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 4, 1, 2, 4].length) (baseStart_6750622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6750622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6750622 prefixEnd_6750622 := by exact prefixLift 6750622
  have htrace : WordTrace (prefixWord ++ tailWord_6750622) baseStart_6750622 baseEnd_6750622 := by
    simpa [prefixWord, tailWord_6750622, baseEnd_6750622] using wordTrace_append hprefix tailTrace_6750622
  have hstable : (prefixWord ++ tailWord_6750622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6750622).length < 2 ^ (prefixWord ++ tailWord_6750622).sum := by decide
  have hdescent : baseEnd_6750622 < baseStart_6750622 := by decide
  rcases family_descends (prefixWord ++ tailWord_6750622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6750632 : List Nat := [2, 1, 6, 1, 1, 3, 1, 2, 1, 2, 3]
def baseStart_6750632 : Nat := 118140960795 + 6750632 * 2 ^ 59
def prefixEnd_6750632 : Nat := 4983230072969 + 3 ^ 40 * 6750632 * 2
def baseEnd_6750632 : Nat := 3466318937622337354954415

theorem tailTrace_6750632 : CollatzResearch.WordTrace tailWord_6750632 prefixEnd_6750632 3466318937622337354954415 := by
  unfold tailWord_6750632
  simp only [CollatzResearch.WordTrace]
  refine ⟨123107888239810327501183075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164143850986413770001577433 123107888239810327501183075)
  ·
    refine ⟨184661832359715491251774613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123107888239810327501183075 184661832359715491251774613)
    ·
      refine ⟨8656023391861663652426935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 184661832359715491251774613 8656023391861663652426935)
      ·
        refine ⟨12984035087792495478640403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8656023391861663652426935 12984035087792495478640403)
        ·
          refine ⟨19476052631688743217960605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12984035087792495478640403 19476052631688743217960605)
          ·
            refine ⟨7303519736883278706735227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19476052631688743217960605 7303519736883278706735227)
            ·
              refine ⟨10955279605324918060102841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7303519736883278706735227 10955279605324918060102841)
              ·
                refine ⟨8216459703993688545077131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10955279605324918060102841 8216459703993688545077131)
                ·
                  refine ⟨12324689555990532817615697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8216459703993688545077131 12324689555990532817615697)
                  ·
                    refine ⟨9243517166992899613211773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12324689555990532817615697 9243517166992899613211773)
                    ·
                      refine ⟨3466318937622337354954415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9243517166992899613211773 3466318937622337354954415)
                      ·
                        rfl

theorem cell23_6750632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_6750632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6750632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6750632 prefixEnd_6750632 := by exact prefixLift 6750632
  have htrace : WordTrace (prefixWord ++ tailWord_6750632) baseStart_6750632 baseEnd_6750632 := by
    simpa [prefixWord, tailWord_6750632, baseEnd_6750632] using wordTrace_append hprefix tailTrace_6750632
  have hstable : (prefixWord ++ tailWord_6750632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6750632).length < 2 ^ (prefixWord ++ tailWord_6750632).sum := by decide
  have hdescent : baseEnd_6750632 < baseStart_6750632 := by decide
  rcases family_descends (prefixWord ++ tailWord_6750632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6750678 : List Nat := [5, 2, 1, 1, 1, 1, 3, 1, 2, 6]
def baseStart_6750678 : Nat := 118140960795 + 6750678 * 2 ^ 59
def prefixEnd_6750678 : Nat := 4983230072969 + 3 ^ 40 * 6750678 * 2
def baseEnd_6750678 : Nat := 1155447519244148058326401

theorem tailTrace_6750678 : CollatzResearch.WordTrace tailWord_6750678 prefixEnd_6750678 1155447519244148058326401 := by
  unfold tailWord_6750678
  simp only [CollatzResearch.WordTrace]
  refine ⟨15388590889840875303658793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 164144969491636003239027125 15388590889840875303658793)
  ·
    refine ⟨11541443167380656477744095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15388590889840875303658793 11541443167380656477744095)
    ·
      refine ⟨17312164751070984716616143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11541443167380656477744095 17312164751070984716616143)
      ·
        refine ⟨25968247126606477074924215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17312164751070984716616143 25968247126606477074924215)
        ·
          refine ⟨38952370689909715612386323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25968247126606477074924215 38952370689909715612386323)
          ·
            refine ⟨58428556034864573418579485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38952370689909715612386323 58428556034864573418579485)
            ·
              refine ⟨21910708513074215031967307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58428556034864573418579485 21910708513074215031967307)
              ·
                refine ⟨32866062769611322547950961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21910708513074215031967307 32866062769611322547950961)
                ·
                  refine ⟨24649547077208491910963221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32866062769611322547950961 24649547077208491910963221)
                  ·
                    refine ⟨1155447519244148058326401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24649547077208491910963221 1155447519244148058326401)
                    ·
                      rfl

theorem cell23_6750678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_6750678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6750678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6750678 prefixEnd_6750678 := by exact prefixLift 6750678
  have htrace : WordTrace (prefixWord ++ tailWord_6750678) baseStart_6750678 baseEnd_6750678 := by
    simpa [prefixWord, tailWord_6750678, baseEnd_6750678] using wordTrace_append hprefix tailTrace_6750678
  have hstable : (prefixWord ++ tailWord_6750678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6750678).length < 2 ^ (prefixWord ++ tailWord_6750678).sum := by decide
  have hdescent : baseEnd_6750678 < baseStart_6750678 := by decide
  rcases family_descends (prefixWord ++ tailWord_6750678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6750681 : List Nat := [1, 2, 1, 2, 4, 1, 3, 1, 2, 2, 4]
def baseStart_6750681 : Nat := 118140960795 + 6750681 * 2 ^ 59
def prefixEnd_6750681 : Nat := 4983230072969 + 3 ^ 40 * 6750681 * 2
def baseEnd_6750681 : Nat := 3466344098174407663241689

theorem tailTrace_6750681 : CollatzResearch.WordTrace tailWord_6750681 prefixEnd_6750681 3466344098174407663241689 := by
  unfold tailWord_6750681
  simp only [CollatzResearch.WordTrace]
  refine ⟨246217563656443136370899897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164145042437628757580599931 246217563656443136370899897)
  ·
    refine ⟨184663172742332352278174923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246217563656443136370899897 184663172742332352278174923)
    ·
      refine ⟨276994759113498528417262385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184663172742332352278174923 276994759113498528417262385)
      ·
        refine ⟨207746069335123896312946789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 276994759113498528417262385 207746069335123896312946789)
        ·
          refine ⟨38952388000335730558677523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 207746069335123896312946789 38952388000335730558677523)
          ·
            refine ⟨58428582000503595838016285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38952388000335730558677523 58428582000503595838016285)
            ·
              refine ⟨21910718250188848439256107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58428582000503595838016285 21910718250188848439256107)
              ·
                refine ⟨32866077375283272658884161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21910718250188848439256107 32866077375283272658884161)
                ·
                  refine ⟨24649558031462454494163121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32866077375283272658884161 24649558031462454494163121)
                  ·
                    refine ⟨18487168523596840870622341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24649558031462454494163121 18487168523596840870622341)
                    ·
                      refine ⟨3466344098174407663241689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18487168523596840870622341 3466344098174407663241689)
                      ·
                        rfl

theorem cell23_6750681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 1, 2, 2, 4].length) (baseStart_6750681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6750681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6750681 prefixEnd_6750681 := by exact prefixLift 6750681
  have htrace : WordTrace (prefixWord ++ tailWord_6750681) baseStart_6750681 baseEnd_6750681 := by
    simpa [prefixWord, tailWord_6750681, baseEnd_6750681] using wordTrace_append hprefix tailTrace_6750681
  have hstable : (prefixWord ++ tailWord_6750681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6750681).length < 2 ^ (prefixWord ++ tailWord_6750681).sum := by decide
  have hdescent : baseEnd_6750681 < baseStart_6750681 := by decide
  rcases family_descends (prefixWord ++ tailWord_6750681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6750685 : List Nat := [1, 4, 3, 1, 1, 1, 4, 1, 1, 4, 2]
def baseStart_6750685 : Nat := 118140960795 + 6750685 * 2 ^ 59
def prefixEnd_6750685 : Nat := 4983230072969 + 3 ^ 40 * 6750685 * 2
def baseEnd_6750685 : Nat := 3466346152097025647591671

theorem tailTrace_6750685 : CollatzResearch.WordTrace tailWord_6750685 prefixEnd_6750685 3466346152097025647591671 := by
  unfold tailWord_6750685
  simp only [CollatzResearch.WordTrace]
  refine ⟨246217709548428645054045509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164145139698952430036030339 246217709548428645054045509)
  ·
    refine ⟨46165820540330370947633533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 246217709548428645054045509 46165820540330370947633533)
    ·
      refine ⟨17312182702623889105362575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46165820540330370947633533 17312182702623889105362575)
      ·
        refine ⟨25968274053935833658043863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17312182702623889105362575 25968274053935833658043863)
        ·
          refine ⟨38952411080903750487065795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25968274053935833658043863 38952411080903750487065795)
          ·
            refine ⟨58428616621355625730598693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38952411080903750487065795 58428616621355625730598693)
            ·
              refine ⟨10955365616504179824487255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58428616621355625730598693 10955365616504179824487255)
              ·
                refine ⟨16433048424756269736730883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10955365616504179824487255 16433048424756269736730883)
                ·
                  refine ⟨24649572637134404605096325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16433048424756269736730883 24649572637134404605096325)
                  ·
                    refine ⟨4621794869462700863455561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24649572637134404605096325 4621794869462700863455561)
                    ·
                      refine ⟨3466346152097025647591671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4621794869462700863455561 3466346152097025647591671)
                      ·
                        rfl

theorem cell23_6750685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 1, 1, 4, 2].length) (baseStart_6750685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6750685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6750685 prefixEnd_6750685 := by exact prefixLift 6750685
  have htrace : WordTrace (prefixWord ++ tailWord_6750685) baseStart_6750685 baseEnd_6750685 := by
    simpa [prefixWord, tailWord_6750685, baseEnd_6750685] using wordTrace_append hprefix tailTrace_6750685
  have hstable : (prefixWord ++ tailWord_6750685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6750685).length < 2 ^ (prefixWord ++ tailWord_6750685).sum := by decide
  have hdescent : baseEnd_6750685 < baseStart_6750685 := by decide
  rcases family_descends (prefixWord ++ tailWord_6750685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6750706 : List Nat := [3, 2, 1, 4, 3, 1, 2, 1, 1, 3, 2]
def baseStart_6750706 : Nat := 118140960795 + 6750706 * 2 ^ 59
def prefixEnd_6750706 : Nat := 4983230072969 + 3 ^ 40 * 6750706 * 2
def baseEnd_6750706 : Nat := 3466356935190770065429075

theorem tailTrace_6750706 : CollatzResearch.WordTrace tailWord_6750706 prefixEnd_6750706 3466356935190770065429075 := by
  unfold tailWord_6750706
  simp only [CollatzResearch.WordTrace]
  refine ⟨61554618870338141410139993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164145650320901710427039981 61554618870338141410139993)
  ·
    refine ⟨46165964152753606057604995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61554618870338141410139993 46165964152753606057604995)
    ·
      refine ⟨69248946229130409086407493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46165964152753606057604995 69248946229130409086407493)
      ·
        refine ⟨12984177417961951703701405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69248946229130409086407493 12984177417961951703701405)
        ·
          refine ⟨4869066531735731888888027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12984177417961951703701405 4869066531735731888888027)
          ·
            refine ⟨7303599797603597833332041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4869066531735731888888027 7303599797603597833332041)
            ·
              refine ⟨5477699848202698374999031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7303599797603597833332041 5477699848202698374999031)
              ·
                refine ⟨8216549772304047562498547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5477699848202698374999031 8216549772304047562498547)
                ·
                  refine ⟨12324824658456071343747821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8216549772304047562498547 12324824658456071343747821)
                  ·
                    refine ⟨4621809246921026753905433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12324824658456071343747821 4621809246921026753905433)
                    ·
                      refine ⟨3466356935190770065429075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4621809246921026753905433 3466356935190770065429075)
                      ·
                        rfl

theorem cell23_6750706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 2, 1, 1, 3, 2].length) (baseStart_6750706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6750706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6750706 prefixEnd_6750706 := by exact prefixLift 6750706
  have htrace : WordTrace (prefixWord ++ tailWord_6750706) baseStart_6750706 baseEnd_6750706 := by
    simpa [prefixWord, tailWord_6750706, baseEnd_6750706] using wordTrace_append hprefix tailTrace_6750706
  have hstable : (prefixWord ++ tailWord_6750706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6750706).length < 2 ^ (prefixWord ++ tailWord_6750706).sum := by decide
  have hdescent : baseEnd_6750706 < baseStart_6750706 := by decide
  rcases family_descends (prefixWord ++ tailWord_6750706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6750741 : List Nat := [1, 3, 2, 1, 3, 1, 1, 1, 3, 3, 4]
def baseStart_6750741 : Nat := 118140960795 + 6750741 * 2 ^ 59
def prefixEnd_6750741 : Nat := 4983230072969 + 3 ^ 40 * 6750741 * 2
def baseEnd_6750741 : Nat := 3466374907013677428491413

theorem tailTrace_6750741 : CollatzResearch.WordTrace tailWord_6750741 prefixEnd_6750741 3466374907013677428491413 := by
  unfold tailWord_6750741
  simp only [CollatzResearch.WordTrace]
  refine ⟨246219752036225766618084077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164146501357483844412056051 246219752036225766618084077)
  ·
    refine ⟨92332407013584662481781529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 246219752036225766618084077 92332407013584662481781529)
    ·
      refine ⟨69249305260188496861336147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92332407013584662481781529 69249305260188496861336147)
      ·
        refine ⟨103873957890282745292004221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69249305260188496861336147 103873957890282745292004221)
        ·
          refine ⟨38952734208856029484501583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103873957890282745292004221 38952734208856029484501583)
          ·
            refine ⟨58429101313284044226752375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38952734208856029484501583 58429101313284044226752375)
            ·
              refine ⟨87643651969926066340128563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58429101313284044226752375 87643651969926066340128563)
              ·
                refine ⟨131465477954889099510192845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87643651969926066340128563 131465477954889099510192845)
                ·
                  refine ⟨49299554233083412316322317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 131465477954889099510192845 49299554233083412316322317)
                  ·
                    refine ⟨18487332837406279618620869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49299554233083412316322317 18487332837406279618620869)
                    ·
                      refine ⟨3466374907013677428491413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18487332837406279618620869 3466374907013677428491413)
                      ·
                        rfl

theorem cell23_6750741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 3, 3, 4].length) (baseStart_6750741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6750741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6750741 prefixEnd_6750741 := by exact prefixLift 6750741
  have htrace : WordTrace (prefixWord ++ tailWord_6750741) baseStart_6750741 baseEnd_6750741 := by
    simpa [prefixWord, tailWord_6750741, baseEnd_6750741] using wordTrace_append hprefix tailTrace_6750741
  have hstable : (prefixWord ++ tailWord_6750741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6750741).length < 2 ^ (prefixWord ++ tailWord_6750741).sum := by decide
  have hdescent : baseEnd_6750741 < baseStart_6750741 := by decide
  rcases family_descends (prefixWord ++ tailWord_6750741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6750759 : List Nat := [1, 1, 7, 2, 1, 2, 1, 3, 5]
def baseStart_6750759 : Nat := 118140960795 + 6750759 * 2 ^ 59
def prefixEnd_6750759 : Nat := 4983230072969 + 3 ^ 40 * 6750759 * 2
def baseEnd_6750759 : Nat := 385153794407273150896259

theorem tailTrace_6750759 : CollatzResearch.WordTrace tailWord_6750759 prefixEnd_6750759 385153794407273150896259 := by
  unfold tailWord_6750759
  simp only [CollatzResearch.WordTrace]
  refine ⟨246220408550160555692239331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164146939033440370461492887 246220408550160555692239331)
  ·
    refine ⟨369330612825240833538358997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246220408550160555692239331 369330612825240833538358997)
    ·
      refine ⟨8656186238091582036055289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 369330612825240833538358997 8656186238091582036055289)
      ·
        refine ⟨6492139678568686527041467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8656186238091582036055289 6492139678568686527041467)
        ·
          refine ⟨9738209517853029790562201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6492139678568686527041467 9738209517853029790562201)
          ·
            refine ⟨7303657138389772342921651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9738209517853029790562201 7303657138389772342921651)
            ·
              refine ⟨10955485707584658514382477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7303657138389772342921651 10955485707584658514382477)
              ·
                refine ⟨4108307140344246942893429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10955485707584658514382477 4108307140344246942893429)
                ·
                  refine ⟨385153794407273150896259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4108307140344246942893429 385153794407273150896259)
                  ·
                    rfl

theorem cell23_6750759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 3, 5].length) (baseStart_6750759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6750759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6750759 prefixEnd_6750759 := by exact prefixLift 6750759
  have htrace : WordTrace (prefixWord ++ tailWord_6750759) baseStart_6750759 baseEnd_6750759 := by
    simpa [prefixWord, tailWord_6750759, baseEnd_6750759] using wordTrace_append hprefix tailTrace_6750759
  have hstable : (prefixWord ++ tailWord_6750759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6750759).length < 2 ^ (prefixWord ++ tailWord_6750759).sum := by decide
  have hdescent : baseEnd_6750759 < baseStart_6750759 := by decide
  rcases family_descends (prefixWord ++ tailWord_6750759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6750772 : List Nat := [2, 5, 1, 3, 1, 1, 1, 2, 2, 5]
def baseStart_6750772 : Nat := 118140960795 + 6750772 * 2 ^ 59
def prefixEnd_6750772 : Nat := 4983230072969 + 3 ^ 40 * 6750772 * 2
def baseEnd_6750772 : Nat := 1155463608304655602401257

theorem tailTrace_6750772 : CollatzResearch.WordTrace tailWord_6750772 prefixEnd_6750772 1155463608304655602401257 := by
  unfold tailWord_6750772
  simp only [CollatzResearch.WordTrace]
  refine ⟨123110441349556729456231285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164147255132742305941641713 123110441349556729456231285)
  ·
    refine ⟨11541603876520943386521683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 123110441349556729456231285 11541603876520943386521683)
    ·
      refine ⟨17312405814781415079782525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11541603876520943386521683 17312405814781415079782525)
      ·
        refine ⟨6492152180543030654918447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17312405814781415079782525 6492152180543030654918447)
        ·
          refine ⟨9738228270814545982377671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6492152180543030654918447 9738228270814545982377671)
          ·
            refine ⟨14607342406221818973566507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9738228270814545982377671 14607342406221818973566507)
            ·
              refine ⟨21911013609332728460349761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14607342406221818973566507 21911013609332728460349761)
              ·
                refine ⟨16433260206999546345262321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21911013609332728460349761 16433260206999546345262321)
                ·
                  refine ⟨12324945155249659758946741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16433260206999546345262321 12324945155249659758946741)
                  ·
                    refine ⟨1155463608304655602401257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12324945155249659758946741 1155463608304655602401257)
                    ·
                      rfl

theorem cell23_6750772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 2, 2, 5].length) (baseStart_6750772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6750772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6750772 prefixEnd_6750772 := by exact prefixLift 6750772
  have htrace : WordTrace (prefixWord ++ tailWord_6750772) baseStart_6750772 baseEnd_6750772 := by
    simpa [prefixWord, tailWord_6750772, baseEnd_6750772] using wordTrace_append hprefix tailTrace_6750772
  have hstable : (prefixWord ++ tailWord_6750772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6750772).length < 2 ^ (prefixWord ++ tailWord_6750772).sum := by decide
  have hdescent : baseEnd_6750772 < baseStart_6750772 := by decide
  rcases family_descends (prefixWord ++ tailWord_6750772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6750778 : List Nat := [3, 1, 1, 1, 3, 3, 1, 1, 4, 2, 3]
def baseStart_6750778 : Nat := 118140960795 + 6750778 * 2 ^ 59
def prefixEnd_6750778 : Nat := 4983230072969 + 3 ^ 40 * 6750778 * 2
def baseEnd_6750778 : Nat := 3466393905797893783728743

theorem tailTrace_6750778 : CollatzResearch.WordTrace tailWord_6750778 prefixEnd_6750778 3466393905797893783728743 := by
  unfold tailWord_6750778
  simp only [CollatzResearch.WordTrace]
  refine ⟨61555275384272930484295247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164147401024727814624787325 61555275384272930484295247)
  ·
    refine ⟨92332913076409395726442871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61555275384272930484295247 92332913076409395726442871)
    ·
      refine ⟨138499369614614093589664307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92332913076409395726442871 138499369614614093589664307)
      ·
        refine ⟨207749054421921140384496461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138499369614614093589664307 207749054421921140384496461)
        ·
          refine ⟨77905895408220427644186173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 207749054421921140384496461 77905895408220427644186173)
          ·
            refine ⟨29214710778082660366569815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77905895408220427644186173 29214710778082660366569815)
            ·
              refine ⟨43822066167123990549854723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29214710778082660366569815 43822066167123990549854723)
              ·
                refine ⟨65733099250685985824782085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43822066167123990549854723 65733099250685985824782085)
                ·
                  refine ⟨12324956109503622342146641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65733099250685985824782085 12324956109503622342146641)
                  ·
                    refine ⟨9243717082127716756609981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12324956109503622342146641 9243717082127716756609981)
                    ·
                      refine ⟨3466393905797893783728743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9243717082127716756609981 3466393905797893783728743)
                      ·
                        rfl

theorem cell23_6750778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 1, 4, 2, 3].length) (baseStart_6750778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6750778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6750778 prefixEnd_6750778 := by exact prefixLift 6750778
  have htrace : WordTrace (prefixWord ++ tailWord_6750778) baseStart_6750778 baseEnd_6750778 := by
    simpa [prefixWord, tailWord_6750778, baseEnd_6750778] using wordTrace_append hprefix tailTrace_6750778
  have hstable : (prefixWord ++ tailWord_6750778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6750778).length < 2 ^ (prefixWord ++ tailWord_6750778).sum := by decide
  have hdescent : baseEnd_6750778 < baseStart_6750778 := by decide
  rcases family_descends (prefixWord ++ tailWord_6750778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6750785 : List Nat := [1, 2, 5, 1, 1, 2, 3, 1, 3, 4]
def baseStart_6750785 : Nat := 118140960795 + 6750785 * 2 ^ 59
def prefixEnd_6750785 : Nat := 4983230072969 + 3 ^ 40 * 6750785 * 2
def baseEnd_6750785 : Nat := 1155465833387491752113737

theorem tailTrace_6750785 : CollatzResearch.WordTrace tailWord_6750785 prefixEnd_6750785 1155465833387491752113737 := by
  unfold tailWord_6750785
  simp only [CollatzResearch.WordTrace]
  refine ⟨246221356848066362132685809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164147571232044241421790539 246221356848066362132685809)
  ·
    refine ⟨184666017636049771599514357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246221356848066362132685809 184666017636049771599514357)
    ·
      refine ⟨17312439153379666087454471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 184666017636049771599514357 17312439153379666087454471)
      ·
        refine ⟨25968658730069499131181707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17312439153379666087454471 25968658730069499131181707)
        ·
          refine ⟨38952988095104248696772561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25968658730069499131181707 38952988095104248696772561)
          ·
            refine ⟨29214741071328186522579421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38952988095104248696772561 29214741071328186522579421)
            ·
              refine ⟨10955527901748069945967283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29214741071328186522579421 10955527901748069945967283)
              ·
                refine ⟨16433291852622104918950925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10955527901748069945967283 16433291852622104918950925)
                ·
                  refine ⟨6162484444733289344606597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16433291852622104918950925 6162484444733289344606597)
                  ·
                    refine ⟨1155465833387491752113737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6162484444733289344606597 1155465833387491752113737)
                    ·
                      rfl

theorem cell23_6750785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 1, 3, 4].length) (baseStart_6750785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6750785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6750785 prefixEnd_6750785 := by exact prefixLift 6750785
  have htrace : WordTrace (prefixWord ++ tailWord_6750785) baseStart_6750785 baseEnd_6750785 := by
    simpa [prefixWord, tailWord_6750785, baseEnd_6750785] using wordTrace_append hprefix tailTrace_6750785
  have hstable : (prefixWord ++ tailWord_6750785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6750785).length < 2 ^ (prefixWord ++ tailWord_6750785).sum := by decide
  have hdescent : baseEnd_6750785 < baseStart_6750785 := by decide
  rcases family_descends (prefixWord ++ tailWord_6750785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6750812 : List Nat := [2, 2, 4, 1, 3, 1, 2, 1, 2, 2, 3]
def baseStart_6750812 : Nat := 118140960795 + 6750812 * 2 ^ 59
def prefixEnd_6750812 : Nat := 4983230072969 + 3 ^ 40 * 6750812 * 2
def baseEnd_6750812 : Nat := 3466411364140146650703587

theorem tailTrace_6750812 : CollatzResearch.WordTrace tailWord_6750812 prefixEnd_6750812 3466411364140146650703587 := by
  unfold tailWord_6750812
  simp only [CollatzResearch.WordTrace]
  refine ⟨123111170809484272871959345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164148227745979030495945793 123111170809484272871959345)
  ·
    refine ⟨92333378107113204653969509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123111170809484272871959345 92333378107113204653969509)
    ·
      refine ⟨17312508395083725872619283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92333378107113204653969509 17312508395083725872619283)
      ·
        refine ⟨25968762592625588808928925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17312508395083725872619283 25968762592625588808928925)
        ·
          refine ⟨9738285972234595803348347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25968762592625588808928925 9738285972234595803348347)
          ·
            refine ⟨14607428958351893705022521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9738285972234595803348347 14607428958351893705022521)
            ·
              refine ⟨10955571718763920278766891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14607428958351893705022521 10955571718763920278766891)
              ·
                refine ⟨16433357578145880418150337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10955571718763920278766891 16433357578145880418150337)
                ·
                  refine ⟨12325018183609410313612753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16433357578145880418150337 12325018183609410313612753)
                  ·
                    refine ⟨9243763637707057735209565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12325018183609410313612753 9243763637707057735209565)
                    ·
                      refine ⟨3466411364140146650703587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9243763637707057735209565 3466411364140146650703587)
                      ·
                        rfl

theorem cell23_6750812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 1, 2, 2, 3].length) (baseStart_6750812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6750812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6750812 prefixEnd_6750812 := by exact prefixLift 6750812
  have htrace : WordTrace (prefixWord ++ tailWord_6750812) baseStart_6750812 baseEnd_6750812 := by
    simpa [prefixWord, tailWord_6750812, baseEnd_6750812] using wordTrace_append hprefix tailTrace_6750812
  have hstable : (prefixWord ++ tailWord_6750812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6750812).length < 2 ^ (prefixWord ++ tailWord_6750812).sum := by decide
  have hdescent : baseEnd_6750812 < baseStart_6750812 := by decide
  rcases family_descends (prefixWord ++ tailWord_6750812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6750828 : List Nat := [2, 2, 1, 1, 3, 1, 2, 5, 1, 5]
def baseStart_6750828 : Nat := 118140960795 + 6750828 * 2 ^ 59
def prefixEnd_6750828 : Nat := 4983230072969 + 3 ^ 40 * 6750828 * 2
def baseEnd_6750828 : Nat := 1155473193276872862701171

theorem tailTrace_6750828 : CollatzResearch.WordTrace tailWord_6750828 prefixEnd_6750828 1155473193276872862701171 := by
  unfold tailWord_6750828
  simp only [CollatzResearch.WordTrace]
  refine ⟨123111462593455290238250569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164148616791273720317667425 123111462593455290238250569)
  ·
    refine ⟨92333596945091467678687927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123111462593455290238250569 92333596945091467678687927)
    ·
      refine ⟨138500395417637201518031891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92333596945091467678687927 138500395417637201518031891)
      ·
        refine ⟨207750593126455802277047837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138500395417637201518031891 207750593126455802277047837)
        ·
          refine ⟨77906472422420925853892939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 207750593126455802277047837 77906472422420925853892939)
          ·
            refine ⟨116859708633631388780839409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77906472422420925853892939 116859708633631388780839409)
            ·
              refine ⟨87644781475223541585629557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116859708633631388780839409 87644781475223541585629557)
              ·
                refine ⟨8216698263302207023652771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 87644781475223541585629557 8216698263302207023652771)
                ·
                  refine ⟨12325047394953310535479157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8216698263302207023652771 12325047394953310535479157)
                  ·
                    refine ⟨1155473193276872862701171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12325047394953310535479157 1155473193276872862701171)
                    ·
                      rfl

theorem cell23_6750828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 5].length) (baseStart_6750828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6750828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6750828 prefixEnd_6750828 := by exact prefixLift 6750828
  have htrace : WordTrace (prefixWord ++ tailWord_6750828) baseStart_6750828 baseEnd_6750828 := by
    simpa [prefixWord, tailWord_6750828, baseEnd_6750828] using wordTrace_append hprefix tailTrace_6750828
  have hstable : (prefixWord ++ tailWord_6750828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6750828).length < 2 ^ (prefixWord ++ tailWord_6750828).sum := by decide
  have hdescent : baseEnd_6750828 < baseStart_6750828 := by decide
  rcases family_descends (prefixWord ++ tailWord_6750828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6750848 : List Nat := [2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 4]
def baseStart_6750848 : Nat := 118140960795 + 6750848 * 2 ^ 59
def prefixEnd_6750848 : Nat := 4983230072969 + 3 ^ 40 * 6750848 * 2
def baseEnd_6750848 : Nat := 3466429849443708509853421

theorem tailTrace_6750848 : CollatzResearch.WordTrace tailWord_6750848 prefixEnd_6750848 3466429849443708509853421 := by
  unfold tailWord_6750848
  simp only [CollatzResearch.WordTrace]
  refine ⟨123111827323419061946114599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164149103097892082594819465 123111827323419061946114599)
  ·
    refine ⟨184667740985128592919171899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123111827323419061946114599 184667740985128592919171899)
    ·
      refine ⟨277001611477692889378757849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184667740985128592919171899 277001611477692889378757849)
      ·
        refine ⟨207751208608269667034068387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 277001611477692889378757849 207751208608269667034068387)
        ·
          refine ⟨311626812912404500551102581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207751208608269667034068387 311626812912404500551102581)
          ·
            refine ⟨29215013710537921926665867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 311626812912404500551102581 29215013710537921926665867)
            ·
              refine ⟨43822520565806882889998801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29215013710537921926665867 43822520565806882889998801)
              ·
                refine ⟨32866890424355162167499101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43822520565806882889998801 32866890424355162167499101)
                ·
                  refine ⟨12325083909133185812812163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32866890424355162167499101 12325083909133185812812163)
                  ·
                    refine ⟨18487625863699778719218245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12325083909133185812812163 18487625863699778719218245)
                    ·
                      refine ⟨3466429849443708509853421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18487625863699778719218245 3466429849443708509853421)
                      ·
                        rfl

theorem cell23_6750848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 4].length) (baseStart_6750848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6750848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6750848 prefixEnd_6750848 := by exact prefixLift 6750848
  have htrace : WordTrace (prefixWord ++ tailWord_6750848) baseStart_6750848 baseEnd_6750848 := by
    simpa [prefixWord, tailWord_6750848, baseEnd_6750848] using wordTrace_append hprefix tailTrace_6750848
  have hstable : (prefixWord ++ tailWord_6750848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6750848).length < 2 ^ (prefixWord ++ tailWord_6750848).sum := by decide
  have hdescent : baseEnd_6750848 < baseStart_6750848 := by decide
  rcases family_descends (prefixWord ++ tailWord_6750848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6750899 : List Nat := [1, 1, 1, 2, 3, 4, 2, 4, 1, 2, 2]
def baseStart_6750899 : Nat := 118140960795 + 6750899 * 2 ^ 59
def prefixEnd_6750899 : Nat := 4983230072969 + 3 ^ 40 * 6750899 * 2
def baseEnd_6750899 : Nat := 3466456036957087810315687

theorem tailTrace_6750899 : CollatzResearch.WordTrace tailWord_6750899 prefixEnd_6750899 3466456036957087810315687 := by
  unfold tailWord_6750899
  simp only [CollatzResearch.WordTrace]
  refine ⟨246225514769653359602335751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164150343179768906401557167 246225514769653359602335751)
  ·
    refine ⟨369338272154480039403503627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246225514769653359602335751 369338272154480039403503627)
    ·
      refine ⟨554007408231720059105255441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369338272154480039403503627 554007408231720059105255441)
      ·
        refine ⟨415505556173790044328941581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 554007408231720059105255441 415505556173790044328941581)
        ·
          refine ⟨155814583565171266623353093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 415505556173790044328941581 155814583565171266623353093)
          ·
            refine ⟨29215234418469612491878705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 155814583565171266623353093 29215234418469612491878705)
            ·
              refine ⟨21911425813852209368909029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29215234418469612491878705 21911425813852209368909029)
              ·
                refine ⟨4108392340097289256670443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21911425813852209368909029 4108392340097289256670443)
                ·
                  refine ⟨6162588510145933885005665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4108392340097289256670443 6162588510145933885005665)
                  ·
                    refine ⟨4621941382609450413754249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6162588510145933885005665 4621941382609450413754249)
                    ·
                      refine ⟨3466456036957087810315687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4621941382609450413754249 3466456036957087810315687)
                      ·
                        rfl

theorem cell23_6750899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 4, 1, 2, 2].length) (baseStart_6750899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6750899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6750899 prefixEnd_6750899 := by exact prefixLift 6750899
  have htrace : WordTrace (prefixWord ++ tailWord_6750899) baseStart_6750899 baseEnd_6750899 := by
    simpa [prefixWord, tailWord_6750899, baseEnd_6750899] using wordTrace_append hprefix tailTrace_6750899
  have hstable : (prefixWord ++ tailWord_6750899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6750899).length < 2 ^ (prefixWord ++ tailWord_6750899).sum := by decide
  have hdescent : baseEnd_6750899 < baseStart_6750899 := by decide
  rcases family_descends (prefixWord ++ tailWord_6750899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6750968 : List Nat := [2, 1, 2, 1, 1, 2, 4, 1, 1, 4, 4]
def baseStart_6750968 : Nat := 118140960795 + 6750968 * 2 ^ 59
def prefixEnd_6750968 : Nat := 4983230072969 + 3 ^ 40 * 6750968 * 2
def baseEnd_6750968 : Nat := 3466491467122248040352869

theorem tailTrace_6750968 : CollatzResearch.WordTrace tailWord_6750968 prefixEnd_6750968 3466491467122248040352869 := by
  unfold tailWord_6750968
  simp only [CollatzResearch.WordTrace]
  refine ⟨123114015703201692193298779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164152020937602256257731705 123114015703201692193298779)
  ·
    refine ⟨184671023554802538289948169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123114015703201692193298779 184671023554802538289948169)
    ·
      refine ⟨138503267666101903717461127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184671023554802538289948169 138503267666101903717461127)
      ·
        refine ⟨207754901499152855576191691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138503267666101903717461127 207754901499152855576191691)
        ·
          refine ⟨311632352248729283364287537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207754901499152855576191691 311632352248729283364287537)
          ·
            refine ⟨233724264186546962523215653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 311632352248729283364287537 233724264186546962523215653)
            ·
              refine ⟨43823299534977555473102935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 233724264186546962523215653 43823299534977555473102935)
              ·
                refine ⟨65734949302466333209654403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43823299534977555473102935 65734949302466333209654403)
                ·
                  refine ⟨98602423953699499814481605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65734949302466333209654403 98602423953699499814481605)
                  ·
                    refine ⟨18487954491318656215215301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 98602423953699499814481605 18487954491318656215215301)
                    ·
                      refine ⟨3466491467122248040352869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18487954491318656215215301 3466491467122248040352869)
                      ·
                        rfl

theorem cell23_6750968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 1, 1, 4, 4].length) (baseStart_6750968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6750968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6750968 prefixEnd_6750968 := by exact prefixLift 6750968
  have htrace : WordTrace (prefixWord ++ tailWord_6750968) baseStart_6750968 baseEnd_6750968 := by
    simpa [prefixWord, tailWord_6750968, baseEnd_6750968] using wordTrace_append hprefix tailTrace_6750968
  have hstable : (prefixWord ++ tailWord_6750968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6750968).length < 2 ^ (prefixWord ++ tailWord_6750968).sum := by decide
  have hdescent : baseEnd_6750968 < baseStart_6750968 := by decide
  rcases family_descends (prefixWord ++ tailWord_6750968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6750995 : List Nat := [1, 1, 1, 2, 1, 3, 4, 5, 5]
def baseStart_6750995 : Nat := 118140960795 + 6750995 * 2 ^ 59
def prefixEnd_6750995 : Nat := 4983230072969 + 3 ^ 40 * 6750995 * 2
def baseEnd_6750995 : Nat := 385167259011102159412805

theorem tailTrace_6750995 : CollatzResearch.WordTrace tailWord_6750995 prefixEnd_6750995 385167259011102159412805 := by
  unfold tailWord_6750995
  simp only [CollatzResearch.WordTrace]
  refine ⟨246229016177305567997830439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164152677451537045331886959 246229016177305567997830439)
  ·
    refine ⟨369343524265958351996745659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246229016177305567997830439 369343524265958351996745659)
    ·
      refine ⟨554015286398937527995118489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369343524265958351996745659 554015286398937527995118489)
      ·
        refine ⟨415511464799203145996338867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 554015286398937527995118489 415511464799203145996338867)
        ·
          refine ⟨623267197198804718994508301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 415511464799203145996338867 623267197198804718994508301)
          ·
            refine ⟨233725198949551769622940613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 623267197198804718994508301 233725198949551769622940613)
            ·
              refine ⟨43823474803040956804301365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 233725198949551769622940613 43823474803040956804301365)
              ·
                refine ⟨4108450762785089700403253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43823474803040956804301365 4108450762785089700403253)
                ·
                  refine ⟨385167259011102159412805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4108450762785089700403253 385167259011102159412805)
                  ·
                    rfl

theorem cell23_6750995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 5, 5].length) (baseStart_6750995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6750995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6750995 prefixEnd_6750995 := by exact prefixLift 6750995
  have htrace : WordTrace (prefixWord ++ tailWord_6750995) baseStart_6750995 baseEnd_6750995 := by
    simpa [prefixWord, tailWord_6750995, baseEnd_6750995] using wordTrace_append hprefix tailTrace_6750995
  have hstable : (prefixWord ++ tailWord_6750995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6750995).length < 2 ^ (prefixWord ++ tailWord_6750995).sum := by decide
  have hdescent : baseEnd_6750995 < baseStart_6750995 := by decide
  rcases family_descends (prefixWord ++ tailWord_6750995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6751022 : List Nat := [4, 1, 3, 2, 1, 1, 1, 1, 1, 5, 3]
def baseStart_6751022 : Nat := 118140960795 + 6751022 * 2 ^ 59
def prefixEnd_6751022 : Nat := 4983230072969 + 3 ^ 40 * 6751022 * 2
def baseEnd_6751022 : Nat := 3466519195077590829077621

theorem tailTrace_6751022 : CollatzResearch.WordTrace tailWord_6751022 prefixEnd_6751022 3466519195077590829077621 := by
  unfold tailWord_6751022
  simp only [CollatzResearch.WordTrace]
  refine ⟨30778750118525968951132915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164153333965471834406042213 30778750118525968951132915)
  ·
    refine ⟨46168125177788953426699373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30778750118525968951132915 46168125177788953426699373)
    ·
      refine ⟨17313046941670857535012265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46168125177788953426699373 17313046941670857535012265)
      ·
        refine ⟨12984785206253143151259199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17313046941670857535012265 12984785206253143151259199)
        ·
          refine ⟨19477177809379714726888799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12984785206253143151259199 19477177809379714726888799)
          ·
            refine ⟨29215766714069572090333199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19477177809379714726888799 29215766714069572090333199)
            ·
              refine ⟨43823650071104358135499799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29215766714069572090333199 43823650071104358135499799)
              ·
                refine ⟨65735475106656537203249699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43823650071104358135499799 65735475106656537203249699)
                ·
                  refine ⟨98603212659984805804874549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65735475106656537203249699 98603212659984805804874549)
                  ·
                    refine ⟨9244051186873575544206989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 98603212659984805804874549 9244051186873575544206989)
                    ·
                      refine ⟨3466519195077590829077621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9244051186873575544206989 3466519195077590829077621)
                      ·
                        rfl

theorem cell23_6751022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_6751022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6751022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6751022 prefixEnd_6751022 := by exact prefixLift 6751022
  have htrace : WordTrace (prefixWord ++ tailWord_6751022) baseStart_6751022 baseEnd_6751022 := by
    simpa [prefixWord, tailWord_6751022, baseEnd_6751022] using wordTrace_append hprefix tailTrace_6751022
  have hstable : (prefixWord ++ tailWord_6751022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6751022).length < 2 ^ (prefixWord ++ tailWord_6751022).sum := by decide
  have hdescent : baseEnd_6751022 < baseStart_6751022 := by decide
  rcases family_descends (prefixWord ++ tailWord_6751022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6751045 : List Nat := [1, 3, 1, 1, 1, 2, 2, 5, 2, 1, 4]
def baseStart_6751045 : Nat := 118140960795 + 6751045 * 2 ^ 59
def prefixEnd_6751045 : Nat := 4983230072969 + 3 ^ 40 * 6751045 * 2
def baseEnd_6751045 : Nat := 3466531005132644239090015

theorem tailTrace_6751045 : CollatzResearch.WordTrace tailWord_6751045 prefixEnd_6751045 3466531005132644239090015 := by
  unfold tailWord_6751045
  simp only [CollatzResearch.WordTrace]
  refine ⟨246230839827124426537150589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164153893218082951024767059 246230839827124426537150589)
  ·
    refine ⟨92336564935171659951431471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 246230839827124426537150589 92336564935171659951431471)
    ·
      refine ⟨138504847402757489927147207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92336564935171659951431471 138504847402757489927147207)
      ·
        refine ⟨207757271104136234890720811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138504847402757489927147207 207757271104136234890720811)
        ·
          refine ⟨311635906656204352336081217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207757271104136234890720811 311635906656204352336081217)
          ·
            refine ⟨233726929992153264252060913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 311635906656204352336081217 233726929992153264252060913)
            ·
              refine ⟨175295197494114948189045685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 233726929992153264252060913 175295197494114948189045685)
              ·
                refine ⟨16433924765073276392723033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 175295197494114948189045685 16433924765073276392723033)
                ·
                  refine ⟨12325443573804957294542275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16433924765073276392723033 12325443573804957294542275)
                  ·
                    refine ⟨18488165360707435941813413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12325443573804957294542275 18488165360707435941813413)
                    ·
                      refine ⟨3466531005132644239090015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18488165360707435941813413 3466531005132644239090015)
                      ·
                        rfl

theorem cell23_6751045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 5, 2, 1, 4].length) (baseStart_6751045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6751045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6751045 prefixEnd_6751045 := by exact prefixLift 6751045
  have htrace : WordTrace (prefixWord ++ tailWord_6751045) baseStart_6751045 baseEnd_6751045 := by
    simpa [prefixWord, tailWord_6751045, baseEnd_6751045] using wordTrace_append hprefix tailTrace_6751045
  have hstable : (prefixWord ++ tailWord_6751045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6751045).length < 2 ^ (prefixWord ++ tailWord_6751045).sum := by decide
  have hdescent : baseEnd_6751045 < baseStart_6751045 := by decide
  rcases family_descends (prefixWord ++ tailWord_6751045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6751072 : List Nat := [2, 1, 1, 3, 3, 1, 4, 1, 3, 4]
def baseStart_6751072 : Nat := 118140960795 + 6751072 * 2 ^ 59
def prefixEnd_6751072 : Nat := 4983230072969 + 3 ^ 40 * 6751072 * 2
def baseEnd_6751072 : Nat := 1155514956370105211150797

theorem tailTrace_6751072 : CollatzResearch.WordTrace tailWord_6751072 prefixEnd_6751072 1155514956370105211150797 := by
  unfold tailWord_6751072
  simp only [CollatzResearch.WordTrace]
  refine ⟨123115912299013305074191735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164154549732017740098922313 123115912299013305074191735)
  ·
    refine ⟨184673868448519957611287603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123115912299013305074191735 184673868448519957611287603)
    ·
      refine ⟨277010802672779936416931405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184673868448519957611287603 277010802672779936416931405)
      ·
        refine ⟨103879051002292476156349277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 277010802672779936416931405 103879051002292476156349277)
        ·
          refine ⟨38954644125859678558630979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103879051002292476156349277 38954644125859678558630979)
          ·
            refine ⟨58431966188789517837946469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38954644125859678558630979 58431966188789517837946469)
            ·
              refine ⟨10955993660398034594614963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58431966188789517837946469 10955993660398034594614963)
              ·
                refine ⟨16433990490597051891922445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10955993660398034594614963 16433990490597051891922445)
                ·
                  refine ⟨6162746433973894459470917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16433990490597051891922445 6162746433973894459470917)
                  ·
                    refine ⟨1155514956370105211150797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6162746433973894459470917 1155514956370105211150797)
                    ·
                      rfl

theorem cell23_6751072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 1, 3, 4].length) (baseStart_6751072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6751072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6751072 prefixEnd_6751072 := by exact prefixLift 6751072
  have htrace : WordTrace (prefixWord ++ tailWord_6751072) baseStart_6751072 baseEnd_6751072 := by
    simpa [prefixWord, tailWord_6751072, baseEnd_6751072] using wordTrace_append hprefix tailTrace_6751072
  have hstable : (prefixWord ++ tailWord_6751072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6751072).length < 2 ^ (prefixWord ++ tailWord_6751072).sum := by decide
  have hdescent : baseEnd_6751072 < baseStart_6751072 := by decide
  rcases family_descends (prefixWord ++ tailWord_6751072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6751145 : List Nat := [1, 2, 1, 1, 1, 1, 6, 3, 1, 6]
def baseStart_6751145 : Nat := 118140960795 + 6751145 * 2 ^ 59
def prefixEnd_6751145 : Nat := 4983230072969 + 3 ^ 40 * 6751145 * 2
def baseEnd_6751145 : Nat := 1155527451066031282613185

theorem tailTrace_6751145 : CollatzResearch.WordTrace tailWord_6751145 prefixEnd_6751145 1155527451066031282613185 := by
  unfold tailWord_6751145
  simp only [CollatzResearch.WordTrace]
  refine ⟨246234487126762143615790889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164156324751174762410527259 246234487126762143615790889)
  ·
    refine ⟨184675865345071607711843167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246234487126762143615790889 184675865345071607711843167)
    ·
      refine ⟨277013798017607411567764751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184675865345071607711843167 277013798017607411567764751)
      ·
        refine ⟨415520697026411117351647127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277013798017607411567764751 415520697026411117351647127)
        ·
          refine ⟨623281045539616676027470691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 415520697026411117351647127 623281045539616676027470691)
          ·
            refine ⟨934921568309425014041206037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 623281045539616676027470691 934921568309425014041206037)
            ·
              refine ⟨43824448514504297533181533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 934921568309425014041206037 43824448514504297533181533)
              ·
                refine ⟨16434168192939111574943075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43824448514504297533181533 16434168192939111574943075)
                ·
                  refine ⟨24651252289408667362414613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16434168192939111574943075 24651252289408667362414613)
                  ·
                    refine ⟨1155527451066031282613185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24651252289408667362414613 1155527451066031282613185)
                    ·
                      rfl

theorem cell23_6751145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 3, 1, 6].length) (baseStart_6751145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6751145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6751145 prefixEnd_6751145 := by exact prefixLift 6751145
  have htrace : WordTrace (prefixWord ++ tailWord_6751145) baseStart_6751145 baseEnd_6751145 := by
    simpa [prefixWord, tailWord_6751145, baseEnd_6751145] using wordTrace_append hprefix tailTrace_6751145
  have hstable : (prefixWord ++ tailWord_6751145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6751145).length < 2 ^ (prefixWord ++ tailWord_6751145).sum := by decide
  have hdescent : baseEnd_6751145 < baseStart_6751145 := by decide
  rcases family_descends (prefixWord ++ tailWord_6751145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6751179 : List Nat := [1, 1, 1, 1, 3, 6, 2, 2, 2, 4]
def baseStart_6751179 : Nat := 118140960795 + 6751179 * 2 ^ 59
def prefixEnd_6751179 : Nat := 4983230072969 + 3 ^ 40 * 6751179 * 2
def baseEnd_6751179 : Nat := 1155533270513448904938133

theorem tailTrace_6751179 : CollatzResearch.WordTrace tailWord_6751179 prefixEnd_6751179 1155533270513448904938133 := by
  unfold tailWord_6751179
  simp only [CollatzResearch.WordTrace]
  refine ⟨246235727208638967422528591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164157151472425978281685727 246235727208638967422528591)
  ·
    refine ⟨369353590812958451133792887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246235727208638967422528591 369353590812958451133792887)
    ·
      refine ⟨554030386219437676700689331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369353590812958451133792887 554030386219437676700689331)
      ·
        refine ⟨831045579329156515051033997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 554030386219437676700689331 831045579329156515051033997)
        ·
          refine ⟨311642092248433693144137749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 831045579329156515051033997 311642092248433693144137749)
          ·
            refine ⟨14608223074145329366131457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 311642092248433693144137749 14608223074145329366131457)
            ·
              refine ⟨10956167305608997024598593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14608223074145329366131457 10956167305608997024598593)
              ·
                refine ⟨8217125479206747768448945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10956167305608997024598593 8217125479206747768448945)
                ·
                  refine ⟨6162844109405060826336709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8217125479206747768448945 6162844109405060826336709)
                  ·
                    refine ⟨1155533270513448904938133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6162844109405060826336709 1155533270513448904938133)
                    ·
                      rfl

theorem cell23_6751179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 2, 2, 4].length) (baseStart_6751179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6751179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6751179 prefixEnd_6751179 := by exact prefixLift 6751179
  have htrace : WordTrace (prefixWord ++ tailWord_6751179) baseStart_6751179 baseEnd_6751179 := by
    simpa [prefixWord, tailWord_6751179, baseEnd_6751179] using wordTrace_append hprefix tailTrace_6751179
  have hstable : (prefixWord ++ tailWord_6751179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6751179).length < 2 ^ (prefixWord ++ tailWord_6751179).sum := by decide
  have hdescent : baseEnd_6751179 < baseStart_6751179 := by decide
  rcases family_descends (prefixWord ++ tailWord_6751179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6751192 : List Nat := [2, 1, 2, 2, 2, 5, 1, 8]
def baseStart_6751192 : Nat := 118140960795 + 6751192 * 2 ^ 59
def prefixEnd_6751192 : Nat := 4983230072969 + 3 ^ 40 * 6751192 * 2
def baseEnd_6751192 : Nat := 128392832844031672738957

theorem tailTrace_6751192 : CollatzResearch.WordTrace tailWord_6751192 prefixEnd_6751192 128392832844031672738957 := by
  unfold tailWord_6751192
  simp only [CollatzResearch.WordTrace]
  refine ⟨123118100678795935321375915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164157467571727913761834553 123118100678795935321375915)
  ·
    refine ⟨184677151018193902982063873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123118100678795935321375915 184677151018193902982063873)
    ·
      refine ⟨138507863263645427236547905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184677151018193902982063873 138507863263645427236547905)
      ·
        refine ⟨103880897447734070427410929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138507863263645427236547905 103880897447734070427410929)
        ·
          refine ⟨77910673085800552820558197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103880897447734070427410929 77910673085800552820558197)
          ·
            refine ⟨7304125601793801826927331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 77910673085800552820558197 7304125601793801826927331)
            ·
              refine ⟨10956188402690702740390997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7304125601793801826927331 10956188402690702740390997)
              ·
                refine ⟨128392832844031672738957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10956188402690702740390997 128392832844031672738957)
                ·
                  rfl

theorem cell23_6751192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 8].length) (baseStart_6751192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6751192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6751192 prefixEnd_6751192 := by exact prefixLift 6751192
  have htrace : WordTrace (prefixWord ++ tailWord_6751192) baseStart_6751192 baseEnd_6751192 := by
    simpa [prefixWord, tailWord_6751192, baseEnd_6751192] using wordTrace_append hprefix tailTrace_6751192
  have hstable : (prefixWord ++ tailWord_6751192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6751192).length < 2 ^ (prefixWord ++ tailWord_6751192).sum := by decide
  have hdescent : baseEnd_6751192 < baseStart_6751192 := by decide
  rcases family_descends (prefixWord ++ tailWord_6751192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6751199 : List Nat := [1, 1, 2, 3, 5, 1, 2, 1, 1, 2, 4]
def baseStart_6751199 : Nat := 118140960795 + 6751199 * 2 ^ 59
def prefixEnd_6751199 : Nat := 4983230072969 + 3 ^ 40 * 6751199 * 2
def baseEnd_6751199 : Nat := 3466610081153436636564307

theorem tailTrace_6751199 : CollatzResearch.WordTrace tailWord_6751199 prefixEnd_6751199 3466610081153436636564307 := by
  unfold tailWord_6751199
  simp only [CollatzResearch.WordTrace]
  refine ⟨246236456668566510838256651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164157637779044340558837767 246236456668566510838256651)
  ·
    refine ⟨369354685002849766257384977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246236456668566510838256651 369354685002849766257384977)
    ·
      refine ⟨277016013752137324693038733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 369354685002849766257384977 277016013752137324693038733)
      ·
        refine ⟨103881005157051496759889525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 277016013752137324693038733 103881005157051496759889525)
        ·
          refine ⟨9738844233473577821239643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 103881005157051496759889525 9738844233473577821239643)
          ·
            refine ⟨14608266350210366731859465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9738844233473577821239643 14608266350210366731859465)
            ·
              refine ⟨10956199762657775048894599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14608266350210366731859465 10956199762657775048894599)
              ·
                refine ⟨16434299643986662573341899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10956199762657775048894599 16434299643986662573341899)
                ·
                  refine ⟨24651449465979993860012849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16434299643986662573341899 24651449465979993860012849)
                  ·
                    refine ⟨18488587099484995395009637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24651449465979993860012849 18488587099484995395009637)
                    ·
                      refine ⟨3466610081153436636564307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18488587099484995395009637 3466610081153436636564307)
                      ·
                        rfl

theorem cell23_6751199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 1, 1, 2, 4].length) (baseStart_6751199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6751199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6751199 prefixEnd_6751199 := by exact prefixLift 6751199
  have htrace : WordTrace (prefixWord ++ tailWord_6751199) baseStart_6751199 baseEnd_6751199 := by
    simpa [prefixWord, tailWord_6751199, baseEnd_6751199] using wordTrace_append hprefix tailTrace_6751199
  have hstable : (prefixWord ++ tailWord_6751199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6751199).length < 2 ^ (prefixWord ++ tailWord_6751199).sum := by decide
  have hdescent : baseEnd_6751199 < baseStart_6751199 := by decide
  rcases family_descends (prefixWord ++ tailWord_6751199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6751230 : List Nat := [4, 2, 2, 2, 3, 1, 1, 2, 2, 4]
def baseStart_6751230 : Nat := 118140960795 + 6751230 * 2 ^ 59
def prefixEnd_6751230 : Nat := 4983230072969 + 3 ^ 40 * 6751230 * 2
def baseEnd_6751230 : Nat := 1155541999684575338425555

theorem tailTrace_6751230 : CollatzResearch.WordTrace tailWord_6751230 prefixEnd_6751230 1155541999684575338425555 := by
  unfold tailWord_6751230
  simp only [CollatzResearch.WordTrace]
  refine ⟨30779698416431775391579393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164158391554302802088423429 30779698416431775391579393)
  ·
    refine ⟨23084773812323831543684545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30779698416431775391579393 23084773812323831543684545)
    ·
      refine ⟨17313580359242873657763409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23084773812323831543684545 17313580359242873657763409)
      ·
        refine ⟨12985185269432155243322557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17313580359242873657763409 12985185269432155243322557)
        ·
          refine ⟨4869444476037058216245959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12985185269432155243322557 4869444476037058216245959)
          ·
            refine ⟨7304166714055587324368939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4869444476037058216245959 7304166714055587324368939)
            ·
              refine ⟨10956250071083380986553409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7304166714055587324368939 10956250071083380986553409)
              ·
                refine ⟨8217187553312535739915057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10956250071083380986553409 8217187553312535739915057)
                ·
                  refine ⟨6162890664984401804936293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8217187553312535739915057 6162890664984401804936293)
                  ·
                    refine ⟨1155541999684575338425555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6162890664984401804936293 1155541999684575338425555)
                    ·
                      rfl

theorem cell23_6751230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 2, 2, 4].length) (baseStart_6751230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6751230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6751230 prefixEnd_6751230 := by exact prefixLift 6751230
  have htrace : WordTrace (prefixWord ++ tailWord_6751230) baseStart_6751230 baseEnd_6751230 := by
    simpa [prefixWord, tailWord_6751230, baseEnd_6751230] using wordTrace_append hprefix tailTrace_6751230
  have hstable : (prefixWord ++ tailWord_6751230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6751230).length < 2 ^ (prefixWord ++ tailWord_6751230).sum := by decide
  have hdescent : baseEnd_6751230 < baseStart_6751230 := by decide
  rcases family_descends (prefixWord ++ tailWord_6751230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6751250 : List Nat := [3, 2, 5, 1, 1, 2, 1, 1, 1, 2, 4]
def baseStart_6751250 : Nat := 118140960795 + 6751250 * 2 ^ 59
def prefixEnd_6751250 : Nat := 4983230072969 + 3 ^ 40 * 6751250 * 2
def baseEnd_6751250 : Nat := 3466636268666815937026573

theorem tailTrace_6751250 : CollatzResearch.WordTrace tailWord_6751250 prefixEnd_6751250 3466636268666815937026573 := by
  unfold tailWord_6751250
  simp only [CollatzResearch.WordTrace]
  refine ⟨61559579197845436637090801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164158877860921164365575469 61559579197845436637090801)
  ·
    refine ⟨46169684398384077477818101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61559579197845436637090801 46169684398384077477818101)
    ·
      refine ⟨4328407912348507263545447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46169684398384077477818101 4328407912348507263545447)
      ·
        refine ⟨6492611868522760895318171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4328407912348507263545447 6492611868522760895318171)
        ·
          refine ⟨9738917802784141342977257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6492611868522760895318171 9738917802784141342977257)
          ·
            refine ⟨7304188352088106007232943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9738917802784141342977257 7304188352088106007232943)
            ·
              refine ⟨10956282528132159010849415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7304188352088106007232943 10956282528132159010849415)
              ·
                refine ⟨16434423792198238516274123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10956282528132159010849415 16434423792198238516274123)
                ·
                  refine ⟨24651635688297357774411185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16434423792198238516274123 24651635688297357774411185)
                  ·
                    refine ⟨18488726766223018330808389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24651635688297357774411185 18488726766223018330808389)
                    ·
                      refine ⟨3466636268666815937026573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18488726766223018330808389 3466636268666815937026573)
                      ·
                        rfl

theorem cell23_6751250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_6751250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6751250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6751250 prefixEnd_6751250 := by exact prefixLift 6751250
  have htrace : WordTrace (prefixWord ++ tailWord_6751250) baseStart_6751250 baseEnd_6751250 := by
    simpa [prefixWord, tailWord_6751250, baseEnd_6751250] using wordTrace_append hprefix tailTrace_6751250
  have hstable : (prefixWord ++ tailWord_6751250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6751250).length < 2 ^ (prefixWord ++ tailWord_6751250).sum := by decide
  have hdescent : baseEnd_6751250 < baseStart_6751250 := by decide
  rcases family_descends (prefixWord ++ tailWord_6751250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6751253 : List Nat := [1, 3, 2, 1, 4, 2, 3, 1, 2, 1, 3]
def baseStart_6751253 : Nat := 118140960795 + 6751253 * 2 ^ 59
def prefixEnd_6751253 : Nat := 4983230072969 + 3 ^ 40 * 6751253 * 2
def baseEnd_6751253 : Nat := 3466637809108779425289059

theorem tailTrace_6751253 : CollatzResearch.WordTrace tailWord_6751253 prefixEnd_6751253 3466637809108779425289059 := by
  unfold tailWord_6751253
  simp only [CollatzResearch.WordTrace]
  refine ⟨246238426210370878060722413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164158950806913918707148275 246238426210370878060722413)
  ·
    refine ⟨92339409828889079272770905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 246238426210370878060722413 92339409828889079272770905)
    ·
      refine ⟨69254557371666809454578179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92339409828889079272770905 69254557371666809454578179)
      ·
        refine ⟨103881836057500214181867269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69254557371666809454578179 103881836057500214181867269)
        ·
          refine ⟨19477844260781290159100113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103881836057500214181867269 19477844260781290159100113)
          ·
            refine ⟨14608383195585967619325085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19477844260781290159100113 14608383195585967619325085)
            ·
              refine ⟨5478143698344737857246907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14608383195585967619325085 5478143698344737857246907)
              ·
                refine ⟨8217215547517106785870361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5478143698344737857246907 8217215547517106785870361)
                ·
                  refine ⟨6162911660637830089402771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8217215547517106785870361 6162911660637830089402771)
                  ·
                    refine ⟨9244367490956745134104157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6162911660637830089402771 9244367490956745134104157)
                    ·
                      refine ⟨3466637809108779425289059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9244367490956745134104157 3466637809108779425289059)
                      ·
                        rfl

theorem cell23_6751253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 3, 1, 2, 1, 3].length) (baseStart_6751253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6751253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6751253 prefixEnd_6751253 := by exact prefixLift 6751253
  have htrace : WordTrace (prefixWord ++ tailWord_6751253) baseStart_6751253 baseEnd_6751253 := by
    simpa [prefixWord, tailWord_6751253, baseEnd_6751253] using wordTrace_append hprefix tailTrace_6751253
  have hstable : (prefixWord ++ tailWord_6751253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6751253).length < 2 ^ (prefixWord ++ tailWord_6751253).sum := by decide
  have hdescent : baseEnd_6751253 < baseStart_6751253 := by decide
  rcases family_descends (prefixWord ++ tailWord_6751253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6751386 : List Nat := [3, 1, 1, 5, 1, 2, 1, 1, 1, 4, 3]
def baseStart_6751386 : Nat := 118140960795 + 6751386 * 2 ^ 59
def prefixEnd_6751386 : Nat := 4983230072969 + 3 ^ 40 * 6751386 * 2
def baseEnd_6751386 : Nat := 3466706102035827404925947

theorem tailTrace_6751386 : CollatzResearch.WordTrace tailWord_6751386 prefixEnd_6751386 3466706102035827404925947 := by
  unfold tailWord_6751386
  simp only [CollatzResearch.WordTrace]
  refine ⟨61560819279722260443828503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164162184745926027850209341 61560819279722260443828503)
  ·
    refine ⟨92341228919583390665742755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61560819279722260443828503 92341228919583390665742755)
    ·
      refine ⟨138511843379375085998614133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92341228919583390665742755 138511843379375085998614133)
      ·
        refine ⟨12985485316816414312370075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 138511843379375085998614133 12985485316816414312370075)
        ·
          refine ⟨19478227975224621468555113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12985485316816414312370075 19478227975224621468555113)
          ·
            refine ⟨14608670981418466101416335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19478227975224621468555113 14608670981418466101416335)
            ·
              refine ⟨21913006472127699152124503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14608670981418466101416335 21913006472127699152124503)
              ·
                refine ⟨32869509708191548728186755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21913006472127699152124503 32869509708191548728186755)
                ·
                  refine ⟨49304264562287323092280133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32869509708191548728186755 49304264562287323092280133)
                  ·
                    refine ⟨9244549605428873079802525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49304264562287323092280133 9244549605428873079802525)
                    ·
                      refine ⟨3466706102035827404925947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9244549605428873079802525 3466706102035827404925947)
                      ·
                        rfl

theorem cell23_6751386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_6751386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6751386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6751386 prefixEnd_6751386 := by exact prefixLift 6751386
  have htrace : WordTrace (prefixWord ++ tailWord_6751386) baseStart_6751386 baseEnd_6751386 := by
    simpa [prefixWord, tailWord_6751386, baseEnd_6751386] using wordTrace_append hprefix tailTrace_6751386
  have hstable : (prefixWord ++ tailWord_6751386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6751386).length < 2 ^ (prefixWord ++ tailWord_6751386).sum := by decide
  have hdescent : baseEnd_6751386 < baseStart_6751386 := by decide
  rcases family_descends (prefixWord ++ tailWord_6751386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6751393 : List Nat := [1, 2, 3, 3, 1, 1, 4, 3, 1, 4]
def baseStart_6751393 : Nat := 118140960795 + 6751393 * 2 ^ 59
def prefixEnd_6751393 : Nat := 4983230072969 + 3 ^ 40 * 6751393 * 2
def baseEnd_6751393 : Nat := 1155569898800136292512805

theorem tailTrace_6751393 : CollatzResearch.WordTrace tailWord_6751393 prefixEnd_6751393 1155569898800136292512805 := by
  unfold tailWord_6751393
  simp only [CollatzResearch.WordTrace]
  refine ⟨246243532429863681970818833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164162354953242454647212555 246243532429863681970818833)
  ·
    refine ⟨184682649322397761478114125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246243532429863681970818833 184682649322397761478114125)
    ·
      refine ⟨69255993495899160554292797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184682649322397761478114125 69255993495899160554292797)
      ·
        refine ⟨25970997560962185207859799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69255993495899160554292797 25970997560962185207859799)
        ·
          refine ⟨38956496341443277811789699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25970997560962185207859799 38956496341443277811789699)
          ·
            refine ⟨58434744512164916717684549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38956496341443277811789699 58434744512164916717684549)
            ·
              refine ⟨10956514596030921884565853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58434744512164916717684549 10956514596030921884565853)
              ·
                refine ⟨4108692973511595706712195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10956514596030921884565853 4108692973511595706712195)
                ·
                  refine ⟨6163039460267393560068293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4108692973511595706712195 6163039460267393560068293)
                  ·
                    refine ⟨1155569898800136292512805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6163039460267393560068293 1155569898800136292512805)
                    ·
                      rfl

theorem cell23_6751393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 3, 1, 4].length) (baseStart_6751393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6751393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6751393 prefixEnd_6751393 := by exact prefixLift 6751393
  have htrace : WordTrace (prefixWord ++ tailWord_6751393) baseStart_6751393 baseEnd_6751393 := by
    simpa [prefixWord, tailWord_6751393, baseEnd_6751393] using wordTrace_append hprefix tailTrace_6751393
  have hstable : (prefixWord ++ tailWord_6751393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6751393).length < 2 ^ (prefixWord ++ tailWord_6751393).sum := by decide
  have hdescent : baseEnd_6751393 < baseStart_6751393 := by decide
  rcases family_descends (prefixWord ++ tailWord_6751393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6751409 : List Nat := [1, 2, 2, 5, 1, 1, 1, 1, 1, 2, 6]
def baseStart_6751409 : Nat := 118140960795 + 6751409 * 2 ^ 59
def prefixEnd_6751409 : Nat := 4983230072969 + 3 ^ 40 * 6751409 * 2
def baseEnd_6751409 : Nat := 3466717912090880814938341

theorem tailTrace_6751409 : CollatzResearch.WordTrace tailWord_6751409 prefixEnd_6751409 3466717912090880814938341 := by
  unfold tailWord_6751409
  simp only [CollatzResearch.WordTrace]
  refine ⟨246244115997805716703401281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164162743998537144468934187 246244115997805716703401281)
  ·
    refine ⟨184683086998354287527550961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246244115997805716703401281 184683086998354287527550961)
    ·
      refine ⟨138512315248765715645663221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184683086998354287527550961 138512315248765715645663221)
      ·
        refine ⟨12985529554571785841780927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 138512315248765715645663221 12985529554571785841780927)
        ·
          refine ⟨19478294331857678762671391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12985529554571785841780927 19478294331857678762671391)
          ·
            refine ⟨29217441497786518144007087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19478294331857678762671391 29217441497786518144007087)
            ·
              refine ⟨43826162246679777216010631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29217441497786518144007087 43826162246679777216010631)
              ·
                refine ⟨65739243370019665824015947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43826162246679777216010631 65739243370019665824015947)
                ·
                  refine ⟨98608865055029498736023921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65739243370019665824015947 98608865055029498736023921)
                  ·
                    refine ⟨73956648791272124052017941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 98608865055029498736023921 73956648791272124052017941)
                    ·
                      refine ⟨3466717912090880814938341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73956648791272124052017941 3466717912090880814938341)
                      ·
                        rfl

theorem cell23_6751409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_6751409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6751409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6751409 prefixEnd_6751409 := by exact prefixLift 6751409
  have htrace : WordTrace (prefixWord ++ tailWord_6751409) baseStart_6751409 baseEnd_6751409 := by
    simpa [prefixWord, tailWord_6751409, baseEnd_6751409] using wordTrace_append hprefix tailTrace_6751409
  have hstable : (prefixWord ++ tailWord_6751409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6751409).length < 2 ^ (prefixWord ++ tailWord_6751409).sum := by decide
  have hdescent : baseEnd_6751409 < baseStart_6751409 := by decide
  rcases family_descends (prefixWord ++ tailWord_6751409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6751444 : List Nat := [2, 4, 1, 4, 2, 1, 1, 3, 1, 4]
def baseStart_6751444 : Nat := 118140960795 + 6751444 * 2 ^ 59
def prefixEnd_6751444 : Nat := 4983230072969 + 3 ^ 40 * 6751444 * 2
def baseEnd_6751444 : Nat := 1155578627971262726000227

theorem tailTrace_6751444 : CollatzResearch.WordTrace tailWord_6751444 prefixEnd_6751444 1155578627971262726000227 := by
  unfold tailWord_6751444
  simp only [CollatzResearch.WordTrace]
  refine ⟨123122696276339458840462693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164163595035119278453950257 123122696276339458840462693)
  ·
    refine ⟨23085505551813648532586755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123122696276339458840462693 23085505551813648532586755)
    ·
      refine ⟨34628258327720472798880133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23085505551813648532586755 34628258327720472798880133)
      ·
        refine ⟨6492798436447588649790025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34628258327720472798880133 6492798436447588649790025)
        ·
          refine ⟨4869598827335691487342519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6492798436447588649790025 4869598827335691487342519)
          ·
            refine ⟨7304398241003537231013779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4869598827335691487342519 7304398241003537231013779)
            ·
              refine ⟨10956597361505305846520669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7304398241003537231013779 10956597361505305846520669)
              ·
                refine ⟨4108724010564489692445251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10956597361505305846520669 4108724010564489692445251)
                ·
                  refine ⟨6163086015846734538667877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4108724010564489692445251 6163086015846734538667877)
                  ·
                    refine ⟨1155578627971262726000227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6163086015846734538667877 1155578627971262726000227)
                    ·
                      rfl

theorem cell23_6751444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 3, 1, 4].length) (baseStart_6751444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6751444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6751444 prefixEnd_6751444 := by exact prefixLift 6751444
  have htrace : WordTrace (prefixWord ++ tailWord_6751444) baseStart_6751444 baseEnd_6751444 := by
    simpa [prefixWord, tailWord_6751444, baseEnd_6751444] using wordTrace_append hprefix tailTrace_6751444
  have hstable : (prefixWord ++ tailWord_6751444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6751444).length < 2 ^ (prefixWord ++ tailWord_6751444).sum := by decide
  have hdescent : baseEnd_6751444 < baseStart_6751444 := by decide
  rcases family_descends (prefixWord ++ tailWord_6751444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6751456 : List Nat := [2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 4]
def baseStart_6751456 : Nat := 118140960795 + 6751456 * 2 ^ 59
def prefixEnd_6751456 : Nat := 4983230072969 + 3 ^ 40 * 6751456 * 2
def baseEnd_6751456 : Nat := 3466742045681642131050625

theorem tailTrace_6751456 : CollatzResearch.WordTrace tailWord_6751456 prefixEnd_6751456 3466742045681642131050625 := by
  unfold tailWord_6751456
  simp only [CollatzResearch.WordTrace]
  refine ⟨123122915114317721865181111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164163886819090295820241481 123122915114317721865181111)
  ·
    refine ⟨184684372671476582797771667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123122915114317721865181111 184684372671476582797771667)
    ·
      refine ⟨277026559007214874196657501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184684372671476582797771667 277026559007214874196657501)
      ·
        refine ⟨103884959627705577823746563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 277026559007214874196657501 103884959627705577823746563)
        ·
          refine ⟨155827439441558366735619845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103884959627705577823746563 155827439441558366735619845)
          ·
            refine ⟨29217644895292193762928721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 155827439441558366735619845 29217644895292193762928721)
            ·
              refine ⟨21913233671469145322196541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29217644895292193762928721 21913233671469145322196541)
              ·
                refine ⟨8217462626800929495823703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21913233671469145322196541 8217462626800929495823703)
                ·
                  refine ⟨12326193940201394243735555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8217462626800929495823703 12326193940201394243735555)
                  ·
                    refine ⟨18489290910302091365603333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12326193940201394243735555 18489290910302091365603333)
                    ·
                      refine ⟨3466742045681642131050625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18489290910302091365603333 3466742045681642131050625)
                      ·
                        rfl

theorem cell23_6751456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 4].length) (baseStart_6751456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6751456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6751456 prefixEnd_6751456 := by exact prefixLift 6751456
  have htrace : WordTrace (prefixWord ++ tailWord_6751456) baseStart_6751456 baseEnd_6751456 := by
    simpa [prefixWord, tailWord_6751456, baseEnd_6751456] using wordTrace_append hprefix tailTrace_6751456
  have hstable : (prefixWord ++ tailWord_6751456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6751456).length < 2 ^ (prefixWord ++ tailWord_6751456).sum := by decide
  have hdescent : baseEnd_6751456 < baseStart_6751456 := by decide
  rcases family_descends (prefixWord ++ tailWord_6751456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6751466 : List Nat := [3, 1, 3, 1, 1, 3, 2, 1, 4, 4]
def baseStart_6751466 : Nat := 118140960795 + 6751466 * 2 ^ 59
def prefixEnd_6751466 : Nat := 4983230072969 + 3 ^ 40 * 6751466 * 2
def baseEnd_6751466 : Nat := 1155582393496062363975193

theorem tailTrace_6751466 : CollatzResearch.WordTrace tailWord_6751466 prefixEnd_6751466 1155582393496062363975193 := by
  unfold tailWord_6751466
  simp only [CollatzResearch.WordTrace]
  refine ⟨61561548739649803859556563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164164129972399476958817501 61561548739649803859556563)
  ·
    refine ⟨92342323109474705789334845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61561548739649803859556563 92342323109474705789334845)
    ·
      refine ⟨34628371166053014671000567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92342323109474705789334845 34628371166053014671000567)
      ·
        refine ⟨51942556749079522006500851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34628371166053014671000567 51942556749079522006500851)
        ·
          refine ⟨77913835123619283009751277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51942556749079522006500851 77913835123619283009751277)
          ·
            refine ⟨29217688171357231128656729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77913835123619283009751277 29217688171357231128656729)
            ·
              refine ⟨21913266128517923346492547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29217688171357231128656729 21913266128517923346492547)
              ·
                refine ⟨32869899192776885019738821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21913266128517923346492547 32869899192776885019738821)
                ·
                  refine ⟨6163106098645665941201029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32869899192776885019738821 6163106098645665941201029)
                  ·
                    refine ⟨1155582393496062363975193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6163106098645665941201029 1155582393496062363975193)
                    ·
                      rfl

theorem cell23_6751466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 1, 4, 4].length) (baseStart_6751466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6751466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6751466 prefixEnd_6751466 := by exact prefixLift 6751466
  have htrace : WordTrace (prefixWord ++ tailWord_6751466) baseStart_6751466 baseEnd_6751466 := by
    simpa [prefixWord, tailWord_6751466, baseEnd_6751466] using wordTrace_append hprefix tailTrace_6751466
  have hstable : (prefixWord ++ tailWord_6751466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6751466).length < 2 ^ (prefixWord ++ tailWord_6751466).sum := by decide
  have hdescent : baseEnd_6751466 < baseStart_6751466 := by decide
  rcases family_descends (prefixWord ++ tailWord_6751466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6751486 : List Nat := [4, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6]
def baseStart_6751486 : Nat := 118140960795 + 6751486 * 2 ^ 59
def prefixEnd_6751486 : Nat := 4983230072969 + 3 ^ 40 * 6751486 * 2
def baseEnd_6751486 : Nat := 3466757450101277013675487

theorem tailTrace_6751486 : CollatzResearch.WordTrace tailWord_6751486 prefixEnd_6751486 3466757450101277013675487 := by
  unfold tailWord_6751486
  simp only [CollatzResearch.WordTrace]
  refine ⟨30780865552315844856744289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164164616279017839235969541 30780865552315844856744289)
  ·
    refine ⟨23085649164236883642558217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30780865552315844856744289 23085649164236883642558217)
    ·
      refine ⟨17314236873177662731918663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23085649164236883642558217 17314236873177662731918663)
      ·
        refine ⟨25971355309766494097877995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17314236873177662731918663 25971355309766494097877995)
        ·
          refine ⟨38957032964649741146816993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25971355309766494097877995 38957032964649741146816993)
          ·
            refine ⟨29217774723487305860112745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38957032964649741146816993 29217774723487305860112745)
            ·
              refine ⟨21913331042615479395084559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29217774723487305860112745 21913331042615479395084559)
              ·
                refine ⟨32869996563923219092626839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21913331042615479395084559 32869996563923219092626839)
                ·
                  refine ⟨49304994845884828638940259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32869996563923219092626839 49304994845884828638940259)
                  ·
                    refine ⟨73957492268827242958410389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49304994845884828638940259 73957492268827242958410389)
                    ·
                      refine ⟨3466757450101277013675487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73957492268827242958410389 3466757450101277013675487)
                      ·
                        rfl

theorem cell23_6751486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_6751486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6751486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6751486 prefixEnd_6751486 := by exact prefixLift 6751486
  have htrace : WordTrace (prefixWord ++ tailWord_6751486) baseStart_6751486 baseEnd_6751486 := by
    simpa [prefixWord, tailWord_6751486, baseEnd_6751486] using wordTrace_append hprefix tailTrace_6751486
  have hstable : (prefixWord ++ tailWord_6751486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6751486).length < 2 ^ (prefixWord ++ tailWord_6751486).sum := by decide
  have hdescent : baseEnd_6751486 < baseStart_6751486 := by decide
  rcases family_descends (prefixWord ++ tailWord_6751486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6751518 : List Nat := [4, 3, 2, 1, 3, 1, 2, 2, 1, 1, 3]
def baseStart_6751518 : Nat := 118140960795 + 6751518 * 2 ^ 59
def prefixEnd_6751518 : Nat := 4983230072969 + 3 ^ 40 * 6751518 * 2
def baseEnd_6751518 : Nat := 3466773881482220888475341

theorem tailTrace_6751518 : CollatzResearch.WordTrace tailWord_6751518 prefixEnd_6751518 3466773881482220888475341 := by
  unfold tailWord_6751518
  simp only [CollatzResearch.WordTrace]
  refine ⟨30781011444301353539889901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164165394369607218879412805 30781011444301353539889901)
  ·
    refine ⟨11542879291613007577458713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30781011444301353539889901 11542879291613007577458713)
    ·
      refine ⟨8657159468709755683094035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11542879291613007577458713 8657159468709755683094035)
      ·
        refine ⟨12985739203064633524641053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8657159468709755683094035 12985739203064633524641053)
        ·
          refine ⟨4869652201149237571740395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12985739203064633524641053 4869652201149237571740395)
          ·
            refine ⟨7304478301723856357610593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4869652201149237571740395 7304478301723856357610593)
            ·
              refine ⟨5478358726292892268207945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7304478301723856357610593 5478358726292892268207945)
              ·
                refine ⟨4108769044719669201155959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5478358726292892268207945 4108769044719669201155959)
                ·
                  refine ⟨6163153567079503801733939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4108769044719669201155959 6163153567079503801733939)
                  ·
                    refine ⟨9244730350619255702600909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6163153567079503801733939 9244730350619255702600909)
                    ·
                      refine ⟨3466773881482220888475341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9244730350619255702600909 3466773881482220888475341)
                      ·
                        rfl

theorem cell23_6751518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 2, 2, 1, 1, 3].length) (baseStart_6751518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6751518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6751518 prefixEnd_6751518 := by exact prefixLift 6751518
  have htrace : WordTrace (prefixWord ++ tailWord_6751518) baseStart_6751518 baseEnd_6751518 := by
    simpa [prefixWord, tailWord_6751518, baseEnd_6751518] using wordTrace_append hprefix tailTrace_6751518
  have hstable : (prefixWord ++ tailWord_6751518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6751518).length < 2 ^ (prefixWord ++ tailWord_6751518).sum := by decide
  have hdescent : baseEnd_6751518 < baseStart_6751518 := by decide
  rcases family_descends (prefixWord ++ tailWord_6751518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6751523 : List Nat := [1, 1, 1, 4, 2, 3, 1, 4, 2, 1, 3]
def baseStart_6751523 : Nat := 118140960795 + 6751523 * 2 ^ 59
def prefixEnd_6751523 : Nat := 4983230072969 + 3 ^ 40 * 6751523 * 2
def baseEnd_6751523 : Nat := 3466776448885493368912817

theorem tailTrace_6751523 : CollatzResearch.WordTrace tailWord_6751523 prefixEnd_6751523 3466776448885493368912817 := by
  unfold tailWord_6751523
  simp only [CollatzResearch.WordTrace]
  refine ⟨246248273919392714173051223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164165515946261809448700815 246248273919392714173051223)
  ·
    refine ⟨369372410879089071259576835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246248273919392714173051223 369372410879089071259576835)
    ·
      refine ⟨554058616318633606889365253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369372410879089071259576835 554058616318633606889365253)
      ·
        refine ⟨103885990559743801291755985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 554058616318633606889365253 103885990559743801291755985)
        ·
          refine ⟨77914492919807850968816989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103885990559743801291755985 77914492919807850968816989)
          ·
            refine ⟨29217934844927944113306371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77914492919807850968816989 29217934844927944113306371)
            ·
              refine ⟨43826902267391916169959557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29217934844927944113306371 43826902267391916169959557)
              ·
                refine ⟨8217544175135984281867417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43826902267391916169959557 8217544175135984281867417)
                ·
                  refine ⟨6163158131351988211400563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8217544175135984281867417 6163158131351988211400563)
                  ·
                    refine ⟨9244737197027982317100845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6163158131351988211400563 9244737197027982317100845)
                    ·
                      refine ⟨3466776448885493368912817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9244737197027982317100845 3466776448885493368912817)
                      ·
                        rfl

theorem cell23_6751523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 4, 2, 1, 3].length) (baseStart_6751523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6751523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6751523 prefixEnd_6751523 := by exact prefixLift 6751523
  have htrace : WordTrace (prefixWord ++ tailWord_6751523) baseStart_6751523 baseEnd_6751523 := by
    simpa [prefixWord, tailWord_6751523, baseEnd_6751523] using wordTrace_append hprefix tailTrace_6751523
  have hstable : (prefixWord ++ tailWord_6751523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6751523).length < 2 ^ (prefixWord ++ tailWord_6751523).sum := by decide
  have hdescent : baseEnd_6751523 < baseStart_6751523 := by decide
  rcases family_descends (prefixWord ++ tailWord_6751523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6751539 : List Nat := [1, 1, 1, 2, 5, 2, 1, 1, 1, 8]
def baseStart_6751539 : Nat := 118140960795 + 6751539 * 2 ^ 59
def prefixEnd_6751539 : Nat := 4983230072969 + 3 ^ 40 * 6751539 * 2
def baseEnd_6751539 : Nat := 1155594888191988435437581

theorem tailTrace_6751539 : CollatzResearch.WordTrace tailWord_6751539 prefixEnd_6751539 1155594888191988435437581 := by
  unfold tailWord_6751539
  simp only [CollatzResearch.WordTrace]
  refine ⟨246248857487334748905633671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164165904991556499270422447 246248857487334748905633671)
  ·
    refine ⟨369373286231002123358450507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246248857487334748905633671 369373286231002123358450507)
    ·
      refine ⟨554059929346503185037675761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369373286231002123358450507 554059929346503185037675761)
      ·
        refine ⟨415544947009877388778256821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 554059929346503185037675761 415544947009877388778256821)
        ·
          refine ⟨38957338782176005197961577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 415544947009877388778256821 38957338782176005197961577)
          ·
            refine ⟨29218004086632003898471183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38957338782176005197961577 29218004086632003898471183)
            ·
              refine ⟨43827006129948005847706775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29218004086632003898471183 43827006129948005847706775)
              ·
                refine ⟨65740509194922008771560163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43827006129948005847706775 65740509194922008771560163)
                ·
                  refine ⟨98610763792383013157340245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65740509194922008771560163 98610763792383013157340245)
                  ·
                    refine ⟨1155594888191988435437581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 98610763792383013157340245 1155594888191988435437581)
                    ·
                      rfl

theorem cell23_6751539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 1, 1, 8].length) (baseStart_6751539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6751539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6751539 prefixEnd_6751539 := by exact prefixLift 6751539
  have htrace : WordTrace (prefixWord ++ tailWord_6751539) baseStart_6751539 baseEnd_6751539 := by
    simpa [prefixWord, tailWord_6751539, baseEnd_6751539] using wordTrace_append hprefix tailTrace_6751539
  have hstable : (prefixWord ++ tailWord_6751539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6751539).length < 2 ^ (prefixWord ++ tailWord_6751539).sum := by decide
  have hdescent : baseEnd_6751539 < baseStart_6751539 := by decide
  rcases family_descends (prefixWord ++ tailWord_6751539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6751540 : List Nat := [2, 5, 1, 1, 1, 1, 1, 5, 2, 1, 3]
def baseStart_6751540 : Nat := 118140960795 + 6751540 * 2 ^ 59
def prefixEnd_6751540 : Nat := 4983230072969 + 3 ^ 40 * 6751540 * 2
def baseEnd_6751540 : Nat := 3466785178056619802400239

theorem tailTrace_6751540 : CollatzResearch.WordTrace tailWord_6751540 prefixEnd_6751540 3466785178056619802400239 := by
  unfold tailWord_6751540
  simp only [CollatzResearch.WordTrace]
  refine ⟨123124446980165563038210037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164165929306887417384280049 123124446980165563038210037)
  ·
    refine ⟨11542916904390521534832191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 123124446980165563038210037 11542916904390521534832191)
    ·
      refine ⟨17314375356585782302248287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11542916904390521534832191 17314375356585782302248287)
      ·
        refine ⟨25971563034878673453372431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17314375356585782302248287 25971563034878673453372431)
        ·
          refine ⟨38957344552318010180058647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25971563034878673453372431 38957344552318010180058647)
          ·
            refine ⟨58436016828477015270087971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38957344552318010180058647 58436016828477015270087971)
            ·
              refine ⟨87654025242715522905131957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58436016828477015270087971 87654025242715522905131957)
              ·
                refine ⟨8217564866504580272356121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 87654025242715522905131957 8217564866504580272356121)
                ·
                  refine ⟨6163173649878435204267091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8217564866504580272356121 6163173649878435204267091)
                  ·
                    refine ⟨9244760474817652806400637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6163173649878435204267091 9244760474817652806400637)
                    ·
                      refine ⟨3466785178056619802400239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9244760474817652806400637 3466785178056619802400239)
                      ·
                        rfl

theorem cell23_6751540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 5, 2, 1, 3].length) (baseStart_6751540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6751540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6751540 prefixEnd_6751540 := by exact prefixLift 6751540
  have htrace : WordTrace (prefixWord ++ tailWord_6751540) baseStart_6751540 baseEnd_6751540 := by
    simpa [prefixWord, tailWord_6751540, baseEnd_6751540] using wordTrace_append hprefix tailTrace_6751540
  have hstable : (prefixWord ++ tailWord_6751540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6751540).length < 2 ^ (prefixWord ++ tailWord_6751540).sum := by decide
  have hdescent : baseEnd_6751540 < baseStart_6751540 := by decide
  rcases family_descends (prefixWord ++ tailWord_6751540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6751550 : List Nat := [4, 2, 1, 2, 1, 1, 2, 4, 1, 3, 2]
def baseStart_6751550 : Nat := 118140960795 + 6751550 * 2 ^ 59
def prefixEnd_6751550 : Nat := 4983230072969 + 3 ^ 40 * 6751550 * 2
def baseEnd_6751550 : Nat := 3466790312863164763275193

theorem tailTrace_6751550 : CollatzResearch.WordTrace tailWord_6751550 prefixEnd_6751550 3466790312863164763275193 := by
  unfold tailWord_6751550
  simp only [CollatzResearch.WordTrace]
  refine ⟨30781157336286862223035513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164166172460196598522856069 30781157336286862223035513)
  ·
    refine ⟨23085868002215146667276635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30781157336286862223035513 23085868002215146667276635)
    ·
      refine ⟨34628802003322720000914953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23085868002215146667276635 34628802003322720000914953)
      ·
        refine ⟨25971601502492040000686215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34628802003322720000914953 25971601502492040000686215)
        ·
          refine ⟨38957402253738060001029323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25971601502492040000686215 38957402253738060001029323)
          ·
            refine ⟨58436103380607090001543985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38957402253738060001029323 58436103380607090001543985)
            ·
              refine ⟨43827077535455317501157989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58436103380607090001543985 43827077535455317501157989)
              ·
                refine ⟨8217577037897872031467123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43827077535455317501157989 8217577037897872031467123)
                ·
                  refine ⟨12326365556846808047200685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8217577037897872031467123 12326365556846808047200685)
                  ·
                    refine ⟨4622387083817553017700257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12326365556846808047200685 4622387083817553017700257)
                    ·
                      refine ⟨3466790312863164763275193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4622387083817553017700257 3466790312863164763275193)
                      ·
                        rfl

theorem cell23_6751550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 4, 1, 3, 2].length) (baseStart_6751550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6751550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6751550 prefixEnd_6751550 := by exact prefixLift 6751550
  have htrace : WordTrace (prefixWord ++ tailWord_6751550) baseStart_6751550 baseEnd_6751550 := by
    simpa [prefixWord, tailWord_6751550, baseEnd_6751550] using wordTrace_append hprefix tailTrace_6751550
  have hstable : (prefixWord ++ tailWord_6751550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6751550).length < 2 ^ (prefixWord ++ tailWord_6751550).sum := by decide
  have hdescent : baseEnd_6751550 < baseStart_6751550 := by decide
  rcases family_descends (prefixWord ++ tailWord_6751550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6751558 : List Nat := [6, 1, 1, 3, 1, 1, 2, 3, 1, 2, 2]
def baseStart_6751558 : Nat := 118140960795 + 6751558 * 2 ^ 59
def prefixEnd_6751558 : Nat := 4983230072969 + 3 ^ 40 * 6751558 * 2
def baseEnd_6751558 : Nat := 3466794420708400731975157

theorem tailTrace_6751558 : CollatzResearch.WordTrace tailWord_6751558 prefixEnd_6751558 3466794420708400731975157 := by
  unfold tailWord_6751558
  simp only [CollatzResearch.WordTrace]
  refine ⟨7695298452320809848455479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 164166366982843943433716885 7695298452320809848455479)
  ·
    refine ⟨11542947678481214772683219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7695298452320809848455479 11542947678481214772683219)
    ·
      refine ⟨17314421517721822159024829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11542947678481214772683219 17314421517721822159024829)
      ·
        refine ⟨6492908069145683309634311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17314421517721822159024829 6492908069145683309634311)
        ·
          refine ⟨9739362103718524964451467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6492908069145683309634311 9739362103718524964451467)
          ·
            refine ⟨14609043155577787446677201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9739362103718524964451467 14609043155577787446677201)
            ·
              refine ⟨10956782366683340585007901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14609043155577787446677201 10956782366683340585007901)
              ·
                refine ⟨4108793387506252719377963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10956782366683340585007901 4108793387506252719377963)
                ·
                  refine ⟨6163190081259379079066945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4108793387506252719377963 6163190081259379079066945)
                  ·
                    refine ⟨4622392560944534309300209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6163190081259379079066945 4622392560944534309300209)
                    ·
                      refine ⟨3466794420708400731975157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4622392560944534309300209 3466794420708400731975157)
                      ·
                        rfl

theorem cell23_6751558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_6751558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6751558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6751558 prefixEnd_6751558 := by exact prefixLift 6751558
  have htrace : WordTrace (prefixWord ++ tailWord_6751558) baseStart_6751558 baseEnd_6751558 := by
    simpa [prefixWord, tailWord_6751558, baseEnd_6751558] using wordTrace_append hprefix tailTrace_6751558
  have hstable : (prefixWord ++ tailWord_6751558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6751558).length < 2 ^ (prefixWord ++ tailWord_6751558).sum := by decide
  have hdescent : baseEnd_6751558 < baseStart_6751558 := by decide
  rcases family_descends (prefixWord ++ tailWord_6751558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6751569 : List Nat := [1, 2, 2, 1, 4, 1, 1, 2, 9]
def baseStart_6751569 : Nat := 118140960795 + 6751569 * 2 ^ 59
def prefixEnd_6751569 : Nat := 4983230072969 + 3 ^ 40 * 6751569 * 2
def baseEnd_6751569 : Nat := 385200007666177798770845

theorem tailTrace_6751569 : CollatzResearch.WordTrace tailWord_6751569 prefixEnd_6751569 385200007666177798770845 := by
  unfold tailWord_6751569
  simp only [CollatzResearch.WordTrace]
  refine ⟨246249951677226064029225761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164166634451484042686150507 246249951677226064029225761)
  ·
    refine ⟨184687463757919548021919321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246249951677226064029225761 184687463757919548021919321)
    ·
      refine ⟨138515597818439661016439491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184687463757919548021919321 138515597818439661016439491)
      ·
        refine ⟨207773396727659491524659237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138515597818439661016439491 207773396727659491524659237)
        ·
          refine ⟨38957511886436154660873607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 207773396727659491524659237 38957511886436154660873607)
          ·
            refine ⟨58436267829654231991310411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38957511886436154660873607 58436267829654231991310411)
            ·
              refine ⟨87654401744481347986965617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58436267829654231991310411 87654401744481347986965617)
              ·
                refine ⟨65740801308361010990224213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87654401744481347986965617 65740801308361010990224213)
                ·
                  refine ⟨385200007666177798770845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 65740801308361010990224213 385200007666177798770845)
                  ·
                    rfl

theorem cell23_6751569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 2, 9].length) (baseStart_6751569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6751569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6751569 prefixEnd_6751569 := by exact prefixLift 6751569
  have htrace : WordTrace (prefixWord ++ tailWord_6751569) baseStart_6751569 baseEnd_6751569 := by
    simpa [prefixWord, tailWord_6751569, baseEnd_6751569] using wordTrace_append hprefix tailTrace_6751569
  have hstable : (prefixWord ++ tailWord_6751569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6751569).length < 2 ^ (prefixWord ++ tailWord_6751569).sum := by decide
  have hdescent : baseEnd_6751569 < baseStart_6751569 := by decide
  rcases family_descends (prefixWord ++ tailWord_6751569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6751599 : List Nat := [1, 1, 2, 1, 3, 1, 3, 1, 3, 7]
def baseStart_6751599 : Nat := 118140960795 + 6751599 * 2 ^ 59
def prefixEnd_6751599 : Nat := 4983230072969 + 3 ^ 40 * 6751599 * 2
def baseEnd_6751599 : Nat := 1155605157805078357187489

theorem tailTrace_6751599 : CollatzResearch.WordTrace tailWord_6751599 prefixEnd_6751599 1155605157805078357187489 := by
  unfold tailWord_6751599
  simp only [CollatzResearch.WordTrace]
  refine ⟨246251045867117379152817851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164167363911411586101878567 246251045867117379152817851)
  ·
    refine ⟨369376568800676068729226777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246251045867117379152817851 369376568800676068729226777)
    ·
      refine ⟨277032426600507051546920083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 369376568800676068729226777 277032426600507051546920083)
      ·
        refine ⟨415548639900760577320380125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277032426600507051546920083 415548639900760577320380125)
        ·
          refine ⟨155830739962785216495142547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 415548639900760577320380125 155830739962785216495142547)
          ·
            refine ⟨233746109944177824742713821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155830739962785216495142547 233746109944177824742713821)
            ·
              refine ⟨87654791229066684278517683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 233746109944177824742713821 87654791229066684278517683)
              ·
                refine ⟨131482186843600026417776525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87654791229066684278517683 131482186843600026417776525)
                ·
                  refine ⟨49305820066350009906666197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 131482186843600026417776525 49305820066350009906666197)
                  ·
                    refine ⟨1155605157805078357187489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49305820066350009906666197 1155605157805078357187489)
                    ·
                      rfl

theorem cell23_6751599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 3, 7].length) (baseStart_6751599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6751599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6751599 prefixEnd_6751599 := by exact prefixLift 6751599
  have htrace : WordTrace (prefixWord ++ tailWord_6751599) baseStart_6751599 baseEnd_6751599 := by
    simpa [prefixWord, tailWord_6751599, baseEnd_6751599] using wordTrace_append hprefix tailTrace_6751599
  have hstable : (prefixWord ++ tailWord_6751599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6751599).length < 2 ^ (prefixWord ++ tailWord_6751599).sum := by decide
  have hdescent : baseEnd_6751599 < baseStart_6751599 := by decide
  rcases family_descends (prefixWord ++ tailWord_6751599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6751620 : List Nat := [2, 3, 2, 1, 1, 5, 1, 3, 5]
def baseStart_6751620 : Nat := 118140960795 + 6751620 * 2 ^ 59
def prefixEnd_6751620 : Nat := 4983230072969 + 3 ^ 40 * 6751620 * 2
def baseEnd_6751620 : Nat := 385202917389886609933319

theorem tailTrace_6751620 : CollatzResearch.WordTrace tailWord_6751620 prefixEnd_6751620 385202917389886609933319 := by
  unfold tailWord_6751620
  simp only [CollatzResearch.WordTrace]
  refine ⟨123125905900020649869666157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164167874533360866492888209 123125905900020649869666157)
  ·
    refine ⟨46172214712507743701124809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123125905900020649869666157 46172214712507743701124809)
    ·
      refine ⟨34629161034380807775843607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46172214712507743701124809 34629161034380807775843607)
      ·
        refine ⟨51943741551571211663765411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34629161034380807775843607 51943741551571211663765411)
        ·
          refine ⟨77915612327356817495648117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51943741551571211663765411 77915612327356817495648117)
          ·
            refine ⟨7304588655689701640217011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 77915612327356817495648117 7304588655689701640217011)
            ·
              refine ⟨10956882983534552460325517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7304588655689701640217011 10956882983534552460325517)
              ·
                refine ⟨4108831118825457172622069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10956882983534552460325517 4108831118825457172622069)
                ·
                  refine ⟨385202917389886609933319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4108831118825457172622069 385202917389886609933319)
                  ·
                    rfl

theorem cell23_6751620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 3, 5].length) (baseStart_6751620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6751620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6751620 prefixEnd_6751620 := by exact prefixLift 6751620
  have htrace : WordTrace (prefixWord ++ tailWord_6751620) baseStart_6751620 baseEnd_6751620 := by
    simpa [prefixWord, tailWord_6751620, baseEnd_6751620] using wordTrace_append hprefix tailTrace_6751620
  have hstable : (prefixWord ++ tailWord_6751620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6751620).length < 2 ^ (prefixWord ++ tailWord_6751620).sum := by decide
  have hdescent : baseEnd_6751620 < baseStart_6751620 := by decide
  rcases family_descends (prefixWord ++ tailWord_6751620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6751703 : List Nat := [1, 1, 3, 2, 1, 1, 1, 2, 7, 1, 3]
def baseStart_6751703 : Nat := 118140960795 + 6751703 * 2 ^ 59
def prefixEnd_6751703 : Nat := 4983230072969 + 3 ^ 40 * 6751703 * 2
def baseEnd_6751703 : Nat := 3466868875403302664661989

theorem tailTrace_6751703 : CollatzResearch.WordTrace tailWord_6751703 prefixEnd_6751703 3466868875403302664661989 := by
  unfold tailWord_6751703
  simp only [CollatzResearch.WordTrace]
  refine ⟨246254839058740604914603763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164169892705827069943069175 246254839058740604914603763)
  ·
    refine ⟨369382258588110907371905645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246254839058740604914603763 369382258588110907371905645)
    ·
      refine ⟨138518346970541590264464617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 369382258588110907371905645 138518346970541590264464617)
      ·
        refine ⟨103888760227906192698348463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138518346970541590264464617 103888760227906192698348463)
        ·
          refine ⟨155833140341859289047522695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103888760227906192698348463 155833140341859289047522695)
          ·
            refine ⟨233749710512788933571284043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155833140341859289047522695 233749710512788933571284043)
            ·
              refine ⟨350624565769183400356926065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 233749710512788933571284043 350624565769183400356926065)
              ·
                refine ⟨262968424326887550267694549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 350624565769183400356926065 262968424326887550267694549)
                ·
                  refine ⟨6163322445161426959399091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 262968424326887550267694549 6163322445161426959399091)
                  ·
                    refine ⟨9244983667742140439098637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6163322445161426959399091 9244983667742140439098637)
                    ·
                      refine ⟨3466868875403302664661989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9244983667742140439098637 3466868875403302664661989)
                      ·
                        rfl

theorem cell23_6751703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 7, 1, 3].length) (baseStart_6751703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6751703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6751703 prefixEnd_6751703 := by exact prefixLift 6751703
  have htrace : WordTrace (prefixWord ++ tailWord_6751703) baseStart_6751703 baseEnd_6751703 := by
    simpa [prefixWord, tailWord_6751703, baseEnd_6751703] using wordTrace_append hprefix tailTrace_6751703
  have hstable : (prefixWord ++ tailWord_6751703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6751703).length < 2 ^ (prefixWord ++ tailWord_6751703).sum := by decide
  have hdescent : baseEnd_6751703 < baseStart_6751703 := by decide
  rcases family_descends (prefixWord ++ tailWord_6751703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6751720 : List Nat := [2, 1, 4, 1, 1, 2, 3, 2, 3, 1, 3]
def baseStart_6751720 : Nat := 118140960795 + 6751720 * 2 ^ 59
def prefixEnd_6751720 : Nat := 4983230072969 + 3 ^ 40 * 6751720 * 2
def baseEnd_6751720 : Nat := 3466877604574429098149411

theorem tailTrace_6751720 : CollatzResearch.WordTrace tailWord_6751720 prefixEnd_6751720 3466877604574429098149411 := by
  unfold tailWord_6751720
  simp only [CollatzResearch.WordTrace]
  refine ⟨123127729549839508408986307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164170306066452677878648409 123127729549839508408986307)
  ·
    refine ⟨184691594324759262613479461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123127729549839508408986307 184691594324759262613479461)
    ·
      refine ⟨34629673935892361740027399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 184691594324759262613479461 34629673935892361740027399)
      ·
        refine ⟨51944510903838542610041099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34629673935892361740027399 51944510903838542610041099)
        ·
          refine ⟨77916766355757813915061649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51944510903838542610041099 77916766355757813915061649)
          ·
            refine ⟨58437574766818360436296237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77916766355757813915061649 58437574766818360436296237)
            ·
              refine ⟨21914090537556885163611089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58437574766818360436296237 21914090537556885163611089)
              ·
                refine ⟨16435567903167663872708317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21914090537556885163611089 16435567903167663872708317)
                ·
                  refine ⟨6163337963687873952265619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16435567903167663872708317 6163337963687873952265619)
                  ·
                    refine ⟨9245006945531810928398429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6163337963687873952265619 9245006945531810928398429)
                    ·
                      refine ⟨3466877604574429098149411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9245006945531810928398429 3466877604574429098149411)
                      ·
                        rfl

theorem cell23_6751720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 2, 3, 1, 3].length) (baseStart_6751720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6751720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6751720 prefixEnd_6751720 := by exact prefixLift 6751720
  have htrace : WordTrace (prefixWord ++ tailWord_6751720) baseStart_6751720 baseEnd_6751720 := by
    simpa [prefixWord, tailWord_6751720, baseEnd_6751720] using wordTrace_append hprefix tailTrace_6751720
  have hstable : (prefixWord ++ tailWord_6751720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6751720).length < 2 ^ (prefixWord ++ tailWord_6751720).sum := by decide
  have hdescent : baseEnd_6751720 < baseStart_6751720 := by decide
  rcases family_descends (prefixWord ++ tailWord_6751720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6751740 : List Nat := [2, 2, 2, 1, 2, 1, 6, 1, 1, 5]
def baseStart_6751740 : Nat := 118140960795 + 6751740 * 2 ^ 59
def prefixEnd_6751740 : Nat := 4983230072969 + 3 ^ 40 * 6751740 * 2
def baseEnd_6751740 : Nat := 1155629291395839673299773

theorem tailTrace_6751740 : CollatzResearch.WordTrace tailWord_6751740 prefixEnd_6751740 1155629291395839673299773 := by
  unfold tailWord_6751740
  simp only [CollatzResearch.WordTrace]
  refine ⟨123128094279803280116850337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164170792373071040155800449 123128094279803280116850337)
  ·
    refine ⟨92346070709852460087637753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123128094279803280116850337 92346070709852460087637753)
    ·
      refine ⟨69259553032389345065728315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92346070709852460087637753 69259553032389345065728315)
      ·
        refine ⟨103889329548584017598592473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69259553032389345065728315 103889329548584017598592473)
        ·
          refine ⟨77916997161438013198944355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103889329548584017598592473 77916997161438013198944355)
          ·
            refine ⟨116875495742157019798416533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77916997161438013198944355 116875495742157019798416533)
            ·
              refine ⟨5478538862913610303050775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 116875495742157019798416533 5478538862913610303050775)
              ·
                refine ⟨8217808294370415454576163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5478538862913610303050775 8217808294370415454576163)
                ·
                  refine ⟨12326712441555623181864245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8217808294370415454576163 12326712441555623181864245)
                  ·
                    refine ⟨1155629291395839673299773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12326712441555623181864245 1155629291395839673299773)
                    ·
                      rfl

theorem cell23_6751740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 6, 1, 1, 5].length) (baseStart_6751740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6751740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6751740 prefixEnd_6751740 := by exact prefixLift 6751740
  have htrace : WordTrace (prefixWord ++ tailWord_6751740) baseStart_6751740 baseEnd_6751740 := by
    simpa [prefixWord, tailWord_6751740, baseEnd_6751740] using wordTrace_append hprefix tailTrace_6751740
  have hstable : (prefixWord ++ tailWord_6751740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6751740).length < 2 ^ (prefixWord ++ tailWord_6751740).sum := by decide
  have hdescent : baseEnd_6751740 < baseStart_6751740 := by decide
  rcases family_descends (prefixWord ++ tailWord_6751740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6751753 : List Nat := [1, 2, 1, 1, 3, 1, 5, 1, 4, 4]
def baseStart_6751753 : Nat := 118140960795 + 6751753 * 2 ^ 59
def prefixEnd_6751753 : Nat := 4983230072969 + 3 ^ 40 * 6751753 * 2
def baseEnd_6751753 : Nat := 1155631516478675823012253

theorem tailTrace_6751753 : CollatzResearch.WordTrace tailWord_6751753 prefixEnd_6751753 1155631516478675823012253 := by
  unfold tailWord_6751753
  simp only [CollatzResearch.WordTrace]
  refine ⟨246256662708559463453923913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164171108472372975635949275 246256662708559463453923913)
  ·
    refine ⟨184692497031419597590442935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246256662708559463453923913 184692497031419597590442935)
    ·
      refine ⟨277038745547129396385664403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184692497031419597590442935 277038745547129396385664403)
      ·
        refine ⟨415558118320694094578496605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277038745547129396385664403 415558118320694094578496605)
        ·
          refine ⟨155834294370260285466936227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 415558118320694094578496605 155834294370260285466936227)
          ·
            refine ⟨233751441555390428200404341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155834294370260285466936227 233751441555390428200404341)
            ·
              refine ⟨21914197645817852643787907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 233751441555390428200404341 21914197645817852643787907)
              ·
                refine ⟨32871296468726778965681861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21914197645817852643787907 32871296468726778965681861)
                ·
                  refine ⟨6163368087886271056065349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32871296468726778965681861 6163368087886271056065349)
                  ·
                    refine ⟨1155631516478675823012253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6163368087886271056065349 1155631516478675823012253)
                    ·
                      rfl

theorem cell23_6751753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 1, 4, 4].length) (baseStart_6751753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6751753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6751753 prefixEnd_6751753 := by exact prefixLift 6751753
  have htrace : WordTrace (prefixWord ++ tailWord_6751753) baseStart_6751753 baseEnd_6751753 := by
    simpa [prefixWord, tailWord_6751753, baseEnd_6751753] using wordTrace_append hprefix tailTrace_6751753
  have hstable : (prefixWord ++ tailWord_6751753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6751753).length < 2 ^ (prefixWord ++ tailWord_6751753).sum := by decide
  have hdescent : baseEnd_6751753 < baseStart_6751753 := by decide
  rcases family_descends (prefixWord ++ tailWord_6751753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6751763 : List Nat := [1, 1, 1, 2, 1, 7, 1, 2, 1, 1, 5]
def baseStart_6751763 : Nat := 118140960795 + 6751763 * 2 ^ 59
def prefixEnd_6751763 : Nat := 4983230072969 + 3 ^ 40 * 6751763 * 2
def baseEnd_6751763 : Nat := 3466899684242572429911713

theorem tailTrace_6751763 : CollatzResearch.WordTrace tailWord_6751763 prefixEnd_6751763 3466899684242572429911713 := by
  unfold tailWord_6751763
  simp only [CollatzResearch.WordTrace]
  refine ⟨246257027438523235161787943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164171351625682156774525295 246257027438523235161787943)
  ·
    refine ⟨369385541157784852742681915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246257027438523235161787943 369385541157784852742681915)
    ·
      refine ⟨554078311736677279114022873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369385541157784852742681915 554078311736677279114022873)
      ·
        refine ⟨415558733802507959335517155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 554078311736677279114022873 415558733802507959335517155)
        ·
          refine ⟨623338100703761939003275733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 415558733802507959335517155 623338100703761939003275733)
          ·
            refine ⟨14609486735244420445389275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 623338100703761939003275733 14609486735244420445389275)
            ·
              refine ⟨21914230102866630668083913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14609486735244420445389275 21914230102866630668083913)
              ·
                refine ⟨16435672577149973001062935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21914230102866630668083913 16435672577149973001062935)
                ·
                  refine ⟨24653508865724959501594403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16435672577149973001062935 24653508865724959501594403)
                  ·
                    refine ⟨36980263298587439252391605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24653508865724959501594403 36980263298587439252391605)
                    ·
                      refine ⟨3466899684242572429911713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36980263298587439252391605 3466899684242572429911713)
                      ·
                        rfl

theorem cell23_6751763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 2, 1, 1, 5].length) (baseStart_6751763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6751763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6751763 prefixEnd_6751763 := by exact prefixLift 6751763
  have htrace : WordTrace (prefixWord ++ tailWord_6751763) baseStart_6751763 baseEnd_6751763 := by
    simpa [prefixWord, tailWord_6751763, baseEnd_6751763] using wordTrace_append hprefix tailTrace_6751763
  have hstable : (prefixWord ++ tailWord_6751763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6751763).length < 2 ^ (prefixWord ++ tailWord_6751763).sum := by decide
  have hdescent : baseEnd_6751763 < baseStart_6751763 := by decide
  rcases family_descends (prefixWord ++ tailWord_6751763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6751773 : List Nat := [1, 4, 2, 2, 1, 1, 3, 1, 1, 1, 6]
def baseStart_6751773 : Nat := 118140960795 + 6751773 * 2 ^ 59
def prefixEnd_6751773 : Nat := 4983230072969 + 3 ^ 40 * 6751773 * 2
def baseEnd_6751773 : Nat := 3466904819049117390786667

theorem tailTrace_6751773 : CollatzResearch.WordTrace tailWord_6751773 prefixEnd_6751773 3466904819049117390786667 := by
  unfold tailWord_6751773
  simp only [CollatzResearch.WordTrace]
  refine ⟨246257392168487006869651973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164171594778991337913101315 246257392168487006869651973)
  ·
    refine ⟨46173261031591313788059745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 246257392168487006869651973 46173261031591313788059745)
    ·
      refine ⟨34629945773693485341044809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46173261031591313788059745 34629945773693485341044809)
      ·
        refine ⟨25972459330270114005783607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34629945773693485341044809 25972459330270114005783607)
        ·
          refine ⟨38958688995405171008675411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25972459330270114005783607 38958688995405171008675411)
          ·
            refine ⟨58438033493107756513013117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38958688995405171008675411 58438033493107756513013117)
            ·
              refine ⟨21914262559915408692379919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58438033493107756513013117 21914262559915408692379919)
              ·
                refine ⟨32871393839873113038569879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21914262559915408692379919 32871393839873113038569879)
                ·
                  refine ⟨49307090759809669557854819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32871393839873113038569879 49307090759809669557854819)
                  ·
                    refine ⟨73960636139714504336782229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49307090759809669557854819 73960636139714504336782229)
                    ·
                      refine ⟨3466904819049117390786667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73960636139714504336782229 3466904819049117390786667)
                      ·
                        rfl

theorem cell23_6751773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_6751773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6751773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6751773 prefixEnd_6751773 := by exact prefixLift 6751773
  have htrace : WordTrace (prefixWord ++ tailWord_6751773) baseStart_6751773 baseEnd_6751773 := by
    simpa [prefixWord, tailWord_6751773, baseEnd_6751773] using wordTrace_append hprefix tailTrace_6751773
  have hstable : (prefixWord ++ tailWord_6751773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6751773).length < 2 ^ (prefixWord ++ tailWord_6751773).sum := by decide
  have hdescent : baseEnd_6751773 < baseStart_6751773 := by decide
  rcases family_descends (prefixWord ++ tailWord_6751773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6751777 : List Nat := [1, 2, 3, 2, 2, 2, 2, 2, 3, 2, 2]
def baseStart_6751777 : Nat := 118140960795 + 6751777 * 2 ^ 59
def prefixEnd_6751777 : Nat := 4983230072969 + 3 ^ 40 * 6751777 * 2
def baseEnd_6751777 : Nat := 3466906872971735375136649

theorem tailTrace_6751777 : CollatzResearch.WordTrace tailWord_6751777 prefixEnd_6751777 3466906872971735375136649 := by
  unfold tailWord_6751777
  simp only [CollatzResearch.WordTrace]
  refine ⟨246257538060472515552797585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164171692040315010368531723 246257538060472515552797585)
  ·
    refine ⟨184693153545354386664598189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246257538060472515552797585 184693153545354386664598189)
    ·
      refine ⟨69259932579507894999224321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184693153545354386664598189 69259932579507894999224321)
      ·
        refine ⟨51944949434630921249418241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69259932579507894999224321 51944949434630921249418241)
        ·
          refine ⟨38958712075973190937063681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51944949434630921249418241 38958712075973190937063681)
          ·
            refine ⟨29219034056979893202797761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38958712075973190937063681 29219034056979893202797761)
            ·
              refine ⟨21914275542734919902098321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29219034056979893202797761 21914275542734919902098321)
              ·
                refine ⟨16435706657051189926573741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21914275542734919902098321 16435706657051189926573741)
                ·
                  refine ⟨6163389996394196222465153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16435706657051189926573741 6163389996394196222465153)
                  ·
                    refine ⟨4622542497295647166848865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6163389996394196222465153 4622542497295647166848865)
                    ·
                      refine ⟨3466906872971735375136649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4622542497295647166848865 3466906872971735375136649)
                      ·
                        rfl

theorem cell23_6751777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 2, 3, 2, 2].length) (baseStart_6751777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6751777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6751777 prefixEnd_6751777 := by exact prefixLift 6751777
  have htrace : WordTrace (prefixWord ++ tailWord_6751777) baseStart_6751777 baseEnd_6751777 := by
    simpa [prefixWord, tailWord_6751777, baseEnd_6751777] using wordTrace_append hprefix tailTrace_6751777
  have hstable : (prefixWord ++ tailWord_6751777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6751777).length < 2 ^ (prefixWord ++ tailWord_6751777).sum := by decide
  have hdescent : baseEnd_6751777 < baseStart_6751777 := by decide
  rcases family_descends (prefixWord ++ tailWord_6751777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6751793 : List Nat := [1, 2, 2, 3, 1, 1, 1, 3, 3, 3, 3]
def baseStart_6751793 : Nat := 118140960795 + 6751793 * 2 ^ 59
def prefixEnd_6751793 : Nat := 4983230072969 + 3 ^ 40 * 6751793 * 2
def baseEnd_6751793 : Nat := 3466915088662207312536575

theorem tailTrace_6751793 : CollatzResearch.WordTrace tailWord_6751793 prefixEnd_6751793 3466915088662207312536575 := by
  unfold tailWord_6751793
  simp only [CollatzResearch.WordTrace]
  refine ⟨246258121628414550285380033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164172081085609700190253355 246258121628414550285380033)
  ·
    refine ⟨184693591221310912714035025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246258121628414550285380033 184693591221310912714035025)
    ·
      refine ⟨138520193415983184535526269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184693591221310912714035025 138520193415983184535526269)
      ·
        refine ⟨51945072530993694200822351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138520193415983184535526269 51945072530993694200822351)
        ·
          refine ⟨77917608796490541301233527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51945072530993694200822351 77917608796490541301233527)
          ·
            refine ⟨116876413194735811951850291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77917608796490541301233527 116876413194735811951850291)
            ·
              refine ⟨175314619792103717927775437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116876413194735811951850291 175314619792103717927775437)
              ·
                refine ⟨65742982422038894222915789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 175314619792103717927775437 65742982422038894222915789)
                ·
                  refine ⟨24653618408264585333593421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65742982422038894222915789 24653618408264585333593421)
                  ·
                    refine ⟨9245106903099219500097533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24653618408264585333593421 9245106903099219500097533)
                    ·
                      refine ⟨3466915088662207312536575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9245106903099219500097533 3466915088662207312536575)
                      ·
                        rfl

theorem cell23_6751793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 3, 3, 3, 3].length) (baseStart_6751793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6751793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6751793 prefixEnd_6751793 := by exact prefixLift 6751793
  have htrace : WordTrace (prefixWord ++ tailWord_6751793) baseStart_6751793 baseEnd_6751793 := by
    simpa [prefixWord, tailWord_6751793, baseEnd_6751793] using wordTrace_append hprefix tailTrace_6751793
  have hstable : (prefixWord ++ tailWord_6751793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6751793).length < 2 ^ (prefixWord ++ tailWord_6751793).sum := by decide
  have hdescent : baseEnd_6751793 < baseStart_6751793 := by decide
  rcases family_descends (prefixWord ++ tailWord_6751793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6751821 : List Nat := [1, 6, 1, 1, 3, 2, 2, 1, 2, 4]
def baseStart_6751821 : Nat := 118140960795 + 6751821 * 2 ^ 59
def prefixEnd_6751821 : Nat := 4983230072969 + 3 ^ 40 * 6751821 * 2
def baseEnd_6751821 : Nat := 1155643155373511067662149

theorem tailTrace_6751821 : CollatzResearch.WordTrace tailWord_6751821 prefixEnd_6751821 1155643155373511067662149 := by
  unfold tailWord_6751821
  simp only [CollatzResearch.WordTrace]
  refine ⟨246259142872313111067399317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164172761914875407378266211 246259142872313111067399317)
  ·
    refine ⟨11543397322139677081284343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 246259142872313111067399317 11543397322139677081284343)
    ·
      refine ⟨17315095983209515621926515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11543397322139677081284343 17315095983209515621926515)
      ·
        refine ⟨25972643974814273432889773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17315095983209515621926515 25972643974814273432889773)
        ·
          refine ⟨9739741490555352537333665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25972643974814273432889773 9739741490555352537333665)
          ·
            refine ⟨7304806117916514403000249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9739741490555352537333665 7304806117916514403000249)
            ·
              refine ⟨5478604588437385802250187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7304806117916514403000249 5478604588437385802250187)
              ·
                refine ⟨8217906882656078703375281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5478604588437385802250187 8217906882656078703375281)
                ·
                  refine ⟨6163430161992059027531461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8217906882656078703375281 6163430161992059027531461)
                  ·
                    refine ⟨1155643155373511067662149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6163430161992059027531461 1155643155373511067662149)
                    ·
                      rfl

theorem cell23_6751821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 2, 1, 2, 4].length) (baseStart_6751821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6751821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6751821 prefixEnd_6751821 := by exact prefixLift 6751821
  have htrace : WordTrace (prefixWord ++ tailWord_6751821) baseStart_6751821 baseEnd_6751821 := by
    simpa [prefixWord, tailWord_6751821, baseEnd_6751821] using wordTrace_append hprefix tailTrace_6751821
  have hstable : (prefixWord ++ tailWord_6751821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6751821).length < 2 ^ (prefixWord ++ tailWord_6751821).sum := by decide
  have hdescent : baseEnd_6751821 < baseStart_6751821 := by decide
  rcases family_descends (prefixWord ++ tailWord_6751821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6751863 : List Nat := [1, 1, 3, 1, 1, 3, 1, 4, 2, 2, 4]
def baseStart_6751863 : Nat := 118140960795 + 6751863 * 2 ^ 59
def prefixEnd_6751863 : Nat := 4983230072969 + 3 ^ 40 * 6751863 * 2
def baseEnd_6751863 : Nat := 3466951032308022038661253

theorem tailTrace_6751863 : CollatzResearch.WordTrace tailWord_6751863 prefixEnd_6751863 3466951032308022038661253 := by
  unfold tailWord_6751863
  simp only [CollatzResearch.WordTrace]
  refine ⟨246260674738160952240428243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164173783158773968160285495 246260674738160952240428243)
  ·
    refine ⟨369391012107241428360642365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246260674738160952240428243 369391012107241428360642365)
    ·
      refine ⟨138521629540215535635240887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 369391012107241428360642365 138521629540215535635240887)
      ·
        refine ⟨207782444310323303452861331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138521629540215535635240887 207782444310323303452861331)
        ·
          refine ⟨311673666465484955179291997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207782444310323303452861331 311673666465484955179291997)
          ·
            refine ⟨116877624924556858192234499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 311673666465484955179291997 116877624924556858192234499)
            ·
              refine ⟨175316437386835287288351749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116877624924556858192234499 175316437386835287288351749)
              ·
                refine ⟨32871832010031616366565953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 175316437386835287288351749 32871832010031616366565953)
                ·
                  refine ⟨24653874007523712274924465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32871832010031616366565953 24653874007523712274924465)
                  ·
                    refine ⟨18490405505642784206193349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24653874007523712274924465 18490405505642784206193349)
                    ·
                      refine ⟨3466951032308022038661253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18490405505642784206193349 3466951032308022038661253)
                      ·
                        rfl

theorem cell23_6751863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 4, 2, 2, 4].length) (baseStart_6751863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6751863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6751863 prefixEnd_6751863 := by exact prefixLift 6751863
  have htrace : WordTrace (prefixWord ++ tailWord_6751863) baseStart_6751863 baseEnd_6751863 := by
    simpa [prefixWord, tailWord_6751863, baseEnd_6751863] using wordTrace_append hprefix tailTrace_6751863
  have hstable : (prefixWord ++ tailWord_6751863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6751863).length < 2 ^ (prefixWord ++ tailWord_6751863).sum := by decide
  have hdescent : baseEnd_6751863 < baseStart_6751863 := by decide
  rcases family_descends (prefixWord ++ tailWord_6751863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6751940 : List Nat := [2, 3, 3, 1, 1, 1, 1, 1, 3, 3, 4]
def baseStart_6751940 : Nat := 118140960795 + 6751940 * 2 ^ 59
def prefixEnd_6751940 : Nat := 4983230072969 + 3 ^ 40 * 6751940 * 2
def baseEnd_6751940 : Nat := 3466990570318418237398399

theorem tailTrace_6751940 : CollatzResearch.WordTrace tailWord_6751940 prefixEnd_6751940 3466990570318418237398399 := by
  unfold tailWord_6751940
  simp only [CollatzResearch.WordTrace]
  refine ⟨123131741579440997195490637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164175655439254662927320849 123131741579440997195490637)
  ·
    refine ⟨46174403092290373948308989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123131741579440997195490637 46174403092290373948308989)
    ·
      refine ⟨17315401159608890230615871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46174403092290373948308989 17315401159608890230615871)
      ·
        refine ⟨25973101739413335345923807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17315401159608890230615871 25973101739413335345923807)
        ·
          refine ⟨38959652609120003018885711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25973101739413335345923807 38959652609120003018885711)
          ·
            refine ⟨58439478913680004528328567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38959652609120003018885711 58439478913680004528328567)
            ·
              refine ⟨87659218370520006792492851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58439478913680004528328567 87659218370520006792492851)
              ·
                refine ⟨131488827555780010188739277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87659218370520006792492851 131488827555780010188739277)
                ·
                  refine ⟨49308310333417503820777229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 131488827555780010188739277 49308310333417503820777229)
                  ·
                    refine ⟨18490616375031563932791461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49308310333417503820777229 18490616375031563932791461)
                    ·
                      refine ⟨3466990570318418237398399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18490616375031563932791461 3466990570318418237398399)
                      ·
                        rfl

theorem cell23_6751940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_6751940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6751940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6751940 prefixEnd_6751940 := by exact prefixLift 6751940
  have htrace : WordTrace (prefixWord ++ tailWord_6751940) baseStart_6751940 baseEnd_6751940 := by
    simpa [prefixWord, tailWord_6751940, baseEnd_6751940] using wordTrace_append hprefix tailTrace_6751940
  have hstable : (prefixWord ++ tailWord_6751940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6751940).length < 2 ^ (prefixWord ++ tailWord_6751940).sum := by decide
  have hdescent : baseEnd_6751940 < baseStart_6751940 := by decide
  rcases family_descends (prefixWord ++ tailWord_6751940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6751958 : List Nat := [5, 2, 1, 3, 1, 2, 1, 3, 5]
def baseStart_6751958 : Nat := 118140960795 + 6751958 * 2 ^ 59
def prefixEnd_6751958 : Nat := 4983230072969 + 3 ^ 40 * 6751958 * 2
def baseEnd_6751958 : Nat := 385222201441133240774813

theorem tailTrace_6751958 : CollatzResearch.WordTrace tailWord_6751958 prefixEnd_6751958 385222201441133240774813 := by
  unfold tailWord_6751958
  simp only [CollatzResearch.WordTrace]
  refine ⟨15391508729551048966571033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 164176093115211188976757685 15391508729551048966571033)
  ·
    refine ⟨11543631547163286724928275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15391508729551048966571033 11543631547163286724928275)
    ·
      refine ⟨17315447320744930087392413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11543631547163286724928275 17315447320744930087392413)
      ·
        refine ⟨6493292745279348782772155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17315447320744930087392413 6493292745279348782772155)
        ·
          refine ⟨9739939117919023174158233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6493292745279348782772155 9739939117919023174158233)
          ·
            refine ⟨7304954338439267380618675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9739939117919023174158233 7304954338439267380618675)
            ·
              refine ⟨10957431507658901070928013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7304954338439267380618675 10957431507658901070928013)
              ·
                refine ⟨4109036815372087901598005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10957431507658901070928013 4109036815372087901598005)
                ·
                  refine ⟨385222201441133240774813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4109036815372087901598005 385222201441133240774813)
                  ·
                    rfl

theorem cell23_6751958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 3, 5].length) (baseStart_6751958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6751958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6751958 prefixEnd_6751958 := by exact prefixLift 6751958
  have htrace : WordTrace (prefixWord ++ tailWord_6751958) baseStart_6751958 baseEnd_6751958 := by
    simpa [prefixWord, tailWord_6751958, baseEnd_6751958] using wordTrace_append hprefix tailTrace_6751958
  have hstable : (prefixWord ++ tailWord_6751958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6751958).length < 2 ^ (prefixWord ++ tailWord_6751958).sum := by decide
  have hdescent : baseEnd_6751958 < baseStart_6751958 := by decide
  rcases family_descends (prefixWord ++ tailWord_6751958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6751960 : List Nat := [2, 1, 2, 2, 3, 1, 1, 3, 1, 4, 3]
def baseStart_6751960 : Nat := 118140960795 + 6751960 * 2 ^ 59
def prefixEnd_6751960 : Nat := 4983230072969 + 3 ^ 40 * 6751960 * 2
def baseEnd_6751960 : Nat := 3467000839931508159148307

theorem tailTrace_6751960 : CollatzResearch.WordTrace tailWord_6751960 prefixEnd_6751960 3467000839931508159148307 := by
  unfold tailWord_6751960
  simp only [CollatzResearch.WordTrace]
  refine ⟨123132106309404768903354667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164176141745873025204472889 123132106309404768903354667)
  ·
    refine ⟨184698159464107153355032001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123132106309404768903354667 184698159464107153355032001)
    ·
      refine ⟨138523619598080365016274001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184698159464107153355032001 138523619598080365016274001)
      ·
        refine ⟨103892714698560273762205501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138523619598080365016274001 103892714698560273762205501)
        ·
          refine ⟨38959768011960102660827063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103892714698560273762205501 38959768011960102660827063)
          ·
            refine ⟨58439652017940153991240595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38959768011960102660827063 58439652017940153991240595)
            ·
              refine ⟨87659478026910230986860893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58439652017940153991240595 87659478026910230986860893)
              ·
                refine ⟨32872304260091336620072835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87659478026910230986860893 32872304260091336620072835)
                ·
                  refine ⟨49308456390137004930109253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32872304260091336620072835 49308456390137004930109253)
                  ·
                    refine ⟨9245335573150688424395485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49308456390137004930109253 9245335573150688424395485)
                    ·
                      refine ⟨3467000839931508159148307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9245335573150688424395485 3467000839931508159148307)
                      ·
                        rfl

theorem cell23_6751960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 3, 1, 4, 3].length) (baseStart_6751960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6751960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6751960 prefixEnd_6751960 := by exact prefixLift 6751960
  have htrace : WordTrace (prefixWord ++ tailWord_6751960) baseStart_6751960 baseEnd_6751960 := by
    simpa [prefixWord, tailWord_6751960, baseEnd_6751960] using wordTrace_append hprefix tailTrace_6751960
  have hstable : (prefixWord ++ tailWord_6751960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6751960).length < 2 ^ (prefixWord ++ tailWord_6751960).sum := by decide
  have hdescent : baseEnd_6751960 < baseStart_6751960 := by decide
  rcases family_descends (prefixWord ++ tailWord_6751960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6751993 : List Nat := [1, 2, 1, 3, 1, 1, 1, 1, 1, 11]
def baseStart_6751993 : Nat := 118140960795 + 6751993 * 2 ^ 59
def prefixEnd_6751993 : Nat := 4983230072969 + 3 ^ 40 * 6751993 * 2
def baseEnd_6751993 : Nat := 1155672594931035510011885

theorem tailTrace_6751993 : CollatzResearch.WordTrace tailWord_6751993 prefixEnd_6751993 1155672594931035510011885 := by
  unfold tailWord_6751993
  simp only [CollatzResearch.WordTrace]
  refine ⟨246265416227689984442660633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164176944151793322961773755 246265416227689984442660633)
  ·
    refine ⟨184699062170767488331995475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246265416227689984442660633 184699062170767488331995475)
    ·
      refine ⟨277048593256151232497993213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184699062170767488331995475 277048593256151232497993213)
      ·
        refine ⟨103893222471056712186747455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 277048593256151232497993213 103893222471056712186747455)
        ·
          refine ⟨155839833706585068280121183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103893222471056712186747455 155839833706585068280121183)
          ·
            refine ⟨233759750559877602420181775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155839833706585068280121183 233759750559877602420181775)
            ·
              refine ⟨350639625839816403630272663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 233759750559877602420181775 350639625839816403630272663)
              ·
                refine ⟨525959438759724605445408995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 350639625839816403630272663 525959438759724605445408995)
                ·
                  refine ⟨788939158139586908168113493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 525959438759724605445408995 788939158139586908168113493)
                  ·
                    refine ⟨1155672594931035510011885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 788939158139586908168113493 1155672594931035510011885)
                    ·
                      rfl

theorem cell23_6751993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 11].length) (baseStart_6751993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6751993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6751993 prefixEnd_6751993 := by exact prefixLift 6751993
  have htrace : WordTrace (prefixWord ++ tailWord_6751993) baseStart_6751993 baseEnd_6751993 := by
    simpa [prefixWord, tailWord_6751993, baseEnd_6751993] using wordTrace_append hprefix tailTrace_6751993
  have hstable : (prefixWord ++ tailWord_6751993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6751993).length < 2 ^ (prefixWord ++ tailWord_6751993).sum := by decide
  have hdescent : baseEnd_6751993 < baseStart_6751993 := by decide
  rcases family_descends (prefixWord ++ tailWord_6751993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6752034 : List Nat := [3, 3, 1, 1, 2, 1, 1, 4, 2, 3, 2]
def baseStart_6752034 : Nat := 118140960795 + 6752034 * 2 ^ 59
def prefixEnd_6752034 : Nat := 4983230072969 + 3 ^ 40 * 6752034 * 2
def baseEnd_6752034 : Nat := 3467038837499940869622967

theorem tailTrace_6752034 : CollatzResearch.WordTrace tailWord_6752034 prefixEnd_6752034 3467038837499940869622967 := by
  unfold tailWord_6752034
  simp only [CollatzResearch.WordTrace]
  refine ⟨61566727905135362111225789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164177941080360965629935437 61566727905135362111225789)
  ·
    refine ⟨23087522964425760791709671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61566727905135362111225789 23087522964425760791709671)
    ·
      refine ⟨34631284446638641187564507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23087522964425760791709671 34631284446638641187564507)
      ·
        refine ⟨51946926669957961781346761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34631284446638641187564507 51946926669957961781346761)
        ·
          refine ⟨38960195002468471336010071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51946926669957961781346761 38960195002468471336010071)
          ·
            refine ⟨58440292503702707004015107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38960195002468471336010071 58440292503702707004015107)
            ·
              refine ⟨87660438755554060506022661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58440292503702707004015107 87660438755554060506022661)
              ·
                refine ⟨16436332266666386344879249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87660438755554060506022661 16436332266666386344879249)
                ·
                  refine ⟨12327249199999789758659437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16436332266666386344879249 12327249199999789758659437)
                  ·
                    refine ⟨4622718449999921159497289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12327249199999789758659437 4622718449999921159497289)
                    ·
                      refine ⟨3467038837499940869622967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4622718449999921159497289 3467038837499940869622967)
                      ·
                        rfl

theorem cell23_6752034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 4, 2, 3, 2].length) (baseStart_6752034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6752034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6752034 prefixEnd_6752034 := by exact prefixLift 6752034
  have htrace : WordTrace (prefixWord ++ tailWord_6752034) baseStart_6752034 baseEnd_6752034 := by
    simpa [prefixWord, tailWord_6752034, baseEnd_6752034] using wordTrace_append hprefix tailTrace_6752034
  have hstable : (prefixWord ++ tailWord_6752034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6752034).length < 2 ^ (prefixWord ++ tailWord_6752034).sum := by decide
  have hdescent : baseEnd_6752034 < baseStart_6752034 := by decide
  rcases family_descends (prefixWord ++ tailWord_6752034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6752060 : List Nat := [2, 2, 2, 2, 1, 1, 2, 3, 1, 1, 6]
def baseStart_6752060 : Nat := 118140960795 + 6752060 * 2 ^ 59
def prefixEnd_6752060 : Nat := 4983230072969 + 3 ^ 40 * 6752060 * 2
def baseEnd_6752060 : Nat := 3467052187996957767897847

theorem tailTrace_6752060 : CollatzResearch.WordTrace tailWord_6752060 prefixEnd_6752060 3467052187996957767897847 := by
  unfold tailWord_6752060
  simp only [CollatzResearch.WordTrace]
  refine ⟨123133929959223627442674817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164178573278964836590233089 123133929959223627442674817)
  ·
    refine ⟨92350447469417720582006113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123133929959223627442674817 92350447469417720582006113)
    ·
      refine ⟨69262835602063290436504585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92350447469417720582006113 69262835602063290436504585)
      ·
        refine ⟨51947126701547467827378439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69262835602063290436504585 51947126701547467827378439)
        ·
          refine ⟨77920690052321201741067659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51947126701547467827378439 77920690052321201741067659)
          ·
            refine ⟨116881035078481802611601489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77920690052321201741067659 116881035078481802611601489)
            ·
              refine ⟨87660776308861351958701117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116881035078481802611601489 87660776308861351958701117)
              ·
                refine ⟨32872791115823006984512919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87660776308861351958701117 32872791115823006984512919)
                ·
                  refine ⟨49309186673734510476769379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32872791115823006984512919 49309186673734510476769379)
                  ·
                    refine ⟨73963780010601765715154069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49309186673734510476769379 73963780010601765715154069)
                    ·
                      refine ⟨3467052187996957767897847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73963780010601765715154069 3467052187996957767897847)
                      ·
                        rfl

theorem cell23_6752060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 3, 1, 1, 6].length) (baseStart_6752060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6752060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6752060 prefixEnd_6752060 := by exact prefixLift 6752060
  have htrace : WordTrace (prefixWord ++ tailWord_6752060) baseStart_6752060 baseEnd_6752060 := by
    simpa [prefixWord, tailWord_6752060, baseEnd_6752060] using wordTrace_append hprefix tailTrace_6752060
  have hstable : (prefixWord ++ tailWord_6752060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6752060).length < 2 ^ (prefixWord ++ tailWord_6752060).sum := by decide
  have hdescent : baseEnd_6752060 < baseStart_6752060 := by decide
  rcases family_descends (prefixWord ++ tailWord_6752060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6752067 : List Nat := [1, 1, 1, 3, 1, 5, 2, 1, 3, 2, 3]
def baseStart_6752067 : Nat := 118140960795 + 6752067 * 2 ^ 59
def prefixEnd_6752067 : Nat := 4983230072969 + 3 ^ 40 * 6752067 * 2
def baseEnd_6752067 : Nat := 3467055782361539240510315

theorem tailTrace_6752067 : CollatzResearch.WordTrace tailWord_6752067 prefixEnd_6752067 3467055782361539240510315 := by
  unfold tailWord_6752067
  simp only [CollatzResearch.WordTrace]
  refine ⟨246268115229421895080854455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164178743486281263387236303 246268115229421895080854455)
  ·
    refine ⟨369402172844132842621281683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246268115229421895080854455 369402172844132842621281683)
    ·
      refine ⟨554103259266199263931922525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369402172844132842621281683 554103259266199263931922525)
      ·
        refine ⟨207788722224824723974470947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 554103259266199263931922525 207788722224824723974470947)
        ·
          refine ⟨311683083337237085961706421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207788722224824723974470947 311683083337237085961706421)
          ·
            refine ⟨29220289062865976808909977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 311683083337237085961706421 29220289062865976808909977)
            ·
              refine ⟨21915216797149482606682483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29220289062865976808909977 21915216797149482606682483)
              ·
                refine ⟨32872825195724223910023725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21915216797149482606682483 32872825195724223910023725)
                ·
                  refine ⟨12327309448396583966258897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32872825195724223910023725 12327309448396583966258897)
                  ·
                    refine ⟨9245482086297437974694173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12327309448396583966258897 9245482086297437974694173)
                    ·
                      refine ⟨3467055782361539240510315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9245482086297437974694173 3467055782361539240510315)
                      ·
                        rfl

theorem cell23_6752067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 1, 3, 2, 3].length) (baseStart_6752067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6752067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6752067 prefixEnd_6752067 := by exact prefixLift 6752067
  have htrace : WordTrace (prefixWord ++ tailWord_6752067) baseStart_6752067 baseEnd_6752067 := by
    simpa [prefixWord, tailWord_6752067, baseEnd_6752067] using wordTrace_append hprefix tailTrace_6752067
  have hstable : (prefixWord ++ tailWord_6752067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6752067).length < 2 ^ (prefixWord ++ tailWord_6752067).sum := by decide
  have hdescent : baseEnd_6752067 < baseStart_6752067 := by decide
  rcases family_descends (prefixWord ++ tailWord_6752067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6752081 : List Nat := [1, 2, 2, 1, 5, 3, 2, 1, 1, 1, 4]
def baseStart_6752081 : Nat := 118140960795 + 6752081 * 2 ^ 59
def prefixEnd_6752081 : Nat := 4983230072969 + 3 ^ 40 * 6752081 * 2
def baseEnd_6752081 : Nat := 3467062971090702185735251

theorem tailTrace_6752081 : CollatzResearch.WordTrace tailWord_6752081 prefixEnd_6752081 3467062971090702185735251 := by
  unfold tailWord_6752081
  simp only [CollatzResearch.WordTrace]
  refine ⟨246268625851371175471864097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164179083900914116981242731 246268625851371175471864097)
  ·
    refine ⟨184701469388528381603898073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246268625851371175471864097 184701469388528381603898073)
    ·
      refine ⟨138526102041396286202923555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184701469388528381603898073 138526102041396286202923555)
      ·
        refine ⟨207789153062094429304385333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138526102041396286202923555 207789153062094429304385333)
        ·
          refine ⟨19480233099571352747286125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 207789153062094429304385333 19480233099571352747286125)
          ·
            refine ⟨7305087412339257280232297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19480233099571352747286125 7305087412339257280232297)
            ·
              refine ⟨5478815559254442960174223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7305087412339257280232297 5478815559254442960174223)
              ·
                refine ⟨8218223338881664440261335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5478815559254442960174223 8218223338881664440261335)
                ·
                  refine ⟨12327335008322496660392003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8218223338881664440261335 12327335008322496660392003)
                  ·
                    refine ⟨18491002512483744990588005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12327335008322496660392003 18491002512483744990588005)
                    ·
                      refine ⟨3467062971090702185735251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18491002512483744990588005 3467062971090702185735251)
                      ·
                        rfl

theorem cell23_6752081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 2, 1, 1, 1, 4].length) (baseStart_6752081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6752081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6752081 prefixEnd_6752081 := by exact prefixLift 6752081
  have htrace : WordTrace (prefixWord ++ tailWord_6752081) baseStart_6752081 baseEnd_6752081 := by
    simpa [prefixWord, tailWord_6752081, baseEnd_6752081] using wordTrace_append hprefix tailTrace_6752081
  have hstable : (prefixWord ++ tailWord_6752081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6752081).length < 2 ^ (prefixWord ++ tailWord_6752081).sum := by decide
  have hdescent : baseEnd_6752081 < baseStart_6752081 := by decide
  rcases family_descends (prefixWord ++ tailWord_6752081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6752098 : List Nat := [3, 3, 2, 1, 2, 2, 2, 1, 3, 2, 2]
def baseStart_6752098 : Nat := 118140960795 + 6752098 * 2 ^ 59
def prefixEnd_6752098 : Nat := 4983230072969 + 3 ^ 40 * 6752098 * 2
def baseEnd_6752098 : Nat := 3467071700261828619222673

theorem tailTrace_6752098 : CollatzResearch.WordTrace tailWord_6752098 prefixEnd_6752098 3467071700261828619222673 := by
  unfold tailWord_6752098
  simp only [CollatzResearch.WordTrace]
  refine ⟨61567311473077396843808237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164179497261539724916821965 61567311473077396843808237)
  ·
    refine ⟨23087741802404023816428089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61567311473077396843808237 23087741802404023816428089)
    ·
      refine ⟨17315806351803017862321067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23087741802404023816428089 17315806351803017862321067)
      ·
        refine ⟨25973709527704526793481601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17315806351803017862321067 25973709527704526793481601)
        ·
          refine ⟨19480282145778395095111201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25973709527704526793481601 19480282145778395095111201)
          ·
            refine ⟨14610211609333796321333401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19480282145778395095111201 14610211609333796321333401)
            ·
              refine ⟨10957658707000347241000051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14610211609333796321333401 10957658707000347241000051)
              ·
                refine ⟨16436488060500520861500077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10957658707000347241000051 16436488060500520861500077)
                ·
                  refine ⟨6163683022687695323062529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16436488060500520861500077 6163683022687695323062529)
                  ·
                    refine ⟨4622762267015771492296897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6163683022687695323062529 4622762267015771492296897)
                    ·
                      refine ⟨3467071700261828619222673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4622762267015771492296897 3467071700261828619222673)
                      ·
                        rfl

theorem cell23_6752098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 1, 3, 2, 2].length) (baseStart_6752098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6752098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6752098 prefixEnd_6752098 := by exact prefixLift 6752098
  have htrace : WordTrace (prefixWord ++ tailWord_6752098) baseStart_6752098 baseEnd_6752098 := by
    simpa [prefixWord, tailWord_6752098, baseEnd_6752098] using wordTrace_append hprefix tailTrace_6752098
  have hstable : (prefixWord ++ tailWord_6752098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6752098).length < 2 ^ (prefixWord ++ tailWord_6752098).sum := by decide
  have hdescent : baseEnd_6752098 < baseStart_6752098 := by decide
  rcases family_descends (prefixWord ++ tailWord_6752098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6752118 : List Nat := [5, 1, 1, 3, 2, 1, 2, 2, 1, 2, 3]
def baseStart_6752118 : Nat := 118140960795 + 6752118 * 2 ^ 59
def prefixEnd_6752118 : Nat := 4983230072969 + 3 ^ 40 * 6752118 * 2
def baseEnd_6752118 : Nat := 3467081969874918540972581

theorem tailTrace_6752118 : CollatzResearch.WordTrace tailWord_6752118 prefixEnd_6752118 3467081969874918540972581 := by
  unfold tailWord_6752118
  simp only [CollatzResearch.WordTrace]
  refine ⟨15391873459514820674435063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 164179983568158087193974005 15391873459514820674435063)
  ·
    refine ⟨23087810189272231011652595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15391873459514820674435063 23087810189272231011652595)
    ·
      refine ⟨34631715283908346517478893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23087810189272231011652595 34631715283908346517478893)
      ·
        refine ⟨12986893231465629944054585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34631715283908346517478893 12986893231465629944054585)
        ·
          refine ⟨9740169923599222458040939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12986893231465629944054585 9740169923599222458040939)
          ·
            refine ⟨14610254885398833687061409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9740169923599222458040939 14610254885398833687061409)
            ·
              refine ⟨10957691164049125265296057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14610254885398833687061409 10957691164049125265296057)
              ·
                refine ⟨8218268373036843948972043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10957691164049125265296057 8218268373036843948972043)
                ·
                  refine ⟨12327402559555265923458065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8218268373036843948972043 12327402559555265923458065)
                  ·
                    refine ⟨9245551919666449442593549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12327402559555265923458065 9245551919666449442593549)
                    ·
                      refine ⟨3467081969874918540972581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9245551919666449442593549 3467081969874918540972581)
                      ·
                        rfl

theorem cell23_6752118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_6752118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6752118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6752118 prefixEnd_6752118 := by exact prefixLift 6752118
  have htrace : WordTrace (prefixWord ++ tailWord_6752118) baseStart_6752118 baseEnd_6752118 := by
    simpa [prefixWord, tailWord_6752118, baseEnd_6752118] using wordTrace_append hprefix tailTrace_6752118
  have hstable : (prefixWord ++ tailWord_6752118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6752118).length < 2 ^ (prefixWord ++ tailWord_6752118).sum := by decide
  have hdescent : baseEnd_6752118 < baseStart_6752118 := by decide
  rcases family_descends (prefixWord ++ tailWord_6752118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6752120 : List Nat := [2, 1, 2, 1, 1, 1, 1, 2, 3, 5, 4]
def baseStart_6752120 : Nat := 118140960795 + 6752120 * 2 ^ 59
def prefixEnd_6752120 : Nat := 4983230072969 + 3 ^ 40 * 6752120 * 2
def baseEnd_6752120 : Nat := 3467082996836227533147571

theorem tailTrace_6752120 : CollatzResearch.WordTrace tailWord_6752120 prefixEnd_6752120 3467082996836227533147571 := by
  unfold tailWord_6752120
  simp only [CollatzResearch.WordTrace]
  refine ⟨123135024149114942566266907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164180032198819923421689209 123135024149114942566266907)
  ·
    refine ⟨184702536223672413849400361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123135024149114942566266907 184702536223672413849400361)
    ·
      refine ⟨138526902167754310387050271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184702536223672413849400361 138526902167754310387050271)
      ·
        refine ⟨207790353251631465580575407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138526902167754310387050271 207790353251631465580575407)
        ·
          refine ⟨311685529877447198370863111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207790353251631465580575407 311685529877447198370863111)
          ·
            refine ⟨467528294816170797556294667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 311685529877447198370863111 467528294816170797556294667)
            ·
              refine ⟨701292442224256196334442001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 467528294816170797556294667 701292442224256196334442001)
              ·
                refine ⟨525969331668192147250831501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 701292442224256196334442001 525969331668192147250831501)
                ·
                  refine ⟨197238499375572055219061813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 525969331668192147250831501 197238499375572055219061813)
                  ·
                    refine ⟨18491109316459880176787045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 197238499375572055219061813 18491109316459880176787045)
                    ·
                      refine ⟨3467082996836227533147571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18491109316459880176787045 3467082996836227533147571)
                      ·
                        rfl

theorem cell23_6752120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 3, 5, 4].length) (baseStart_6752120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6752120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6752120 prefixEnd_6752120 := by exact prefixLift 6752120
  have htrace : WordTrace (prefixWord ++ tailWord_6752120) baseStart_6752120 baseEnd_6752120 := by
    simpa [prefixWord, tailWord_6752120, baseEnd_6752120] using wordTrace_append hprefix tailTrace_6752120
  have hstable : (prefixWord ++ tailWord_6752120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6752120).length < 2 ^ (prefixWord ++ tailWord_6752120).sum := by decide
  have hdescent : baseEnd_6752120 < baseStart_6752120 := by decide
  rcases family_descends (prefixWord ++ tailWord_6752120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6752188 : List Nat := [2, 2, 2, 5, 1, 1, 1, 2, 1, 4, 2]
def baseStart_6752188 : Nat := 118140960795 + 6752188 * 2 ^ 59
def prefixEnd_6752188 : Nat := 4983230072969 + 3 ^ 40 * 6752188 * 2
def baseEnd_6752188 : Nat := 3467117913520733267097259

theorem tailTrace_6752188 : CollatzResearch.WordTrace tailWord_6752188 prefixEnd_6752188 3467117913520733267097259 := by
  unfold tailWord_6752188
  simp only [CollatzResearch.WordTrace]
  refine ⟨123136264230991766373004609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164181685641322355164006145 123136264230991766373004609)
  ·
    refine ⟨92352198173243824779753457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123136264230991766373004609 92352198173243824779753457)
    ·
      refine ⟨69264148629932868584815093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92352198173243824779753457 69264148629932868584815093)
      ·
        refine ⟨6493513934056206429826415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 69264148629932868584815093 6493513934056206429826415)
        ·
          refine ⟨9740270901084309644739623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6493513934056206429826415 9740270901084309644739623)
          ·
            refine ⟨14610406351626464467109435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9740270901084309644739623 14610406351626464467109435)
            ·
              refine ⟨21915609527439696700664153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14610406351626464467109435 21915609527439696700664153)
              ·
                refine ⟨16436707145579772525498115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21915609527439696700664153 16436707145579772525498115)
                ·
                  refine ⟨24655060718369658788247173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16436707145579772525498115 24655060718369658788247173)
                  ·
                    refine ⟨4622823884694311022796345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24655060718369658788247173 4622823884694311022796345)
                    ·
                      refine ⟨3467117913520733267097259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4622823884694311022796345 3467117913520733267097259)
                      ·
                        rfl

theorem cell23_6752188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_6752188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6752188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6752188 prefixEnd_6752188 := by exact prefixLift 6752188
  have htrace : WordTrace (prefixWord ++ tailWord_6752188) baseStart_6752188 baseEnd_6752188 := by
    simpa [prefixWord, tailWord_6752188, baseEnd_6752188] using wordTrace_append hprefix tailTrace_6752188
  have hstable : (prefixWord ++ tailWord_6752188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6752188).length < 2 ^ (prefixWord ++ tailWord_6752188).sum := by decide
  have hdescent : baseEnd_6752188 < baseStart_6752188 := by decide
  rcases family_descends (prefixWord ++ tailWord_6752188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6752207 : List Nat := [1, 1, 2, 1, 1, 5, 1, 4, 2, 5]
def baseStart_6752207 : Nat := 118140960795 + 6752207 * 2 ^ 59
def prefixEnd_6752207 : Nat := 4983230072969 + 3 ^ 40 * 6752207 * 2
def baseEnd_6752207 : Nat := 1155709223217722897586557

theorem tailTrace_6752207 : CollatzResearch.WordTrace tailWord_6752207 prefixEnd_6752207 1155709223217722897586557 := by
  unfold tailWord_6752207
  simp only [CollatzResearch.WordTrace]
  refine ⟨246273221448914698990950875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164182147632609799327300583 246273221448914698990950875)
  ·
    refine ⟨369409832173372048486426313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246273221448914698990950875 369409832173372048486426313)
    ·
      refine ⟨277057374130029036364819735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 369409832173372048486426313 277057374130029036364819735)
      ·
        refine ⟨415586061195043554547229603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277057374130029036364819735 415586061195043554547229603)
        ·
          refine ⟨623379091792565331820844405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 415586061195043554547229603 623379091792565331820844405)
          ·
            refine ⟨58441789855552999858204163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 623379091792565331820844405 58441789855552999858204163)
            ·
              refine ⟨87662684783329499787306245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58441789855552999858204163 87662684783329499787306245)
              ·
                refine ⟨16436753396874281210119921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87662684783329499787306245 16436753396874281210119921)
                ·
                  refine ⟨12327565047655710907589941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16436753396874281210119921 12327565047655710907589941)
                  ·
                    refine ⟨1155709223217722897586557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12327565047655710907589941 1155709223217722897586557)
                    ·
                      rfl

theorem cell23_6752207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 4, 2, 5].length) (baseStart_6752207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6752207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6752207 prefixEnd_6752207 := by exact prefixLift 6752207
  have htrace : WordTrace (prefixWord ++ tailWord_6752207) baseStart_6752207 baseEnd_6752207 := by
    simpa [prefixWord, tailWord_6752207, baseEnd_6752207] using wordTrace_append hprefix tailTrace_6752207
  have hstable : (prefixWord ++ tailWord_6752207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6752207).length < 2 ^ (prefixWord ++ tailWord_6752207).sum := by decide
  have hdescent : baseEnd_6752207 < baseStart_6752207 := by decide
  rcases family_descends (prefixWord ++ tailWord_6752207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6752221 : List Nat := [1, 4, 3, 1, 3, 1, 1, 1, 2, 3, 3]
def baseStart_6752221 : Nat := 118140960795 + 6752221 * 2 ^ 59
def prefixEnd_6752221 : Nat := 4983230072969 + 3 ^ 40 * 6752221 * 2
def baseEnd_6752221 : Nat := 3467134858382331637984607

theorem tailTrace_6752221 : CollatzResearch.WordTrace tailWord_6752221 prefixEnd_6752221 3467134858382331637984607 := by
  unfold tailWord_6752221
  simp only [CollatzResearch.WordTrace]
  refine ⟨246273732070863979381960517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164182488047242652921307011 246273732070863979381960517)
  ·
    refine ⟨46176324763286996134117597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 246273732070863979381960517 46176324763286996134117597)
    ·
      refine ⟨17316121786232623550294099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46176324763286996134117597 17316121786232623550294099)
      ·
        refine ⟨25974182679348935325441149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17316121786232623550294099 25974182679348935325441149)
        ·
          refine ⟨9740318504755850747040431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25974182679348935325441149 9740318504755850747040431)
          ·
            refine ⟨14610477757133776120560647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9740318504755850747040431 14610477757133776120560647)
            ·
              refine ⟨21915716635700664180840971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14610477757133776120560647 21915716635700664180840971)
              ·
                refine ⟨32873574953550996271261457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21915716635700664180840971 32873574953550996271261457)
                ·
                  refine ⟨24655181215163247203446093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32873574953550996271261457 24655181215163247203446093)
                  ·
                    refine ⟨9245692955686217701292285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24655181215163247203446093 9245692955686217701292285)
                    ·
                      refine ⟨3467134858382331637984607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9245692955686217701292285 3467134858382331637984607)
                      ·
                        rfl

theorem cell23_6752221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 1, 2, 3, 3].length) (baseStart_6752221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6752221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6752221 prefixEnd_6752221 := by exact prefixLift 6752221
  have htrace : WordTrace (prefixWord ++ tailWord_6752221) baseStart_6752221 baseEnd_6752221 := by
    simpa [prefixWord, tailWord_6752221, baseEnd_6752221] using wordTrace_append hprefix tailTrace_6752221
  have hstable : (prefixWord ++ tailWord_6752221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6752221).length < 2 ^ (prefixWord ++ tailWord_6752221).sum := by decide
  have hdescent : baseEnd_6752221 < baseStart_6752221 := by decide
  rcases family_descends (prefixWord ++ tailWord_6752221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6752241 : List Nat := [1, 2, 2, 2, 5, 2, 1, 1, 2, 5]
def baseStart_6752241 : Nat := 118140960795 + 6752241 * 2 ^ 59
def prefixEnd_6752241 : Nat := 4983230072969 + 3 ^ 40 * 6752241 * 2
def baseEnd_6752241 : Nat := 1155715042665140519911505

theorem tailTrace_6752241 : CollatzResearch.WordTrace tailWord_6752241 prefixEnd_6752241 1155715042665140519911505 := by
  unfold tailWord_6752241
  simp only [CollatzResearch.WordTrace]
  refine ⟨246274461530791522797688577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164182974353861015198459051 246274461530791522797688577)
  ·
    refine ⟨184705846148093642098266433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246274461530791522797688577 184705846148093642098266433)
    ·
      refine ⟨138529384611070231573699825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184705846148093642098266433 138529384611070231573699825)
      ·
        refine ⟨103897038458302673680274869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138529384611070231573699825 103897038458302673680274869)
        ·
          refine ⟨9740347355465875657525769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 103897038458302673680274869 9740347355465875657525769)
          ·
            refine ⟨7305260516599406743144327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9740347355465875657525769 7305260516599406743144327)
            ·
              refine ⟨10957890774899110114716491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7305260516599406743144327 10957890774899110114716491)
              ·
                refine ⟨16436836162348665172074737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10957890774899110114716491 16436836162348665172074737)
                ·
                  refine ⟨12327627121761498879056053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16436836162348665172074737 12327627121761498879056053)
                  ·
                    refine ⟨1155715042665140519911505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12327627121761498879056053 1155715042665140519911505)
                    ·
                      rfl

theorem cell23_6752241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 1, 2, 5].length) (baseStart_6752241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6752241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6752241 prefixEnd_6752241 := by exact prefixLift 6752241
  have htrace : WordTrace (prefixWord ++ tailWord_6752241) baseStart_6752241 baseEnd_6752241 := by
    simpa [prefixWord, tailWord_6752241, baseEnd_6752241] using wordTrace_append hprefix tailTrace_6752241
  have hstable : (prefixWord ++ tailWord_6752241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6752241).length < 2 ^ (prefixWord ++ tailWord_6752241).sum := by decide
  have hdescent : baseEnd_6752241 < baseStart_6752241 := by decide
  rcases family_descends (prefixWord ++ tailWord_6752241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6752257 : List Nat := [1, 2, 4, 1, 2, 1, 1, 1, 1, 3, 6]
def baseStart_6752257 : Nat := 118140960795 + 6752257 * 2 ^ 59
def prefixEnd_6752257 : Nat := 4983230072969 + 3 ^ 40 * 6752257 * 2
def baseEnd_6752257 : Nat := 3467153343685893497134441

theorem tailTrace_6752257 : CollatzResearch.WordTrace tailWord_6752257 prefixEnd_6752257 3467153343685893497134441 := by
  unfold tailWord_6752257
  simp only [CollatzResearch.WordTrace]
  refine ⟨246275045098733557530271025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164183363399155705020180683 246275045098733557530271025)
  ·
    refine ⟨184706283824050168147703269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246275045098733557530271025 184706283824050168147703269)
    ·
      refine ⟨34632428217009406527694363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 184706283824050168147703269 34632428217009406527694363)
      ·
        refine ⟨51948642325514109791541545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34632428217009406527694363 51948642325514109791541545)
        ·
          refine ⟨38961481744135582343656159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51948642325514109791541545 38961481744135582343656159)
          ·
            refine ⟨58442222616203373515484239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38961481744135582343656159 58442222616203373515484239)
            ·
              refine ⟨87663333924305060273226359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58442222616203373515484239 87663333924305060273226359)
              ·
                refine ⟨131495000886457590409839539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87663333924305060273226359 131495000886457590409839539)
                ·
                  refine ⟨197242501329686385614759309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 131495000886457590409839539 197242501329686385614759309)
                  ·
                    refine ⟨73965937998632394605534741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 197242501329686385614759309 73965937998632394605534741)
                    ·
                      refine ⟨3467153343685893497134441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73965937998632394605534741 3467153343685893497134441)
                      ·
                        rfl

theorem cell23_6752257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_6752257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6752257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6752257 prefixEnd_6752257 := by exact prefixLift 6752257
  have htrace : WordTrace (prefixWord ++ tailWord_6752257) baseStart_6752257 baseEnd_6752257 := by
    simpa [prefixWord, tailWord_6752257, baseEnd_6752257] using wordTrace_append hprefix tailTrace_6752257
  have hstable : (prefixWord ++ tailWord_6752257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6752257).length < 2 ^ (prefixWord ++ tailWord_6752257).sum := by decide
  have hdescent : baseEnd_6752257 < baseStart_6752257 := by decide
  rcases family_descends (prefixWord ++ tailWord_6752257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6752264 : List Nat := [2, 1, 3, 2, 1, 2, 2, 1, 4, 2, 3]
def baseStart_6752264 : Nat := 118140960795 + 6752264 * 2 ^ 59
def prefixEnd_6752264 : Nat := 4983230072969 + 3 ^ 40 * 6752264 * 2
def baseEnd_6752264 : Nat := 3467156938050474969746909

theorem tailTrace_6752264 : CollatzResearch.WordTrace tailWord_6752264 prefixEnd_6752264 3467156938050474969746909 := by
  unfold tailWord_6752264
  simp only [CollatzResearch.WordTrace]
  refine ⟨123137650204854098862887923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164183533606472131817183897 123137650204854098862887923)
  ·
    refine ⟨184706475307281148294331885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123137650204854098862887923 184706475307281148294331885)
    ·
      refine ⟨69264928240230430610374457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184706475307281148294331885 69264928240230430610374457)
      ·
        refine ⟨51948696180172822957780843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69264928240230430610374457 51948696180172822957780843)
        ·
          refine ⟨77923044270259234436671265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51948696180172822957780843 77923044270259234436671265)
          ·
            refine ⟨58442283202694425827503449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77923044270259234436671265 58442283202694425827503449)
            ·
              refine ⟨43831712402020819370627587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58442283202694425827503449 43831712402020819370627587)
              ·
                refine ⟨65747568603031229055941381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43831712402020819370627587 65747568603031229055941381)
                ·
                  refine ⟨12327669113068355447989009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65747568603031229055941381 12327669113068355447989009)
                  ·
                    refine ⟨9245751834801266585991757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12327669113068355447989009 9245751834801266585991757)
                    ·
                      refine ⟨3467156938050474969746909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9245751834801266585991757 3467156938050474969746909)
                      ·
                        rfl

theorem cell23_6752264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 1, 4, 2, 3].length) (baseStart_6752264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6752264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6752264 prefixEnd_6752264 := by exact prefixLift 6752264
  have htrace : WordTrace (prefixWord ++ tailWord_6752264) baseStart_6752264 baseEnd_6752264 := by
    simpa [prefixWord, tailWord_6752264, baseEnd_6752264] using wordTrace_append hprefix tailTrace_6752264
  have hstable : (prefixWord ++ tailWord_6752264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6752264).length < 2 ^ (prefixWord ++ tailWord_6752264).sum := by decide
  have hdescent : baseEnd_6752264 < baseStart_6752264 := by decide
  rcases family_descends (prefixWord ++ tailWord_6752264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6752267 : List Nat := [1, 1, 1, 1, 6, 1, 3, 1, 8]
def baseStart_6752267 : Nat := 118140960795 + 6752267 * 2 ^ 59
def prefixEnd_6752267 : Nat := 4983230072969 + 3 ^ 40 * 6752267 * 2
def baseEnd_6752267 : Nat := 385239830943604273112155

theorem tailTrace_6752267 : CollatzResearch.WordTrace tailWord_6752267 prefixEnd_6752267 385239830943604273112155 := by
  unfold tailWord_6752267
  simp only [CollatzResearch.WordTrace]
  refine ⟨246275409828697329238135055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164183606552464886158756703 246275409828697329238135055)
  ·
    refine ⟨369413114743045993857202583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246275409828697329238135055 369413114743045993857202583)
    ·
      refine ⟨554119672114568990785803875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369413114743045993857202583 554119672114568990785803875)
      ·
        refine ⟨831179508171853486178705813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 554119672114568990785803875 831179508171853486178705813)
        ·
          refine ⟨38961539445555632164626835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 831179508171853486178705813 38961539445555632164626835)
          ·
            refine ⟨58442309168333448246940253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38961539445555632164626835 58442309168333448246940253)
            ·
              refine ⟨21915865938125043092602595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58442309168333448246940253 21915865938125043092602595)
              ·
                refine ⟨32873798907187564638903893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21915865938125043092602595 32873798907187564638903893)
                ·
                  refine ⟨385239830943604273112155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32873798907187564638903893 385239830943604273112155)
                  ·
                    rfl

theorem cell23_6752267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 1, 8].length) (baseStart_6752267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6752267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6752267 prefixEnd_6752267 := by exact prefixLift 6752267
  have htrace : WordTrace (prefixWord ++ tailWord_6752267) baseStart_6752267 baseEnd_6752267 := by
    simpa [prefixWord, tailWord_6752267, baseEnd_6752267] using wordTrace_append hprefix tailTrace_6752267
  have hstable : (prefixWord ++ tailWord_6752267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6752267).length < 2 ^ (prefixWord ++ tailWord_6752267).sum := by decide
  have hdescent : baseEnd_6752267 < baseStart_6752267 := by decide
  rcases family_descends (prefixWord ++ tailWord_6752267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6752287 : List Nat := [1, 1, 2, 4, 1, 2, 1, 2, 1, 2, 6]
def baseStart_6752287 : Nat := 118140960795 + 6752287 * 2 ^ 59
def prefixEnd_6752287 : Nat := 4983230072969 + 3 ^ 40 * 6752287 * 2
def baseEnd_6752287 : Nat := 3467168748105528379759303

theorem tailTrace_6752287 : CollatzResearch.WordTrace tailWord_6752287 prefixEnd_6752287 3467168748105528379759303 := by
  unfold tailWord_6752287
  simp only [CollatzResearch.WordTrace]
  refine ⟨246276139288624872653863115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164184092859083248435908743 246276139288624872653863115)
  ·
    refine ⟨369414208932937308980794673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246276139288624872653863115 369414208932937308980794673)
    ·
      refine ⟨277060656699702981735596005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 369414208932937308980794673 277060656699702981735596005)
      ·
        refine ⟨51948873131194309075424251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 277060656699702981735596005 51948873131194309075424251)
        ·
          refine ⟨77923309696791463613136377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51948873131194309075424251 77923309696791463613136377)
          ·
            refine ⟨58442482272593597709852283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77923309696791463613136377 58442482272593597709852283)
            ·
              refine ⟨87663723408890396564778425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58442482272593597709852283 87663723408890396564778425)
              ·
                refine ⟨65747792556667797423583819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87663723408890396564778425 65747792556667797423583819)
                ·
                  refine ⟨98621688835001696135375729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65747792556667797423583819 98621688835001696135375729)
                  ·
                    refine ⟨73966266626251272101531797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 98621688835001696135375729 73966266626251272101531797)
                    ·
                      refine ⟨3467168748105528379759303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73966266626251272101531797 3467168748105528379759303)
                      ·
                        rfl

theorem cell23_6752287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_6752287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6752287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6752287 prefixEnd_6752287 := by exact prefixLift 6752287
  have htrace : WordTrace (prefixWord ++ tailWord_6752287) baseStart_6752287 baseEnd_6752287 := by
    simpa [prefixWord, tailWord_6752287, baseEnd_6752287] using wordTrace_append hprefix tailTrace_6752287
  have hstable : (prefixWord ++ tailWord_6752287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6752287).length < 2 ^ (prefixWord ++ tailWord_6752287).sum := by decide
  have hdescent : baseEnd_6752287 < baseStart_6752287 := by decide
  rcases family_descends (prefixWord ++ tailWord_6752287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6752297 : List Nat := [1, 2, 1, 1, 1, 1, 1, 1, 9, 5]
def baseStart_6752297 : Nat := 118140960795 + 6752297 * 2 ^ 59
def prefixEnd_6752297 : Nat := 4983230072969 + 3 ^ 40 * 6752297 * 2
def baseEnd_6752297 : Nat := 1155724627637357780211419

theorem tailTrace_6752297 : CollatzResearch.WordTrace tailWord_6752297 prefixEnd_6752297 1155724627637357780211419 := by
  unfold tailWord_6752297
  simp only [CollatzResearch.WordTrace]
  refine ⟨246276504018588644361727145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164184336012392429574484763 246276504018588644361727145)
  ·
    refine ⟨184707378013941483271295359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246276504018588644361727145 184707378013941483271295359)
    ·
      refine ⟨277061067020912224906943039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184707378013941483271295359 277061067020912224906943039)
      ·
        refine ⟨415591600531368337360414559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277061067020912224906943039 415591600531368337360414559)
        ·
          refine ⟨623387400797052506040621839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 415591600531368337360414559 623387400797052506040621839)
          ·
            refine ⟨935081101195578759060932759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 623387400797052506040621839 935081101195578759060932759)
            ·
              refine ⟨1402621651793368138591399139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 935081101195578759060932759 1402621651793368138591399139)
              ·
                refine ⟨2103932477690052207887098709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1402621651793368138591399139 2103932477690052207887098709)
                ·
                  refine ⟨12327729361465149655588469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 2103932477690052207887098709 12327729361465149655588469)
                  ·
                    refine ⟨1155724627637357780211419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12327729361465149655588469 1155724627637357780211419)
                    ·
                      rfl

theorem cell23_6752297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 9, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 9, 5].length) (baseStart_6752297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6752297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6752297 prefixEnd_6752297 := by exact prefixLift 6752297
  have htrace : WordTrace (prefixWord ++ tailWord_6752297) baseStart_6752297 baseEnd_6752297 := by
    simpa [prefixWord, tailWord_6752297, baseEnd_6752297] using wordTrace_append hprefix tailTrace_6752297
  have hstable : (prefixWord ++ tailWord_6752297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6752297).length < 2 ^ (prefixWord ++ tailWord_6752297).sum := by decide
  have hdescent : baseEnd_6752297 < baseStart_6752297 := by decide
  rcases family_descends (prefixWord ++ tailWord_6752297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6752348 : List Nat := [2, 2, 4, 1, 1, 4, 1, 2, 1, 5]
def baseStart_6752348 : Nat := 118140960795 + 6752348 * 2 ^ 59
def prefixEnd_6752348 : Nat := 4983230072969 + 3 ^ 40 * 6752348 * 2
def baseEnd_6752348 : Nat := 1155733356808484213698841

theorem tailTrace_6752348 : CollatzResearch.WordTrace tailWord_6752348 prefixEnd_6752348 1155733356808484213698841 := by
  unfold tailWord_6752348
  simp only [CollatzResearch.WordTrace]
  refine ⟨123139182070701940035916849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164185576094269253381222465 123139182070701940035916849)
  ·
    refine ⟨92354386553026455026937637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123139182070701940035916849 92354386553026455026937637)
    ·
      refine ⟨17316447478692460317550807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92354386553026455026937637 17316447478692460317550807)
      ·
        refine ⟨25974671218038690476326211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17316447478692460317550807 25974671218038690476326211)
        ·
          refine ⟨38962006827058035714489317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25974671218038690476326211 38962006827058035714489317)
          ·
            refine ⟨7305376280073381696466747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38962006827058035714489317 7305376280073381696466747)
            ·
              refine ⟨10958064420110072544700121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7305376280073381696466747 10958064420110072544700121)
              ·
                refine ⟨8218548315082554408525091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10958064420110072544700121 8218548315082554408525091)
                ·
                  refine ⟨12327822472623831612787637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8218548315082554408525091 12327822472623831612787637)
                  ·
                    refine ⟨1155733356808484213698841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12327822472623831612787637 1155733356808484213698841)
                    ·
                      rfl

theorem cell23_6752348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 2, 1, 5].length) (baseStart_6752348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6752348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6752348 prefixEnd_6752348 := by exact prefixLift 6752348
  have htrace : WordTrace (prefixWord ++ tailWord_6752348) baseStart_6752348 baseEnd_6752348 := by
    simpa [prefixWord, tailWord_6752348, baseEnd_6752348] using wordTrace_append hprefix tailTrace_6752348
  have hstable : (prefixWord ++ tailWord_6752348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6752348).length < 2 ^ (prefixWord ++ tailWord_6752348).sum := by decide
  have hdescent : baseEnd_6752348 < baseStart_6752348 := by decide
  rcases family_descends (prefixWord ++ tailWord_6752348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6752364 : List Nat := [2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 4]
def baseStart_6752364 : Nat := 118140960795 + 6752364 * 2 ^ 59
def prefixEnd_6752364 : Nat := 4983230072969 + 3 ^ 40 * 6752364 * 2
def baseEnd_6752364 : Nat := 3467208286115924578496449

theorem tailTrace_6752364 : CollatzResearch.WordTrace tailWord_6752364 prefixEnd_6752364 3467208286115924578496449 := by
  unfold tailWord_6752364
  simp only [CollatzResearch.WordTrace]
  refine ⟨123139473854672957402208073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164185965139563943202944097 123139473854672957402208073)
  ·
    refine ⟨92354605391004718051656055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123139473854672957402208073 92354605391004718051656055)
    ·
      refine ⟨138531908086507077077484083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92354605391004718051656055 138531908086507077077484083)
      ·
        refine ⟨207797862129760615616226125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138531908086507077077484083 207797862129760615616226125)
        ·
          refine ⟨77924198298660230856084797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 207797862129760615616226125 77924198298660230856084797)
          ·
            refine ⟨29221574361997586571031799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77924198298660230856084797 29221574361997586571031799)
            ·
              refine ⟨43832361542996379856547699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29221574361997586571031799 43832361542996379856547699)
              ·
                refine ⟨65748542314494569784821549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43832361542996379856547699 65748542314494569784821549)
                ·
                  refine ⟨24655703367935463669308081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65748542314494569784821549 24655703367935463669308081)
                  ·
                    refine ⟨18491777525951597751981061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24655703367935463669308081 18491777525951597751981061)
                    ·
                      refine ⟨3467208286115924578496449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18491777525951597751981061 3467208286115924578496449)
                      ·
                        rfl

theorem cell23_6752364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 4].length) (baseStart_6752364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6752364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6752364 prefixEnd_6752364 := by exact prefixLift 6752364
  have htrace : WordTrace (prefixWord ++ tailWord_6752364) baseStart_6752364 baseEnd_6752364 := by
    simpa [prefixWord, tailWord_6752364, baseEnd_6752364] using wordTrace_append hprefix tailTrace_6752364
  have hstable : (prefixWord ++ tailWord_6752364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6752364).length < 2 ^ (prefixWord ++ tailWord_6752364).sum := by decide
  have hdescent : baseEnd_6752364 < baseStart_6752364 := by decide
  rcases family_descends (prefixWord ++ tailWord_6752364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6752368 : List Nat := [2, 1, 1, 1, 5, 3, 3, 1, 1, 1, 4]
def baseStart_6752368 : Nat := 118140960795 + 6752368 * 2 ^ 59
def prefixEnd_6752368 : Nat := 4983230072969 + 3 ^ 40 * 6752368 * 2
def baseEnd_6752368 : Nat := 3467210340038542562846431

theorem tailTrace_6752368 : CollatzResearch.WordTrace tailWord_6752368 prefixEnd_6752368 3467210340038542562846431 := by
  unfold tailWord_6752368
  simp only [CollatzResearch.WordTrace]
  refine ⟨123139546800665711743780879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164186062400887615658374505 123139546800665711743780879)
  ·
    refine ⟨184709320200998567615671319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123139546800665711743780879 184709320200998567615671319)
    ·
      refine ⟨277063980301497851423506979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184709320200998567615671319 277063980301497851423506979)
      ·
        refine ⟨415595970452246777135260469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277063980301497851423506979 415595970452246777135260469)
        ·
          refine ⟨38962122229898135356430669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 415595970452246777135260469 38962122229898135356430669)
          ·
            refine ⟨14610795836211800758661501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38962122229898135356430669 14610795836211800758661501)
            ·
              refine ⟨5479048438579425284498063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14610795836211800758661501 5479048438579425284498063)
              ·
                refine ⟨8218572657869137926747095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5479048438579425284498063 8218572657869137926747095)
                ·
                  refine ⟨12327858986803706890120643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8218572657869137926747095 12327858986803706890120643)
                  ·
                    refine ⟨18491788480205560335180965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12327858986803706890120643 18491788480205560335180965)
                    ·
                      refine ⟨3467210340038542562846431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18491788480205560335180965 3467210340038542562846431)
                      ·
                        rfl

theorem cell23_6752368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 3, 1, 1, 1, 4].length) (baseStart_6752368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6752368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6752368 prefixEnd_6752368 := by exact prefixLift 6752368
  have htrace : WordTrace (prefixWord ++ tailWord_6752368) baseStart_6752368 baseEnd_6752368 := by
    simpa [prefixWord, tailWord_6752368, baseEnd_6752368] using wordTrace_append hprefix tailTrace_6752368
  have hstable : (prefixWord ++ tailWord_6752368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6752368).length < 2 ^ (prefixWord ++ tailWord_6752368).sum := by decide
  have hdescent : baseEnd_6752368 < baseStart_6752368 := by decide
  rcases family_descends (prefixWord ++ tailWord_6752368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6752374 : List Nat := [5, 1, 1, 2, 1, 13]
def baseStart_6752374 : Nat := 118140960795 + 6752374 * 2 ^ 59
def prefixEnd_6752374 : Nat := 4983230072969 + 3 ^ 40 * 6752374 * 2
def baseEnd_6752374 : Nat := 14268367987335265594121

theorem tailTrace_6752374 : CollatzResearch.WordTrace tailWord_6752374 prefixEnd_6752374 14268367987335265594121 := by
  unfold tailWord_6752374
  simp only [CollatzResearch.WordTrace]
  refine ⟨15392457027456855407017511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 164186208292873124341520117 15392457027456855407017511)
  ·
    refine ⟨23088685541185283110526267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15392457027456855407017511 23088685541185283110526267)
    ·
      refine ⟨34633028311777924665789401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23088685541185283110526267 34633028311777924665789401)
      ·
        refine ⟨25974771233833443499342051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34633028311777924665789401 25974771233833443499342051)
        ·
          refine ⟨38962156850750165249013077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25974771233833443499342051 38962156850750165249013077)
          ·
            refine ⟨14268367987335265594121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 38962156850750165249013077 14268367987335265594121)
            ·
              rfl

theorem cell23_6752374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 13].length) (baseStart_6752374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6752374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6752374 prefixEnd_6752374 := by exact prefixLift 6752374
  have htrace : WordTrace (prefixWord ++ tailWord_6752374) baseStart_6752374 baseEnd_6752374 := by
    simpa [prefixWord, tailWord_6752374, baseEnd_6752374] using wordTrace_append hprefix tailTrace_6752374
  have hstable : (prefixWord ++ tailWord_6752374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6752374).length < 2 ^ (prefixWord ++ tailWord_6752374).sum := by decide
  have hdescent : baseEnd_6752374 < baseStart_6752374 := by decide
  rcases family_descends (prefixWord ++ tailWord_6752374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6752384 : List Nat := [2, 1, 1, 2, 1, 3, 1, 1, 5, 3, 3]
def baseStart_6752384 : Nat := 118140960795 + 6752384 * 2 ^ 59
def prefixEnd_6752384 : Nat := 4983230072969 + 3 ^ 40 * 6752384 * 2
def baseEnd_6752384 : Nat := 3467218555729014500246357

theorem tailTrace_6752384 : CollatzResearch.WordTrace tailWord_6752384 prefixEnd_6752384 3467218555729014500246357 := by
  unfold tailWord_6752384
  simp only [CollatzResearch.WordTrace]
  refine ⟨123139838584636729110072103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164186451446182305480096137 123139838584636729110072103)
  ·
    refine ⟨184709757876955093665108155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123139838584636729110072103 184709757876955093665108155)
    ·
      refine ⟨277064636815432640497662233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184709757876955093665108155 277064636815432640497662233)
      ·
        refine ⟨207798477611574480373246675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 277064636815432640497662233 207798477611574480373246675)
        ·
          refine ⟨311697716417361720559870013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207798477611574480373246675 311697716417361720559870013)
          ·
            refine ⟨116886643656510645209951255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 311697716417361720559870013 116886643656510645209951255)
            ·
              refine ⟨175329965484765967814926883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116886643656510645209951255 175329965484765967814926883)
              ·
                refine ⟨262994948227148951722390325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 175329965484765967814926883 262994948227148951722390325)
                ·
                  refine ⟨24655776396295214223974093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 262994948227148951722390325 24655776396295214223974093)
                  ·
                    refine ⟨9245916148610705333990285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24655776396295214223974093 9245916148610705333990285)
                    ·
                      refine ⟨3467218555729014500246357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9245916148610705333990285 3467218555729014500246357)
                      ·
                        rfl

theorem cell23_6752384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 5, 3, 3].length) (baseStart_6752384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6752384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6752384 prefixEnd_6752384 := by exact prefixLift 6752384
  have htrace : WordTrace (prefixWord ++ tailWord_6752384) baseStart_6752384 baseEnd_6752384 := by
    simpa [prefixWord, tailWord_6752384, baseEnd_6752384] using wordTrace_append hprefix tailTrace_6752384
  have hstable : (prefixWord ++ tailWord_6752384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6752384).length < 2 ^ (prefixWord ++ tailWord_6752384).sum := by decide
  have hdescent : baseEnd_6752384 < baseStart_6752384 := by decide
  rcases family_descends (prefixWord ++ tailWord_6752384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6752398 : List Nat := [4, 1, 1, 3, 3, 1, 2, 1, 1, 2, 4]
def baseStart_6752398 : Nat := 118140960795 + 6752398 * 2 ^ 59
def prefixEnd_6752398 : Nat := 4983230072969 + 3 ^ 40 * 6752398 * 2
def baseEnd_6752398 : Nat := 3467225744458177445471293

theorem tailTrace_6752398 : CollatzResearch.WordTrace tailWord_6752398 prefixEnd_6752398 3467225744458177445471293 := by
  unfold tailWord_6752398
  simp only [CollatzResearch.WordTrace]
  refine ⟨30785023473902842326394231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164186791860815159074102565 30785023473902842326394231)
  ·
    refine ⟨46177535210854263489591347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30785023473902842326394231 46177535210854263489591347)
    ·
      refine ⟨69266302816281395234387021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46177535210854263489591347 69266302816281395234387021)
      ·
        refine ⟨25974863556105523212895133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69266302816281395234387021 25974863556105523212895133)
        ·
          refine ⟨9740573833539571204835675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25974863556105523212895133 9740573833539571204835675)
          ·
            refine ⟨14610860750309356807253513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9740573833539571204835675 14610860750309356807253513)
            ·
              refine ⟨10958145562732017605440135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14610860750309356807253513 10958145562732017605440135)
              ·
                refine ⟨16437218344098026408160203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10958145562732017605440135 16437218344098026408160203)
                ·
                  refine ⟨24655827516147039612240305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16437218344098026408160203 24655827516147039612240305)
                  ·
                    refine ⟨18491870637110279709180229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24655827516147039612240305 18491870637110279709180229)
                    ·
                      refine ⟨3467225744458177445471293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18491870637110279709180229 3467225744458177445471293)
                      ·
                        rfl

theorem cell23_6752398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 1, 1, 2, 4].length) (baseStart_6752398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6752398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6752398 prefixEnd_6752398 := by exact prefixLift 6752398
  have htrace : WordTrace (prefixWord ++ tailWord_6752398) baseStart_6752398 baseEnd_6752398 := by
    simpa [prefixWord, tailWord_6752398, baseEnd_6752398] using wordTrace_append hprefix tailTrace_6752398
  have hstable : (prefixWord ++ tailWord_6752398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6752398).length < 2 ^ (prefixWord ++ tailWord_6752398).sum := by decide
  have hdescent : baseEnd_6752398 < baseStart_6752398 := by decide
  rcases family_descends (prefixWord ++ tailWord_6752398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6752411 : List Nat := [1, 1, 1, 1, 1, 1, 2, 7, 3, 3, 2]
def baseStart_6752411 : Nat := 118140960795 + 6752411 * 2 ^ 59
def prefixEnd_6752411 : Nat := 4983230072969 + 3 ^ 40 * 6752411 * 2
def baseEnd_6752411 : Nat := 3467232419706685894608733

theorem tailTrace_6752411 : CollatzResearch.WordTrace tailWord_6752411 prefixEnd_6752411 3467232419706685894608733 := by
  unfold tailWord_6752411
  simp only [CollatzResearch.WordTrace]
  refine ⟨246280661940175641831377087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164187107960117094554251391 246280661940175641831377087)
  ·
    refine ⟨369420992910263462747065631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246280661940175641831377087 369420992910263462747065631)
    ·
      refine ⟨554131489365395194120598447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369420992910263462747065631 554131489365395194120598447)
      ·
        refine ⟨831197234048092791180897671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 554131489365395194120598447 831197234048092791180897671)
        ·
          refine ⟨1246795851072139186771346507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 831197234048092791180897671 1246795851072139186771346507)
          ·
            refine ⟨1870193776608208780157019761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1246795851072139186771346507 1870193776608208780157019761)
            ·
              refine ⟨1402645332456156585117764821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1870193776608208780157019761 1402645332456156585117764821)
              ·
                refine ⟨32874499979441169963697613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1402645332456156585117764821 32874499979441169963697613)
                ·
                  refine ⟨12327937492290438736386605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32874499979441169963697613 12327937492290438736386605)
                  ·
                    refine ⟨4622976559608914526144977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12327937492290438736386605 4622976559608914526144977)
                    ·
                      refine ⟨3467232419706685894608733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4622976559608914526144977 3467232419706685894608733)
                      ·
                        rfl

theorem cell23_6752411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 7, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 7, 3, 3, 2].length) (baseStart_6752411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6752411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6752411 prefixEnd_6752411 := by exact prefixLift 6752411
  have htrace : WordTrace (prefixWord ++ tailWord_6752411) baseStart_6752411 baseEnd_6752411 := by
    simpa [prefixWord, tailWord_6752411, baseEnd_6752411] using wordTrace_append hprefix tailTrace_6752411
  have hstable : (prefixWord ++ tailWord_6752411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6752411).length < 2 ^ (prefixWord ++ tailWord_6752411).sum := by decide
  have hdescent : baseEnd_6752411 < baseStart_6752411 := by decide
  rcases family_descends (prefixWord ++ tailWord_6752411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6752418 : List Nat := [3, 3, 1, 3, 1, 1, 2, 2, 1, 3, 3]
def baseStart_6752418 : Nat := 118140960795 + 6752418 * 2 ^ 59
def prefixEnd_6752418 : Nat := 4983230072969 + 3 ^ 40 * 6752418 * 2
def baseEnd_6752418 : Nat := 3467236014071267367221201

theorem tailTrace_6752418 : CollatzResearch.WordTrace tailWord_6752418 prefixEnd_6752418 3467236014071267367221201 := by
  unfold tailWord_6752418
  simp only [CollatzResearch.WordTrace]
  refine ⟨61570229312787570506720477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164187278167433521351254605 61570229312787570506720477)
  ·
    refine ⟨23088835992295338940020179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61570229312787570506720477 23088835992295338940020179)
    ·
      refine ⟨34633253988443008410030269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23088835992295338940020179 34633253988443008410030269)
      ·
        refine ⟨12987470245666128153761351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34633253988443008410030269 12987470245666128153761351)
        ·
          refine ⟨19481205368499192230642027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12987470245666128153761351 19481205368499192230642027)
          ·
            refine ⟨29221808052748788345963041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19481205368499192230642027 29221808052748788345963041)
            ·
              refine ⟨21916356039561591259472281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29221808052748788345963041 21916356039561591259472281)
              ·
                refine ⟨16437267029671193444604211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21916356039561591259472281 16437267029671193444604211)
                ·
                  refine ⟨24655900544506790166906317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16437267029671193444604211 24655900544506790166906317)
                  ·
                    refine ⟨9245962704190046312589869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24655900544506790166906317 9245962704190046312589869)
                    ·
                      refine ⟨3467236014071267367221201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9245962704190046312589869 3467236014071267367221201)
                      ·
                        rfl

theorem cell23_6752418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_6752418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6752418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6752418 prefixEnd_6752418 := by exact prefixLift 6752418
  have htrace : WordTrace (prefixWord ++ tailWord_6752418) baseStart_6752418 baseEnd_6752418 := by
    simpa [prefixWord, tailWord_6752418, baseEnd_6752418] using wordTrace_append hprefix tailTrace_6752418
  have hstable : (prefixWord ++ tailWord_6752418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6752418).length < 2 ^ (prefixWord ++ tailWord_6752418).sum := by decide
  have hdescent : baseEnd_6752418 < baseStart_6752418 := by decide
  rcases family_descends (prefixWord ++ tailWord_6752418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6752434 : List Nat := [3, 2, 1, 1, 1, 3, 1, 1, 4, 6]
def baseStart_6752434 : Nat := 118140960795 + 6752434 * 2 ^ 59
def prefixEnd_6752434 : Nat := 4983230072969 + 3 ^ 40 * 6752434 * 2
def baseEnd_6752434 : Nat := 1155748076587246434873709

theorem tailTrace_6752434 : CollatzResearch.WordTrace tailWord_6752434 prefixEnd_6752434 1155748076587246434873709 := by
  unfold tailWord_6752434
  simp only [CollatzResearch.WordTrace]
  refine ⟨61570375204773079189866089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164187667212728211172976237 61570375204773079189866089)
  ·
    refine ⟨46177781403579809392399567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61570375204773079189866089 46177781403579809392399567)
    ·
      refine ⟨69266672105369714088599351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46177781403579809392399567 69266672105369714088599351)
      ·
        refine ⟨103900008158054571132899027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69266672105369714088599351 103900008158054571132899027)
        ·
          refine ⟨155850012237081856699348541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103900008158054571132899027 155850012237081856699348541)
          ·
            refine ⟨58443754588905696262255703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 155850012237081856699348541 58443754588905696262255703)
            ·
              refine ⟨87665631883358544393383555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58443754588905696262255703 87665631883358544393383555)
              ·
                refine ⟨131498447825037816590075333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87665631883358544393383555 131498447825037816590075333)
                ·
                  refine ⟨24655958967194590610639125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 131498447825037816590075333 24655958967194590610639125)
                  ·
                    refine ⟨1155748076587246434873709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24655958967194590610639125 1155748076587246434873709)
                    ·
                      rfl

theorem cell23_6752434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 4, 6].length) (baseStart_6752434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6752434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6752434 prefixEnd_6752434 := by exact prefixLift 6752434
  have htrace : WordTrace (prefixWord ++ tailWord_6752434) baseStart_6752434 baseEnd_6752434 := by
    simpa [prefixWord, tailWord_6752434, baseEnd_6752434] using wordTrace_append hprefix tailTrace_6752434
  have hstable : (prefixWord ++ tailWord_6752434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6752434).length < 2 ^ (prefixWord ++ tailWord_6752434).sum := by decide
  have hdescent : baseEnd_6752434 < baseStart_6752434 := by decide
  rcases family_descends (prefixWord ++ tailWord_6752434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6752436 : List Nat := [2, 5, 3, 1, 1, 1, 2, 1, 3, 2, 2]
def baseStart_6752436 : Nat := 118140960795 + 6752436 * 2 ^ 59
def prefixEnd_6752436 : Nat := 4983230072969 + 3 ^ 40 * 6752436 * 2
def baseEnd_6752436 : Nat := 3467245256723048296796119

theorem tailTrace_6752436 : CollatzResearch.WordTrace tailWord_6752436 prefixEnd_6752436 3467245256723048296796119 := by
  unfold tailWord_6752436
  simp only [CollatzResearch.WordTrace]
  refine ⟨123140786882542535550518581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164187715843390047400691441 123140786882542535550518581)
  ·
    refine ⟨11544448770238362707861117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 123140786882542535550518581 11544448770238362707861117)
    ·
      refine ⟨4329168288839386015447919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11544448770238362707861117 4329168288839386015447919)
      ·
        refine ⟨6493752433259079023171879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4329168288839386015447919 6493752433259079023171879)
        ·
          refine ⟨9740628649888618534757819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6493752433259079023171879 9740628649888618534757819)
          ·
            refine ⟨14610942974832927802136729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9740628649888618534757819 14610942974832927802136729)
            ·
              refine ⟨10958207231124695851602547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14610942974832927802136729 10958207231124695851602547)
              ·
                refine ⟨16437310846687043777403821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10958207231124695851602547 16437310846687043777403821)
                ·
                  refine ⟨6163991567507641416526433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16437310846687043777403821 6163991567507641416526433)
                  ·
                    refine ⟨4622993675630731062394825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6163991567507641416526433 4622993675630731062394825)
                    ·
                      refine ⟨3467245256723048296796119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4622993675630731062394825 3467245256723048296796119)
                      ·
                        rfl

theorem cell23_6752436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_6752436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6752436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6752436 prefixEnd_6752436 := by exact prefixLift 6752436
  have htrace : WordTrace (prefixWord ++ tailWord_6752436) baseStart_6752436 baseEnd_6752436 := by
    simpa [prefixWord, tailWord_6752436, baseEnd_6752436] using wordTrace_append hprefix tailTrace_6752436
  have hstable : (prefixWord ++ tailWord_6752436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6752436).length < 2 ^ (prefixWord ++ tailWord_6752436).sum := by decide
  have hdescent : baseEnd_6752436 < baseStart_6752436 := by decide
  rcases family_descends (prefixWord ++ tailWord_6752436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6752452 : List Nat := [2, 3, 3, 1, 2, 2, 3, 1, 2, 1, 3]
def baseStart_6752452 : Nat := 118140960795 + 6752452 * 2 ^ 59
def prefixEnd_6752452 : Nat := 4983230072969 + 3 ^ 40 * 6752452 * 2
def baseEnd_6752452 : Nat := 3467253472413520234196045

theorem tailTrace_6752452 : CollatzResearch.WordTrace tailWord_6752452 prefixEnd_6752452 3467253472413520234196045 := by
  unfold tailWord_6752452
  simp only [CollatzResearch.WordTrace]
  refine ⟨123141078666513552916809805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164188104888684737222413073 123141078666513552916809805)
  ·
    refine ⟨46177904499942582343803677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123141078666513552916809805 46177904499942582343803677)
    ·
      refine ⟨17316714187478468378926379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46177904499942582343803677 17316714187478468378926379)
      ·
        refine ⟨25975071281217702568389569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17316714187478468378926379 25975071281217702568389569)
        ·
          refine ⟨19481303460913276926292177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25975071281217702568389569 19481303460913276926292177)
          ·
            refine ⟨14610977595684957694719133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19481303460913276926292177 14610977595684957694719133)
            ·
              refine ⟨5479116598381859135519675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14610977595684957694719133 5479116598381859135519675)
              ·
                refine ⟨8218674897572788703279513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5479116598381859135519675 8218674897572788703279513)
                ·
                  refine ⟨6164006173179591527459635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8218674897572788703279513 6164006173179591527459635)
                  ·
                    refine ⟨9246009259769387291189453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6164006173179591527459635 9246009259769387291189453)
                    ·
                      refine ⟨3467253472413520234196045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9246009259769387291189453 3467253472413520234196045)
                      ·
                        rfl

theorem cell23_6752452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 3, 1, 2, 1, 3].length) (baseStart_6752452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6752452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6752452 prefixEnd_6752452 := by exact prefixLift 6752452
  have htrace : WordTrace (prefixWord ++ tailWord_6752452) baseStart_6752452 baseEnd_6752452 := by
    simpa [prefixWord, tailWord_6752452, baseEnd_6752452] using wordTrace_append hprefix tailTrace_6752452
  have hstable : (prefixWord ++ tailWord_6752452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6752452).length < 2 ^ (prefixWord ++ tailWord_6752452).sum := by decide
  have hdescent : baseEnd_6752452 < baseStart_6752452 := by decide
  rcases family_descends (prefixWord ++ tailWord_6752452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6752498 : List Nat := [3, 2, 1, 3, 2, 3, 1, 1, 7]
def baseStart_6752498 : Nat := 118140960795 + 6752498 * 2 ^ 59
def prefixEnd_6752498 : Nat := 4983230072969 + 3 ^ 40 * 6752498 * 2
def baseEnd_6752498 : Nat := 385253010280403006024537

theorem tailTrace_6752498 : CollatzResearch.WordTrace tailWord_6752498 prefixEnd_6752498 385253010280403006024537 := by
  unfold tailWord_6752498
  simp only [CollatzResearch.WordTrace]
  refine ⟨61570958772715113922448537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164189223393906970459862765 61570958772715113922448537)
  ·
    refine ⟨46178219079536335441836403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61570958772715113922448537 46178219079536335441836403)
    ·
      refine ⟨69267328619304503162754605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46178219079536335441836403 69267328619304503162754605)
      ·
        refine ⟨25975248232239188686032977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69267328619304503162754605 25975248232239188686032977)
        ·
          refine ⟨19481436174179391514524733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25975248232239188686032977 19481436174179391514524733)
          ·
            refine ⟨7305538565317271817946775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19481436174179391514524733 7305538565317271817946775)
            ·
              refine ⟨10958307847975907726920163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7305538565317271817946775 10958307847975907726920163)
              ·
                refine ⟨16437461771963861590380245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10958307847975907726920163 16437461771963861590380245)
                ·
                  refine ⟨385253010280403006024537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16437461771963861590380245 385253010280403006024537)
                  ·
                    rfl

theorem cell23_6752498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 1, 7].length) (baseStart_6752498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6752498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6752498 prefixEnd_6752498 := by exact prefixLift 6752498
  have htrace : WordTrace (prefixWord ++ tailWord_6752498) baseStart_6752498 baseEnd_6752498 := by
    simpa [prefixWord, tailWord_6752498, baseEnd_6752498] using wordTrace_append hprefix tailTrace_6752498
  have hstable : (prefixWord ++ tailWord_6752498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6752498).length < 2 ^ (prefixWord ++ tailWord_6752498).sum := by decide
  have hdescent : baseEnd_6752498 < baseStart_6752498 := by decide
  rcases family_descends (prefixWord ++ tailWord_6752498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6752548 : List Nat := [2, 3, 1, 3, 1, 2, 2, 2, 2, 1, 4]
def baseStart_6752548 : Nat := 118140960795 + 6752548 * 2 ^ 59
def prefixEnd_6752548 : Nat := 4983230072969 + 3 ^ 40 * 6752548 * 2
def baseEnd_6752548 : Nat := 3467302766556351858595603

theorem tailTrace_6752548 : CollatzResearch.WordTrace tailWord_6752548 prefixEnd_6752548 3467302766556351858595603 := by
  unfold tailWord_6752548
  simp only [CollatzResearch.WordTrace]
  refine ⟨123142829370339657114557149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164190439160452876152742865 123142829370339657114557149)
  ·
    refine ⟨46178561013877371417958931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123142829370339657114557149 46178561013877371417958931)
    ·
      refine ⟨69267841520816057126938397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46178561013877371417958931 69267841520816057126938397)
      ·
        refine ⟨25975440570306021422601899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69267841520816057126938397 25975440570306021422601899)
        ·
          refine ⟨38963160855459032133902849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25975440570306021422601899 38963160855459032133902849)
          ·
            refine ⟨29222370641594274100427137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38963160855459032133902849 29222370641594274100427137)
            ·
              refine ⟨21916777981195705575320353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29222370641594274100427137 21916777981195705575320353)
              ·
                refine ⟨16437583485896779181490265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21916777981195705575320353 16437583485896779181490265)
                ·
                  refine ⟨12328187614422584386117699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16437583485896779181490265 12328187614422584386117699)
                  ·
                    refine ⟨18492281421633876579176549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12328187614422584386117699 18492281421633876579176549)
                    ·
                      refine ⟨3467302766556351858595603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18492281421633876579176549 3467302766556351858595603)
                      ·
                        rfl

theorem cell23_6752548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_6752548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6752548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6752548 prefixEnd_6752548 := by exact prefixLift 6752548
  have htrace : WordTrace (prefixWord ++ tailWord_6752548) baseStart_6752548 baseEnd_6752548 := by
    simpa [prefixWord, tailWord_6752548, baseEnd_6752548] using wordTrace_append hprefix tailTrace_6752548
  have hstable : (prefixWord ++ tailWord_6752548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6752548).length < 2 ^ (prefixWord ++ tailWord_6752548).sum := by decide
  have hdescent : baseEnd_6752548 < baseStart_6752548 := by decide
  rcases family_descends (prefixWord ++ tailWord_6752548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6752615 : List Nat := [1, 1, 5, 1, 3, 1, 1, 3, 3, 1, 3]
def baseStart_6752615 : Nat := 118140960795 + 6752615 * 2 ^ 59
def prefixEnd_6752615 : Nat := 4983230072969 + 3 ^ 40 * 6752615 * 2
def baseEnd_6752615 : Nat := 3467337169760203096457795

theorem tailTrace_6752615 : CollatzResearch.WordTrace tailWord_6752615 prefixEnd_6752615 3467337169760203096457795 := by
  unfold tailWord_6752615
  simp only [CollatzResearch.WordTrace]
  refine ⟨246288102431436584671803299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164192068287624389781202199 246288102431436584671803299)
  ·
    refine ⟨369432153647154877007704949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246288102431436584671803299 369432153647154877007704949)
    ·
      refine ⟨34634264404420769719472339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 369432153647154877007704949 34634264404420769719472339)
      ·
        refine ⟨51951396606631154579208509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34634264404420769719472339 51951396606631154579208509)
        ·
          refine ⟨19481773727486682967203191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51951396606631154579208509 19481773727486682967203191)
          ·
            refine ⟨29222660591230024450804787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19481773727486682967203191 29222660591230024450804787)
            ·
              refine ⟨43833990886845036676207181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29222660591230024450804787 43833990886845036676207181)
              ·
                refine ⟨16437746582566888753577693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43833990886845036676207181 16437746582566888753577693)
                ·
                  refine ⟨6164154968462583282591635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16437746582566888753577693 6164154968462583282591635)
                  ·
                    refine ⟨9246232452693874923887453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6164154968462583282591635 9246232452693874923887453)
                    ·
                      refine ⟨3467337169760203096457795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9246232452693874923887453 3467337169760203096457795)
                      ·
                        rfl

theorem cell23_6752615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 3, 3, 1, 3].length) (baseStart_6752615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6752615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6752615 prefixEnd_6752615 := by exact prefixLift 6752615
  have htrace : WordTrace (prefixWord ++ tailWord_6752615) baseStart_6752615 baseEnd_6752615 := by
    simpa [prefixWord, tailWord_6752615, baseEnd_6752615] using wordTrace_append hprefix tailTrace_6752615
  have hstable : (prefixWord ++ tailWord_6752615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6752615).length < 2 ^ (prefixWord ++ tailWord_6752615).sum := by decide
  have hdescent : baseEnd_6752615 < baseStart_6752615 := by decide
  rcases family_descends (prefixWord ++ tailWord_6752615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6752631 : List Nat := [1, 1, 3, 1, 1, 2, 2, 5, 1, 6]
def baseStart_6752631 : Nat := 118140960795 + 6752631 * 2 ^ 59
def prefixEnd_6752631 : Nat := 4983230072969 + 3 ^ 40 * 6752631 * 2
def baseEnd_6752631 : Nat := 1155781795150225011285907

theorem tailTrace_6752631 : CollatzResearch.WordTrace tailWord_6752631 prefixEnd_6752631 1155781795150225011285907 := by
  unfold tailWord_6752631
  simp only [CollatzResearch.WordTrace]
  refine ⟨246288685999378619404385747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164192457332919079602923831 246288685999378619404385747)
  ·
    refine ⟨369433028999067929106578621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246288685999378619404385747 369433028999067929106578621)
    ·
      refine ⟨138537385874650473414966983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 369433028999067929106578621 138537385874650473414966983)
      ·
        refine ⟨207806078811975710122450475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138537385874650473414966983 207806078811975710122450475)
        ·
          refine ⟨311709118217963565183675713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207806078811975710122450475 311709118217963565183675713)
          ·
            refine ⟨233781838663472673887756785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 311709118217963565183675713 233781838663472673887756785)
            ·
              refine ⟨175336378997604505415817589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 233781838663472673887756785 175336378997604505415817589)
              ·
                refine ⟨16437785531025422382732899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 175336378997604505415817589 16437785531025422382732899)
                ·
                  refine ⟨24656678296538133574099349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16437785531025422382732899 24656678296538133574099349)
                  ·
                    refine ⟨1155781795150225011285907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24656678296538133574099349 1155781795150225011285907)
                    ·
                      rfl

theorem cell23_6752631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 5, 1, 6].length) (baseStart_6752631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6752631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6752631 prefixEnd_6752631 := by exact prefixLift 6752631
  have htrace : WordTrace (prefixWord ++ tailWord_6752631) baseStart_6752631 baseEnd_6752631 := by
    simpa [prefixWord, tailWord_6752631, baseEnd_6752631] using wordTrace_append hprefix tailTrace_6752631
  have hstable : (prefixWord ++ tailWord_6752631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6752631).length < 2 ^ (prefixWord ++ tailWord_6752631).sum := by decide
  have hdescent : baseEnd_6752631 < baseStart_6752631 := by decide
  rcases family_descends (prefixWord ++ tailWord_6752631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6752648 : List Nat := [2, 1, 3, 3, 1, 1, 1, 1, 6, 4]
def baseStart_6752648 : Nat := 118140960795 + 6752648 * 2 ^ 59
def prefixEnd_6752648 : Nat := 4983230072969 + 3 ^ 40 * 6752648 * 2
def baseEnd_6752648 : Nat := 1155784704873933822448381

theorem tailTrace_6752648 : CollatzResearch.WordTrace tailWord_6752648 prefixEnd_6752648 1155784704873933822448381 := by
  unfold tailWord_6752648
  simp only [CollatzResearch.WordTrace]
  refine ⟨123144653020158515653877299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164192870693544687538503065 123144653020158515653877299)
  ·
    refine ⟨184716979530237773480815949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123144653020158515653877299 184716979530237773480815949)
    ·
      refine ⟨69268867323839165055305981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184716979530237773480815949 69268867323839165055305981)
      ·
        refine ⟨25975825246439686895739743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69268867323839165055305981 25975825246439686895739743)
        ·
          refine ⟨38963737869659530343609615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25975825246439686895739743 38963737869659530343609615)
          ·
            refine ⟨58445606804489295515414423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38963737869659530343609615 58445606804489295515414423)
            ·
              refine ⟨87668410206733943273121635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58445606804489295515414423 87668410206733943273121635)
              ·
                refine ⟨131502615310100914909682453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87668410206733943273121635 131502615310100914909682453)
                ·
                  refine ⟨6164185092660980386391365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 131502615310100914909682453 6164185092660980386391365)
                  ·
                    refine ⟨1155784704873933822448381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6164185092660980386391365 1155784704873933822448381)
                    ·
                      rfl

theorem cell23_6752648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 6, 4].length) (baseStart_6752648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6752648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6752648 prefixEnd_6752648 := by exact prefixLift 6752648
  have htrace : WordTrace (prefixWord ++ tailWord_6752648) baseStart_6752648 baseEnd_6752648 := by
    simpa [prefixWord, tailWord_6752648, baseEnd_6752648] using wordTrace_append hprefix tailTrace_6752648
  have hstable : (prefixWord ++ tailWord_6752648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6752648).length < 2 ^ (prefixWord ++ tailWord_6752648).sum := by decide
  have hdescent : baseEnd_6752648 < baseStart_6752648 := by decide
  rcases family_descends (prefixWord ++ tailWord_6752648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6752649 : List Nat := [1, 2, 1, 1, 6, 3, 1, 3, 1, 1, 3]
def baseStart_6752649 : Nat := 118140960795 + 6752649 * 2 ^ 59
def prefixEnd_6752649 : Nat := 4983230072969 + 3 ^ 40 * 6752649 * 2
def baseEnd_6752649 : Nat := 3467354628102455963432639

theorem tailTrace_6752649 : CollatzResearch.WordTrace tailWord_6752649 prefixEnd_6752649 3467354628102455963432639 := by
  unfold tailWord_6752649
  simp only [CollatzResearch.WordTrace]
  refine ⟨246289342513313408478541001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164192895008875605652360667 246289342513313408478541001)
  ·
    refine ⟨184717006884985056358905751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246289342513313408478541001 184717006884985056358905751)
    ·
      refine ⟨277075510327477584538358627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184717006884985056358905751 277075510327477584538358627)
      ·
        refine ⟨415613265491216376807537941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277075510327477584538358627 415613265491216376807537941)
        ·
          refine ⟨19481871819900767662853341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 415613265491216376807537941 19481871819900767662853341)
          ·
            refine ⟨7305701932462787873570003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19481871819900767662853341 7305701932462787873570003)
            ·
              refine ⟨10958552898694181810355005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7305701932462787873570003 10958552898694181810355005)
              ·
                refine ⟨4109457337010318178883127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10958552898694181810355005 4109457337010318178883127)
                ·
                  refine ⟨6164186005515477268324691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4109457337010318178883127 6164186005515477268324691)
                  ·
                    refine ⟨9246279008273215902487037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6164186005515477268324691 9246279008273215902487037)
                    ·
                      refine ⟨3467354628102455963432639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9246279008273215902487037 3467354628102455963432639)
                      ·
                        rfl

theorem cell23_6752649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 3, 1, 1, 3].length) (baseStart_6752649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6752649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6752649 prefixEnd_6752649 := by exact prefixLift 6752649
  have htrace : WordTrace (prefixWord ++ tailWord_6752649) baseStart_6752649 baseEnd_6752649 := by
    simpa [prefixWord, tailWord_6752649, baseEnd_6752649] using wordTrace_append hprefix tailTrace_6752649
  have hstable : (prefixWord ++ tailWord_6752649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6752649).length < 2 ^ (prefixWord ++ tailWord_6752649).sum := by decide
  have hdescent : baseEnd_6752649 < baseStart_6752649 := by decide
  rcases family_descends (prefixWord ++ tailWord_6752649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6752672 : List Nat := [2, 1, 1, 4, 1, 3, 3, 1, 3, 2, 2]
def baseStart_6752672 : Nat := 118140960795 + 6752672 * 2 ^ 59
def prefixEnd_6752672 : Nat := 4983230072969 + 3 ^ 40 * 6752672 * 2
def baseEnd_6752672 : Nat := 3467366438157509373445033

theorem tailTrace_6752672 : CollatzResearch.WordTrace tailWord_6752672 prefixEnd_6752672 3467366438157509373445033 := by
  unfold tailWord_6752672
  simp only [CollatzResearch.WordTrace]
  refine ⟨123145090696115041703314135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164193454261486722271085513 123145090696115041703314135)
  ·
    refine ⟨184717636044172562554971203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123145090696115041703314135 184717636044172562554971203)
    ·
      refine ⟨277076454066258843832456805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184717636044172562554971203 277076454066258843832456805)
      ·
        refine ⟨51951835137423533218585651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 277076454066258843832456805 51951835137423533218585651)
        ·
          refine ⟨77927752706135299827878477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51951835137423533218585651 77927752706135299827878477)
          ·
            refine ⟨29222907264800737435454429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77927752706135299827878477 29222907264800737435454429)
            ·
              refine ⟨10958590224300276538295411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29222907264800737435454429 10958590224300276538295411)
              ·
                refine ⟨16437885336450414807443117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10958590224300276538295411 16437885336450414807443117)
                ·
                  refine ⟨6164207001168905552791169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16437885336450414807443117 6164207001168905552791169)
                  ·
                    refine ⟨4623155250876679164593377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6164207001168905552791169 4623155250876679164593377)
                    ·
                      refine ⟨3467366438157509373445033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4623155250876679164593377 3467366438157509373445033)
                      ·
                        rfl

theorem cell23_6752672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 1, 3, 2, 2].length) (baseStart_6752672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6752672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6752672 prefixEnd_6752672 := by exact prefixLift 6752672
  have htrace : WordTrace (prefixWord ++ tailWord_6752672) baseStart_6752672 baseEnd_6752672 := by
    simpa [prefixWord, tailWord_6752672, baseEnd_6752672] using wordTrace_append hprefix tailTrace_6752672
  have hstable : (prefixWord ++ tailWord_6752672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6752672).length < 2 ^ (prefixWord ++ tailWord_6752672).sum := by decide
  have hdescent : baseEnd_6752672 < baseStart_6752672 := by decide
  rcases family_descends (prefixWord ++ tailWord_6752672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6752721 : List Nat := [1, 2, 2, 1, 2, 1, 1, 2, 3, 8]
def baseStart_6752721 : Nat := 118140960795 + 6752721 * 2 ^ 59
def prefixEnd_6752721 : Nat := 4983230072969 + 3 ^ 40 * 6752721 * 2
def baseEnd_6752721 : Nat := 1155797199569859893910769

theorem tailTrace_6752721 : CollatzResearch.WordTrace tailWord_6752721 prefixEnd_6752721 1155797199569859893910769 := by
  unfold tailWord_6752721
  simp only [CollatzResearch.WordTrace]
  refine ⟨246291968569052564775162017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164194645712701709850108011 246291968569052564775162017)
  ·
    refine ⟨184718976426789423581371513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246291968569052564775162017 184718976426789423581371513)
    ·
      refine ⟨138539232320092067686028635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184718976426789423581371513 138539232320092067686028635)
      ·
        refine ⟨207808848480138101529042953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138539232320092067686028635 207808848480138101529042953)
        ·
          refine ⟨155856636360103576146782215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207808848480138101529042953 155856636360103576146782215)
          ·
            refine ⟨233784954540155364220173323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155856636360103576146782215 233784954540155364220173323)
            ·
              refine ⟨350677431810233046330259985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 233784954540155364220173323 350677431810233046330259985)
              ·
                refine ⟨263008073857674784747694989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 350677431810233046330259985 263008073857674784747694989)
                ·
                  refine ⟨98628027696628044280385621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 263008073857674784747694989 98628027696628044280385621)
                  ·
                    refine ⟨1155797199569859893910769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 98628027696628044280385621 1155797199569859893910769)
                    ·
                      rfl

theorem cell23_6752721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 8].length) (baseStart_6752721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6752721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6752721 prefixEnd_6752721 := by exact prefixLift 6752721
  have htrace : WordTrace (prefixWord ++ tailWord_6752721) baseStart_6752721 baseEnd_6752721 := by
    simpa [prefixWord, tailWord_6752721, baseEnd_6752721] using wordTrace_append hprefix tailTrace_6752721
  have hstable : (prefixWord ++ tailWord_6752721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6752721).length < 2 ^ (prefixWord ++ tailWord_6752721).sum := by decide
  have hdescent : baseEnd_6752721 < baseStart_6752721 := by decide
  rcases family_descends (prefixWord ++ tailWord_6752721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6752731 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2, 2, 7, 5]
def baseStart_6752731 : Nat := 118140960795 + 6752731 * 2 ^ 59
def prefixEnd_6752731 : Nat := 4983230072969 + 3 ^ 40 * 6752731 * 2
def baseEnd_6752731 : Nat := 3467396733516124642607261

theorem tailTrace_6752731 : CollatzResearch.WordTrace tailWord_6752731 prefixEnd_6752731 3467396733516124642607261 := by
  unfold tailWord_6752731
  simp only [CollatzResearch.WordTrace]
  refine ⟨246292333299016336483026047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164194888866010890988684031 246292333299016336483026047)
  ·
    refine ⟨369438499948524504724539071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246292333299016336483026047 369438499948524504724539071)
    ·
      refine ⟨554157749922786757086808607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369438499948524504724539071 554157749922786757086808607)
      ·
        refine ⟨831236624884180135630212911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 554157749922786757086808607 831236624884180135630212911)
        ·
          refine ⟨1246854937326270203445319367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 831236624884180135630212911 1246854937326270203445319367)
          ·
            refine ⟨1870282405989405305167979051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1246854937326270203445319367 1870282405989405305167979051)
            ·
              refine ⟨2805423608984107957751968577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1870282405989405305167979051 2805423608984107957751968577)
              ·
                refine ⟨2104067706738080968313976433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2805423608984107957751968577 2104067706738080968313976433)
                ·
                  refine ⟨1578050780053560726235482325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2104067706738080968313976433 1578050780053560726235482325)
                  ·
                    refine ⟨36985565157505329521144117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1578050780053560726235482325 36985565157505329521144117)
                    ·
                      refine ⟨3467396733516124642607261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36985565157505329521144117 3467396733516124642607261)
                      ·
                        rfl

theorem cell23_6752731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7, 5].length) (baseStart_6752731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6752731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6752731 prefixEnd_6752731 := by exact prefixLift 6752731
  have htrace : WordTrace (prefixWord ++ tailWord_6752731) baseStart_6752731 baseEnd_6752731 := by
    simpa [prefixWord, tailWord_6752731, baseEnd_6752731] using wordTrace_append hprefix tailTrace_6752731
  have hstable : (prefixWord ++ tailWord_6752731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6752731).length < 2 ^ (prefixWord ++ tailWord_6752731).sum := by decide
  have hdescent : baseEnd_6752731 < baseStart_6752731 := by decide
  rcases family_descends (prefixWord ++ tailWord_6752731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6752748 : List Nat := [2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 3]
def baseStart_6752748 : Nat := 118140960795 + 6752748 * 2 ^ 59
def prefixEnd_6752748 : Nat := 4983230072969 + 3 ^ 40 * 6752748 * 2
def baseEnd_6752748 : Nat := 3467405462687251076094683

theorem tailTrace_6752748 : CollatzResearch.WordTrace tailWord_6752748 prefixEnd_6752748 3467405462687251076094683 := by
  unfold tailWord_6752748
  simp only [CollatzResearch.WordTrace]
  refine ⟨123146476669977374193197449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164195302226636498924263265 123146476669977374193197449)
  ·
    refine ⟨92359857502483030644898087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123146476669977374193197449 92359857502483030644898087)
    ·
      refine ⟨138539786253724545967347131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92359857502483030644898087 138539786253724545967347131)
      ·
        refine ⟨207809679380586818951020697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138539786253724545967347131 207809679380586818951020697)
        ·
          refine ⟨155857259535440114213265523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207809679380586818951020697 155857259535440114213265523)
          ·
            refine ⟨233785889303160171319898285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155857259535440114213265523 233785889303160171319898285)
            ·
              refine ⟨87669708488685064244961857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 233785889303160171319898285 87669708488685064244961857)
              ·
                refine ⟨65752281366513798183721393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87669708488685064244961857 65752281366513798183721393)
                ·
                  refine ⟨49314211024885348637791045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65752281366513798183721393 49314211024885348637791045)
                  ·
                    refine ⟨9246414567166002869585821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49314211024885348637791045 9246414567166002869585821)
                    ·
                      refine ⟨3467405462687251076094683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9246414567166002869585821 3467405462687251076094683)
                      ·
                        rfl

theorem cell23_6752748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 3].length) (baseStart_6752748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6752748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6752748 prefixEnd_6752748 := by exact prefixLift 6752748
  have htrace : WordTrace (prefixWord ++ tailWord_6752748) baseStart_6752748 baseEnd_6752748 := by
    simpa [prefixWord, tailWord_6752748, baseEnd_6752748] using wordTrace_append hprefix tailTrace_6752748
  have hstable : (prefixWord ++ tailWord_6752748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6752748).length < 2 ^ (prefixWord ++ tailWord_6752748).sum := by decide
  have hdescent : baseEnd_6752748 < baseStart_6752748 := by decide
  rcases family_descends (prefixWord ++ tailWord_6752748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
