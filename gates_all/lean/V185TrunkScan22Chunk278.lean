import V185TrunkScan22Chunk277

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2477123 : List Nat := [1, 1, 1, 3, 1, 2, 4, 1, 5, 3]
def baseStart_2477123 : Nat := 118140960795 + 2477123 * 2 ^ 59
def prefixEnd_2477123 : Nat := 4983230072969 + 3 ^ 40 * 2477123 * 2
def baseEnd_2477123 : Nat := 847969826204944652380283

theorem tailTrace_2477123 : CollatzResearch.WordTrace tailWord_2477123 prefixEnd_2477123 847969826204944652380283 := by
  unfold tailWord_2477123
  simp only [CollatzResearch.WordTrace]
  refine ⟨90348098204813904772068023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60232065469875936514712015 90348098204813904772068023)
  ·
    refine ⟨135522147307220857158102035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90348098204813904772068023 135522147307220857158102035)
    ·
      refine ⟨203283220960831285737153053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135522147307220857158102035 203283220960831285737153053)
      ·
        refine ⟨76231207860311732151432395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 203283220960831285737153053 76231207860311732151432395)
        ·
          refine ⟨114346811790467598227148593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76231207860311732151432395 114346811790467598227148593)
          ·
            refine ⟨85760108842850698670361445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114346811790467598227148593 85760108842850698670361445)
            ·
              refine ⟨16080020408034506000692771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 85760108842850698670361445 16080020408034506000692771)
              ·
                refine ⟨24120030612051759001039157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16080020408034506000692771 24120030612051759001039157)
                ·
                  refine ⟨2261252869879852406347421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24120030612051759001039157 2261252869879852406347421)
                  ·
                    refine ⟨847969826204944652380283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2261252869879852406347421 847969826204944652380283)
                    ·
                      rfl

theorem cell22_2477123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 1, 5, 3].length) (baseStart_2477123 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2477123 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2477123 prefixEnd_2477123 := by exact prefixLift 2477123
  have htrace : WordTrace (prefixWord ++ tailWord_2477123) baseStart_2477123 baseEnd_2477123 := by
    simpa [prefixWord, tailWord_2477123, baseEnd_2477123] using wordTrace_append hprefix tailTrace_2477123
  have hstable : (prefixWord ++ tailWord_2477123).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2477123).length < 2 ^ (prefixWord ++ tailWord_2477123).sum := by decide
  have hdescent : baseEnd_2477123 < baseStart_2477123 := by decide
  rcases family_descends (prefixWord ++ tailWord_2477123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2477136 : List Nat := [2, 1, 1, 1, 1, 3, 1, 3, 9]
def baseStart_2477136 : Nat := 118140960795 + 2477136 * 2 ^ 59
def prefixEnd_2477136 : Nat := 4983230072969 + 3 ^ 40 * 2477136 * 2
def baseEnd_2477136 : Nat := 282658092123538983935081

theorem tailTrace_2477136 : CollatzResearch.WordTrace tailWord_2477136 prefixEnd_2477136 282658092123538983935081 := by
  unfold tailWord_2477136
  simp only [CollatzResearch.WordTrace]
  refine ⟨45174286176883403996145631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60232381569177871994860841 45174286176883403996145631)
  ·
    refine ⟨67761429265325105994218447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45174286176883403996145631 67761429265325105994218447)
    ·
      refine ⟨101642143897987658991327671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67761429265325105994218447 101642143897987658991327671)
      ·
        refine ⟨152463215846981488486991507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101642143897987658991327671 152463215846981488486991507)
        ·
          refine ⟨228694823770472232730487261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152463215846981488486991507 228694823770472232730487261)
          ·
            refine ⟨85760558913927087273932723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 228694823770472232730487261 85760558913927087273932723)
            ·
              refine ⟨128640838370890630910899085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85760558913927087273932723 128640838370890630910899085)
              ·
                refine ⟨48240314389083986591587157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 128640838370890630910899085 48240314389083986591587157)
                ·
                  refine ⟨282658092123538983935081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 48240314389083986591587157 282658092123538983935081)
                  ·
                    rfl

theorem cell22_2477136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 9].length) (baseStart_2477136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2477136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2477136 prefixEnd_2477136 := by exact prefixLift 2477136
  have htrace : WordTrace (prefixWord ++ tailWord_2477136) baseStart_2477136 baseEnd_2477136 := by
    simpa [prefixWord, tailWord_2477136, baseEnd_2477136] using wordTrace_append hprefix tailTrace_2477136
  have hstable : (prefixWord ++ tailWord_2477136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2477136).length < 2 ^ (prefixWord ++ tailWord_2477136).sum := by decide
  have hdescent : baseEnd_2477136 < baseStart_2477136 := by decide
  rcases family_descends (prefixWord ++ tailWord_2477136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2477142 : List Nat := [5, 2, 2, 1, 3, 9]
def baseStart_2477142 : Nat := 118140960795 + 2477142 * 2 ^ 59
def prefixEnd_2477142 : Nat := 4983230072969 + 3 ^ 40 * 2477142 * 2
def baseEnd_2477142 : Nat := 10468843583867097977225

theorem tailTrace_2477142 : CollatzResearch.WordTrace tailWord_2477142 prefixEnd_2477142 10468843583867097977225 := by
  unfold tailWord_2477142
  simp only [CollatzResearch.WordTrace]
  refine ⟨5646799449484066938563105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 60232527461163380678006453 5646799449484066938563105)
  ·
    refine ⟨4235099587113050203922329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5646799449484066938563105 4235099587113050203922329)
    ·
      refine ⟨3176324690334787652941747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4235099587113050203922329 3176324690334787652941747)
      ·
        refine ⟨4764487035502181479412621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3176324690334787652941747 4764487035502181479412621)
        ·
          refine ⟨1786682638313318054779733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4764487035502181479412621 1786682638313318054779733)
          ·
            refine ⟨10468843583867097977225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1786682638313318054779733 10468843583867097977225)
            ·
              rfl

theorem cell22_2477142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 9].length) (baseStart_2477142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2477142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2477142 prefixEnd_2477142 := by exact prefixLift 2477142
  have htrace : WordTrace (prefixWord ++ tailWord_2477142) baseStart_2477142 baseEnd_2477142 := by
    simpa [prefixWord, tailWord_2477142, baseEnd_2477142] using wordTrace_append hprefix tailTrace_2477142
  have hstable : (prefixWord ++ tailWord_2477142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2477142).length < 2 ^ (prefixWord ++ tailWord_2477142).sum := by decide
  have hdescent : baseEnd_2477142 < baseStart_2477142 := by decide
  rcases family_descends (prefixWord ++ tailWord_2477142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2477153 : List Nat := [1, 2, 3, 1, 1, 2, 3, 4, 5]
def baseStart_2477153 : Nat := 118140960795 + 2477153 * 2 ^ 59
def prefixEnd_2477153 : Nat := 4983230072969 + 3 ^ 40 * 2477153 * 2
def baseEnd_2477153 : Nat := 282660031939344858043397

theorem tailTrace_2477153 : CollatzResearch.WordTrace tailWord_2477153 prefixEnd_2477153 282660031939344858043397 := by
  unfold tailWord_2477153
  simp only [CollatzResearch.WordTrace]
  refine ⟨90349192394705219895660113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60232794929803479930440075 90349192394705219895660113)
  ·
    refine ⟨67761894296028914921745085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90349192394705219895660113 67761894296028914921745085)
    ·
      refine ⟨25410710361010843095654407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67761894296028914921745085 25410710361010843095654407)
      ·
        refine ⟨38116065541516264643481611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25410710361010843095654407 38116065541516264643481611)
        ·
          refine ⟨57174098312274396965222417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38116065541516264643481611 57174098312274396965222417)
          ·
            refine ⟨42880573734205797723916813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57174098312274396965222417 42880573734205797723916813)
            ·
              refine ⟨16080215150327174146468805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42880573734205797723916813 16080215150327174146468805)
              ·
                refine ⟨3015040340686345152462901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16080215150327174146468805 3015040340686345152462901)
                ·
                  refine ⟨282660031939344858043397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3015040340686345152462901 282660031939344858043397)
                  ·
                    rfl

theorem cell22_2477153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 4, 5].length) (baseStart_2477153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2477153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2477153 prefixEnd_2477153 := by exact prefixLift 2477153
  have htrace : WordTrace (prefixWord ++ tailWord_2477153) baseStart_2477153 baseEnd_2477153 := by
    simpa [prefixWord, tailWord_2477153, baseEnd_2477153] using wordTrace_append hprefix tailTrace_2477153
  have hstable : (prefixWord ++ tailWord_2477153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2477153).length < 2 ^ (prefixWord ++ tailWord_2477153).sum := by decide
  have hdescent : baseEnd_2477153 < baseStart_2477153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2477153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2477157 : List Nat := [1, 3, 1, 3, 2, 1, 3, 4, 1, 3]
def baseStart_2477157 : Nat := 118140960795 + 2477157 * 2 ^ 59
def prefixEnd_2477157 : Nat := 4983230072969 + 3 ^ 40 * 2477157 * 2
def baseEnd_2477157 : Nat := 847981465099779897030179

theorem tailTrace_2477157 : CollatzResearch.WordTrace tailWord_2477157 prefixEnd_2477157 847981465099779897030179 := by
  unfold tailWord_2477157
  simp only [CollatzResearch.WordTrace]
  refine ⟨90349338286690728578805725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60232892191127152385870483 90349338286690728578805725)
  ·
    refine ⟨33881001857509023217052147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90349338286690728578805725 33881001857509023217052147)
    ·
      refine ⟨50821502786263534825578221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33881001857509023217052147 50821502786263534825578221)
      ·
        refine ⟨19058063544848825559591833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50821502786263534825578221 19058063544848825559591833)
        ·
          refine ⟨14293547658636619169693875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19058063544848825559591833 14293547658636619169693875)
          ·
            refine ⟨21440321487954928754540813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14293547658636619169693875 21440321487954928754540813)
            ·
              refine ⟨8040120557983098282952805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21440321487954928754540813 8040120557983098282952805)
              ·
                refine ⟨1507522604621830928053651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8040120557983098282952805 1507522604621830928053651)
                ·
                  refine ⟨2261283906932746392080477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1507522604621830928053651 2261283906932746392080477)
                  ·
                    refine ⟨847981465099779897030179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2261283906932746392080477 847981465099779897030179)
                    ·
                      rfl

theorem cell22_2477157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 4, 1, 3].length) (baseStart_2477157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2477157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2477157 prefixEnd_2477157 := by exact prefixLift 2477157
  have htrace : WordTrace (prefixWord ++ tailWord_2477157) baseStart_2477157 baseEnd_2477157 := by
    simpa [prefixWord, tailWord_2477157, baseEnd_2477157] using wordTrace_append hprefix tailTrace_2477157
  have hstable : (prefixWord ++ tailWord_2477157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2477157).length < 2 ^ (prefixWord ++ tailWord_2477157).sum := by decide
  have hdescent : baseEnd_2477157 < baseStart_2477157 := by decide
  rcases family_descends (prefixWord ++ tailWord_2477157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2477168 : List Nat := [2, 1, 1, 1, 5, 1, 3, 1, 2, 5]
def baseStart_2477168 : Nat := 118140960795 + 2477168 * 2 ^ 59
def prefixEnd_2477168 : Nat := 4983230072969 + 3 ^ 40 * 2477168 * 2
def baseEnd_2477168 : Nat := 847985230624579535005145

theorem tailTrace_2477168 : CollatzResearch.WordTrace tailWord_2477168 prefixEnd_2477168 847985230624579535005145 := by
  unfold tailWord_2477168
  simp only [CollatzResearch.WordTrace]
  refine ⟨45174869744825438728728079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60233159659767251638304105 45174869744825438728728079)
  ·
    refine ⟨67762304617238158093092119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45174869744825438728728079 67762304617238158093092119)
    ·
      refine ⟨101643456925857237139638179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67762304617238158093092119 101643456925857237139638179)
      ·
        refine ⟨152465185388785855709457269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101643456925857237139638179 152465185388785855709457269)
        ·
          refine ⟨14293611130198673972761619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 152465185388785855709457269 14293611130198673972761619)
          ·
            refine ⟨21440416695298010959142429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14293611130198673972761619 21440416695298010959142429)
            ·
              refine ⟨8040156260736754109678411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21440416695298010959142429 8040156260736754109678411)
              ·
                refine ⟨12060234391105131164517617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8040156260736754109678411 12060234391105131164517617)
                ·
                  refine ⟨9045175793328848373388213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12060234391105131164517617 9045175793328848373388213)
                  ·
                    refine ⟨847985230624579535005145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9045175793328848373388213 847985230624579535005145)
                    ·
                      rfl

theorem cell22_2477168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 1, 2, 5].length) (baseStart_2477168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2477168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2477168 prefixEnd_2477168 := by exact prefixLift 2477168
  have htrace : WordTrace (prefixWord ++ tailWord_2477168) baseStart_2477168 baseEnd_2477168 := by
    simpa [prefixWord, tailWord_2477168, baseEnd_2477168] using wordTrace_append hprefix tailTrace_2477168
  have hstable : (prefixWord ++ tailWord_2477168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2477168).length < 2 ^ (prefixWord ++ tailWord_2477168).sum := by decide
  have hdescent : baseEnd_2477168 < baseStart_2477168 := by decide
  rcases family_descends (prefixWord ++ tailWord_2477168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2477228 : List Nat := [2, 2, 1, 1, 1, 1, 1, 3, 6, 4]
def baseStart_2477228 : Nat := 118140960795 + 2477228 * 2 ^ 59
def prefixEnd_2477228 : Nat := 4983230072969 + 3 ^ 40 * 2477228 * 2
def baseEnd_2477228 : Nat := 848005769850759378504961

theorem tailTrace_2477228 : CollatzResearch.WordTrace tailWord_2477228 prefixEnd_2477228 848005769850759378504961 := by
  unfold tailWord_2477228
  simp only [CollatzResearch.WordTrace]
  refine ⟨45175963934716753852320169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60234618579622338469760225 45175963934716753852320169)
  ·
    refine ⟨33881972951037565389240127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45175963934716753852320169 33881972951037565389240127)
    ·
      refine ⟨50822959426556348083860191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33881972951037565389240127 50822959426556348083860191)
      ·
        refine ⟨76234439139834522125790287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50822959426556348083860191 76234439139834522125790287)
        ·
          refine ⟨114351658709751783188685431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76234439139834522125790287 114351658709751783188685431)
          ·
            refine ⟨171527488064627674783028147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114351658709751783188685431 171527488064627674783028147)
            ·
              refine ⟨257291232096941512174542221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 171527488064627674783028147 257291232096941512174542221)
              ·
                refine ⟨96484212036353067065453333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 257291232096941512174542221 96484212036353067065453333)
                ·
                  refine ⟨4522697439204050018693125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 96484212036353067065453333 4522697439204050018693125)
                  ·
                    refine ⟨848005769850759378504961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4522697439204050018693125 848005769850759378504961)
                    ·
                      rfl

theorem cell22_2477228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 4].length) (baseStart_2477228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2477228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2477228 prefixEnd_2477228 := by exact prefixLift 2477228
  have htrace : WordTrace (prefixWord ++ tailWord_2477228) baseStart_2477228 baseEnd_2477228 := by
    simpa [prefixWord, tailWord_2477228, baseEnd_2477228] using wordTrace_append hprefix tailTrace_2477228
  have hstable : (prefixWord ++ tailWord_2477228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2477228).length < 2 ^ (prefixWord ++ tailWord_2477228).sum := by decide
  have hdescent : baseEnd_2477228 < baseStart_2477228 := by decide
  rcases family_descends (prefixWord ++ tailWord_2477228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2477249 : List Nat := [1, 2, 6, 1, 1, 1, 3, 3, 4]
def baseStart_2477249 : Nat := 118140960795 + 2477249 * 2 ^ 59
def prefixEnd_2477249 : Nat := 4983230072969 + 3 ^ 40 * 2477249 * 2
def baseEnd_2477249 : Nat := 282670986193307441243299

theorem tailTrace_2477249 : CollatzResearch.WordTrace tailWord_2477249 prefixEnd_2477249 282670986193307441243299 := by
  unfold tailWord_2477249
  simp only [CollatzResearch.WordTrace]
  refine ⟨90352693802357428291154801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60235129201571618860769867 90352693802357428291154801)
  ·
    refine ⟨67764520351768071218366101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90352693802357428291154801 67764520351768071218366101)
    ·
      refine ⟨3176461891489128338360911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 67764520351768071218366101 3176461891489128338360911)
      ·
        refine ⟨4764692837233692507541367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3176461891489128338360911 4764692837233692507541367)
        ·
          refine ⟨7147039255850538761312051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4764692837233692507541367 7147039255850538761312051)
          ·
            refine ⟨10720558883775808141968077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7147039255850538761312051 10720558883775808141968077)
            ·
              refine ⟨4020209581415928053238029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10720558883775808141968077 4020209581415928053238029)
              ·
                refine ⟨1507578593030973019964261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4020209581415928053238029 1507578593030973019964261)
                ·
                  refine ⟨282670986193307441243299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1507578593030973019964261 282670986193307441243299)
                  ·
                    rfl

theorem cell22_2477249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 3, 4].length) (baseStart_2477249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2477249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2477249 prefixEnd_2477249 := by exact prefixLift 2477249
  have htrace : WordTrace (prefixWord ++ tailWord_2477249) baseStart_2477249 baseEnd_2477249 := by
    simpa [prefixWord, tailWord_2477249, baseEnd_2477249] using wordTrace_append hprefix tailTrace_2477249
  have hstable : (prefixWord ++ tailWord_2477249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2477249).length < 2 ^ (prefixWord ++ tailWord_2477249).sum := by decide
  have hdescent : baseEnd_2477249 < baseStart_2477249 := by decide
  rcases family_descends (prefixWord ++ tailWord_2477249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2477262 : List Nat := [4, 1, 1, 1, 5, 1, 1, 2, 2, 4]
def baseStart_2477262 : Nat := 118140960795 + 2477262 * 2 ^ 59
def prefixEnd_2477262 : Nat := 4983230072969 + 3 ^ 40 * 2477262 * 2
def baseEnd_2477262 : Nat := 848017408745594623154857

theorem tailTrace_2477262 : CollatzResearch.WordTrace tailWord_2477262 prefixEnd_2477262 848017408745594623154857 := by
  unfold tailWord_2477262
  simp only [CollatzResearch.WordTrace]
  refine ⟨11294145993913791438922255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60235445300873554340918693 11294145993913791438922255)
  ·
    refine ⟨16941218990870687158383383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11294145993913791438922255 16941218990870687158383383)
    ·
      refine ⟨25411828486306030737575075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16941218990870687158383383 25411828486306030737575075)
      ·
        refine ⟨38117742729459046106362613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25411828486306030737575075 38117742729459046106362613)
        ·
          refine ⟨3573538380886785572471495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38117742729459046106362613 3573538380886785572471495)
          ·
            refine ⟨5360307571330178358707243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3573538380886785572471495 5360307571330178358707243)
            ·
              refine ⟨8040461356995267538060865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5360307571330178358707243 8040461356995267538060865)
              ·
                refine ⟨6030346017746450653545649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8040461356995267538060865 6030346017746450653545649)
                ·
                  refine ⟨4522759513309837990159237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6030346017746450653545649 4522759513309837990159237)
                  ·
                    refine ⟨848017408745594623154857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4522759513309837990159237 848017408745594623154857)
                    ·
                      rfl

theorem cell22_2477262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 2, 2, 4].length) (baseStart_2477262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2477262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2477262 prefixEnd_2477262 := by exact prefixLift 2477262
  have htrace : WordTrace (prefixWord ++ tailWord_2477262) baseStart_2477262 baseEnd_2477262 := by
    simpa [prefixWord, tailWord_2477262, baseEnd_2477262] using wordTrace_append hprefix tailTrace_2477262
  have hstable : (prefixWord ++ tailWord_2477262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2477262).length < 2 ^ (prefixWord ++ tailWord_2477262).sum := by decide
  have hdescent : baseEnd_2477262 < baseStart_2477262 := by decide
  rcases family_descends (prefixWord ++ tailWord_2477262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2477273 : List Nat := [1, 2, 1, 2, 3, 1, 1, 3, 2, 6]
def baseStart_2477273 : Nat := 118140960795 + 2477273 * 2 ^ 59
def prefixEnd_2477273 : Nat := 4983230072969 + 3 ^ 40 * 2477273 * 2
def baseEnd_2477273 : Nat := 848021174270394261129823

theorem tailTrace_2477273 : CollatzResearch.WordTrace tailWord_2477273 prefixEnd_2477273 848021174270394261129823 := by
  unfold tailWord_2477273
  simp only [CollatzResearch.WordTrace]
  refine ⟨90353569154270480390028473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60235712769513653593352315 90353569154270480390028473)
  ·
    refine ⟨67765176865702860292521355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90353569154270480390028473 67765176865702860292521355)
    ·
      refine ⟨101647765298554290438782033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67765176865702860292521355 101647765298554290438782033)
      ·
        refine ⟨76235823973915717829086525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101647765298554290438782033 76235823973915717829086525)
        ·
          refine ⟨28588433990218394185907447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76235823973915717829086525 28588433990218394185907447)
          ·
            refine ⟨42882650985327591278861171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28588433990218394185907447 42882650985327591278861171)
            ·
              refine ⟨64323976477991386918291757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42882650985327591278861171 64323976477991386918291757)
              ·
                refine ⟨24121491179246770094359409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64323976477991386918291757 24121491179246770094359409)
                ·
                  refine ⟨18091118384435077570769557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24121491179246770094359409 18091118384435077570769557)
                  ·
                    refine ⟨848021174270394261129823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18091118384435077570769557 848021174270394261129823)
                    ·
                      rfl

theorem cell22_2477273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 3, 2, 6].length) (baseStart_2477273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2477273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2477273 prefixEnd_2477273 := by exact prefixLift 2477273
  have htrace : WordTrace (prefixWord ++ tailWord_2477273) baseStart_2477273 baseEnd_2477273 := by
    simpa [prefixWord, tailWord_2477273, baseEnd_2477273] using wordTrace_append hprefix tailTrace_2477273
  have hstable : (prefixWord ++ tailWord_2477273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2477273).length < 2 ^ (prefixWord ++ tailWord_2477273).sum := by decide
  have hdescent : baseEnd_2477273 < baseStart_2477273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2477273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2477277 : List Nat := [1, 4, 3, 2, 2, 1, 2, 7]
def baseStart_2477277 : Nat := 118140960795 + 2477277 * 2 ^ 59
def prefixEnd_2477277 : Nat := 4983230072969 + 3 ^ 40 * 2477277 * 2
def baseEnd_2477277 : Nat := 94224727061348842669979

theorem tailTrace_2477277 : CollatzResearch.WordTrace tailWord_2477277 prefixEnd_2477277 94224727061348842669979 := by
  unfold tailWord_2477277
  simp only [CollatzResearch.WordTrace]
  refine ⟨90353715046255989073174085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60235810030837326048782723 90353715046255989073174085)
  ·
    refine ⟨16941321571172997951220141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90353715046255989073174085 16941321571172997951220141)
    ·
      refine ⟨6352995589189874231707553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16941321571172997951220141 6352995589189874231707553)
      ·
        refine ⟨4764746691892405673780665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6352995589189874231707553 4764746691892405673780665)
        ·
          refine ⟨3573560018919304255335499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4764746691892405673780665 3573560018919304255335499)
          ·
            refine ⟨5360340028378956383003249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3573560018919304255335499 5360340028378956383003249)
            ·
              refine ⟨4020255021284217287252437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5360340028378956383003249 4020255021284217287252437)
              ·
                refine ⟨94224727061348842669979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4020255021284217287252437 94224727061348842669979)
                ·
                  rfl

theorem cell22_2477277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 7].length) (baseStart_2477277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2477277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2477277 prefixEnd_2477277 := by exact prefixLift 2477277
  have htrace : WordTrace (prefixWord ++ tailWord_2477277) baseStart_2477277 baseEnd_2477277 := by
    simpa [prefixWord, tailWord_2477277, baseEnd_2477277] using wordTrace_append hprefix tailTrace_2477277
  have hstable : (prefixWord ++ tailWord_2477277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2477277).length < 2 ^ (prefixWord ++ tailWord_2477277).sum := by decide
  have hdescent : baseEnd_2477277 < baseStart_2477277 := by decide
  rcases family_descends (prefixWord ++ tailWord_2477277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2477303 : List Nat := [1, 1, 3, 1, 1, 1, 2, 4, 1, 7]
def baseStart_2477303 : Nat := 118140960795 + 2477303 * 2 ^ 59
def prefixEnd_2477303 : Nat := 4983230072969 + 3 ^ 40 * 2477303 * 2
def baseEnd_2477303 : Nat := 848031443883484182879731

theorem tailTrace_2477303 : CollatzResearch.WordTrace tailWord_2477303 prefixEnd_2477303 848031443883484182879731 := by
  unfold tailWord_2477303
  simp only [CollatzResearch.WordTrace]
  refine ⟨90354663344161795513620563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60236442229441197009080375 90354663344161795513620563)
  ·
    refine ⟨135531995016242693270430845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90354663344161795513620563 135531995016242693270430845)
    ·
      refine ⟨50824498131091009976411567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135531995016242693270430845 50824498131091009976411567)
      ·
        refine ⟨76236747196636514964617351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50824498131091009976411567 76236747196636514964617351)
        ·
          refine ⟨114355120794954772446926027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76236747196636514964617351 114355120794954772446926027)
          ·
            refine ⟨171532681192432158670389041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114355120794954772446926027 171532681192432158670389041)
            ·
              refine ⟨128649510894324119002791781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 171532681192432158670389041 128649510894324119002791781)
              ·
                refine ⟨24121783292685772313023459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 128649510894324119002791781 24121783292685772313023459)
                ·
                  refine ⟨36182674939028658469535189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24121783292685772313023459 36182674939028658469535189)
                  ·
                    refine ⟨848031443883484182879731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36182674939028658469535189 848031443883484182879731)
                    ·
                      rfl

theorem cell22_2477303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 4, 1, 7].length) (baseStart_2477303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2477303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2477303 prefixEnd_2477303 := by exact prefixLift 2477303
  have htrace : WordTrace (prefixWord ++ tailWord_2477303) baseStart_2477303 baseEnd_2477303 := by
    simpa [prefixWord, tailWord_2477303, baseEnd_2477303] using wordTrace_append hprefix tailTrace_2477303
  have hstable : (prefixWord ++ tailWord_2477303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2477303).length < 2 ^ (prefixWord ++ tailWord_2477303).sum := by decide
  have hdescent : baseEnd_2477303 < baseStart_2477303 := by decide
  rcases family_descends (prefixWord ++ tailWord_2477303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2477326 : List Nat := [4, 1, 1, 2, 1, 3, 4, 2, 1, 3]
def baseStart_2477326 : Nat := 118140960795 + 2477326 * 2 ^ 59
def prefixEnd_2477326 : Nat := 4983230072969 + 3 ^ 40 * 2477326 * 2
def baseEnd_2477326 : Nat := 848039317253519789554661

theorem tailTrace_2477326 : CollatzResearch.WordTrace tailWord_2477326 prefixEnd_2477326 848039317253519789554661 := by
  unfold tailWord_2477326
  simp only [CollatzResearch.WordTrace]
  refine ⟨11294437777884808805213479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60237001482052313627805221 11294437777884808805213479)
  ·
    refine ⟨16941656666827213207820219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11294437777884808805213479 16941656666827213207820219)
    ·
      refine ⟨25412485000240819811730329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16941656666827213207820219 25412485000240819811730329)
      ·
        refine ⟨19059363750180614858797747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25412485000240819811730329 19059363750180614858797747)
        ·
          refine ⟨28589045625270922288196621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19059363750180614858797747 28589045625270922288196621)
          ·
            refine ⟨10720892109476595858073733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28589045625270922288196621 10720892109476595858073733)
            ·
              refine ⟨2010167270526861723388825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10720892109476595858073733 2010167270526861723388825)
              ·
                refine ⟨1507625452895146292541619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2010167270526861723388825 1507625452895146292541619)
                ·
                  refine ⟨2261438179342719438812429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1507625452895146292541619 2261438179342719438812429)
                  ·
                    refine ⟨848039317253519789554661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2261438179342719438812429 848039317253519789554661)
                    ·
                      rfl

theorem cell22_2477326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 4, 2, 1, 3].length) (baseStart_2477326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2477326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2477326 prefixEnd_2477326 := by exact prefixLift 2477326
  have htrace : WordTrace (prefixWord ++ tailWord_2477326) baseStart_2477326 baseEnd_2477326 := by
    simpa [prefixWord, tailWord_2477326, baseEnd_2477326] using wordTrace_append hprefix tailTrace_2477326
  have hstable : (prefixWord ++ tailWord_2477326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2477326).length < 2 ^ (prefixWord ++ tailWord_2477326).sum := by decide
  have hdescent : baseEnd_2477326 < baseStart_2477326 := by decide
  rcases family_descends (prefixWord ++ tailWord_2477326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2477335 : List Nat := [1, 1, 3, 4, 1, 1, 1, 1, 5, 4]
def baseStart_2477335 : Nat := 118140960795 + 2477335 * 2 ^ 59
def prefixEnd_2477335 : Nat := 4983230072969 + 3 ^ 40 * 2477335 * 2
def baseEnd_2477335 : Nat := 848042398137446766079633

theorem tailTrace_2477335 : CollatzResearch.WordTrace tailWord_2477335 prefixEnd_2477335 848042398137446766079633 := by
  unfold tailWord_2477335
  simp only [CollatzResearch.WordTrace]
  refine ⟨90355830480045864978785459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60237220320030576652523639 90355830480045864978785459)
  ·
    refine ⟨135533745720068797468178189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90355830480045864978785459 135533745720068797468178189)
    ·
      refine ⟨50825154645025799050566821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135533745720068797468178189 50825154645025799050566821)
      ·
        refine ⟨9529716495942337321981279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50825154645025799050566821 9529716495942337321981279)
        ·
          refine ⟨14294574743913505982971919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9529716495942337321981279 14294574743913505982971919)
          ·
            refine ⟨21441862115870258974457879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14294574743913505982971919 21441862115870258974457879)
            ·
              refine ⟨32162793173805388461686819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21441862115870258974457879 32162793173805388461686819)
              ·
                refine ⟨48244189760708082692530229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32162793173805388461686819 48244189760708082692530229)
                ·
                  refine ⟨4522892790066382752424709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48244189760708082692530229 4522892790066382752424709)
                  ·
                    refine ⟨848042398137446766079633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4522892790066382752424709 848042398137446766079633)
                    ·
                      rfl

theorem cell22_2477335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 5, 4].length) (baseStart_2477335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2477335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2477335 prefixEnd_2477335 := by exact prefixLift 2477335
  have htrace : WordTrace (prefixWord ++ tailWord_2477335) baseStart_2477335 baseEnd_2477335 := by
    simpa [prefixWord, tailWord_2477335, baseEnd_2477335] using wordTrace_append hprefix tailTrace_2477335
  have hstable : (prefixWord ++ tailWord_2477335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2477335).length < 2 ^ (prefixWord ++ tailWord_2477335).sum := by decide
  have hdescent : baseEnd_2477335 < baseStart_2477335 := by decide
  rcases family_descends (prefixWord ++ tailWord_2477335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2477352 : List Nat := [2, 1, 5, 1, 2, 1, 2, 1, 3, 4]
def baseStart_2477352 : Nat := 118140960795 + 2477352 * 2 ^ 59
def prefixEnd_2477352 : Nat := 4983230072969 + 3 ^ 40 * 2477352 * 2
def baseEnd_2477352 : Nat := 848048217584864388404581

theorem tailTrace_2477352 : CollatzResearch.WordTrace tailWord_2477352 prefixEnd_2477352 848048217584864388404581 := by
  unfold tailWord_2477352
  simp only [CollatzResearch.WordTrace]
  refine ⟨45178225260492138441077155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60237633680656184588102873 45178225260492138441077155)
  ·
    refine ⟨67767337890738207661615733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45178225260492138441077155 67767337890738207661615733)
    ·
      refine ⟨6353187927256706968276475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 67767337890738207661615733 6353187927256706968276475)
      ·
        refine ⟨9529781890885060452414713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6353187927256706968276475 9529781890885060452414713)
        ·
          refine ⟨7147336418163795339311035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9529781890885060452414713 7147336418163795339311035)
          ·
            refine ⟨10721004627245693008966553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7147336418163795339311035 10721004627245693008966553)
            ·
              refine ⟨8040753470434269756724915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10721004627245693008966553 8040753470434269756724915)
              ·
                refine ⟨12061130205651404635087373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8040753470434269756724915 12061130205651404635087373)
                ·
                  refine ⟨4522923827119276738157765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12061130205651404635087373 4522923827119276738157765)
                  ·
                    refine ⟨848048217584864388404581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4522923827119276738157765 848048217584864388404581)
                    ·
                      rfl

theorem cell22_2477352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_2477352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2477352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2477352 prefixEnd_2477352 := by exact prefixLift 2477352
  have htrace : WordTrace (prefixWord ++ tailWord_2477352) baseStart_2477352 baseEnd_2477352 := by
    simpa [prefixWord, tailWord_2477352, baseEnd_2477352] using wordTrace_append hprefix tailTrace_2477352
  have hstable : (prefixWord ++ tailWord_2477352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2477352).length < 2 ^ (prefixWord ++ tailWord_2477352).sum := by decide
  have hdescent : baseEnd_2477352 < baseStart_2477352 := by decide
  rcases family_descends (prefixWord ++ tailWord_2477352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2477369 : List Nat := [1, 2, 1, 6, 2, 1, 1, 3, 1, 4]
def baseStart_2477369 : Nat := 118140960795 + 2477369 * 2 ^ 59
def prefixEnd_2477369 : Nat := 4983230072969 + 3 ^ 40 * 2477369 * 2
def baseEnd_2477369 : Nat := 848054037032282010729529

theorem tailTrace_2477369 : CollatzResearch.WordTrace tailWord_2477369 prefixEnd_2477369 848054037032282010729529 := by
  unfold tailWord_2477369
  simp only [CollatzResearch.WordTrace]
  refine ⟨90357070561922688785523161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60238047041281792523682107 90357070561922688785523161)
  ·
    refine ⟨67767802921442016589142371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90357070561922688785523161 67767802921442016589142371)
    ·
      refine ⟨101651704382163024883713557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67767802921442016589142371 101651704382163024883713557)
      ·
        refine ⟨4764923642913891791424073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 101651704382163024883713557 4764923642913891791424073)
        ·
          refine ⟨3573692732185418843568055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4764923642913891791424073 3573692732185418843568055)
          ·
            refine ⟨5360539098278128265352083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3573692732185418843568055 5360539098278128265352083)
            ·
              refine ⟨8040808647417192398028125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5360539098278128265352083 8040808647417192398028125)
              ·
                refine ⟨3015303242781447149260547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8040808647417192398028125 3015303242781447149260547)
                ·
                  refine ⟨4522954864172170723890821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3015303242781447149260547 4522954864172170723890821)
                  ·
                    refine ⟨848054037032282010729529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4522954864172170723890821 848054037032282010729529)
                    ·
                      rfl

theorem cell22_2477369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 3, 1, 4].length) (baseStart_2477369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2477369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2477369 prefixEnd_2477369 := by exact prefixLift 2477369
  have htrace : WordTrace (prefixWord ++ tailWord_2477369) baseStart_2477369 baseEnd_2477369 := by
    simpa [prefixWord, tailWord_2477369, baseEnd_2477369] using wordTrace_append hprefix tailTrace_2477369
  have hstable : (prefixWord ++ tailWord_2477369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2477369).length < 2 ^ (prefixWord ++ tailWord_2477369).sum := by decide
  have hdescent : baseEnd_2477369 < baseStart_2477369 := by decide
  rcases family_descends (prefixWord ++ tailWord_2477369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2477412 : List Nat := [2, 3, 1, 1, 3, 2, 4, 6]
def baseStart_2477412 : Nat := 118140960795 + 2477412 * 2 ^ 59
def prefixEnd_2477412 : Nat := 4983230072969 + 3 ^ 40 * 2477412 * 2
def baseEnd_2477412 : Nat := 94229861867893803544933

theorem tailTrace_2477412 : CollatzResearch.WordTrace tailWord_2477412 prefixEnd_2477412 94229861867893803544933 := by
  unfold tailWord_2477412
  simp only [CollatzResearch.WordTrace]
  refine ⟨45179319450383453564669245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60239092600511271419558993 45179319450383453564669245)
  ·
    refine ⟨16942244793893795086750967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45179319450383453564669245 16942244793893795086750967)
    ·
      refine ⟨25413367190840692630126451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16942244793893795086750967 25413367190840692630126451)
      ·
        refine ⟨38120050786261038945189677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25413367190840692630126451 38120050786261038945189677)
        ·
          refine ⟨14295019044847889604446129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38120050786261038945189677 14295019044847889604446129)
          ·
            refine ⟨10721264283635917203334597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14295019044847889604446129 10721264283635917203334597)
            ·
              refine ⟨2010237053181734475625237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10721264283635917203334597 2010237053181734475625237)
              ·
                refine ⟨94229861867893803544933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2010237053181734475625237 94229861867893803544933)
                ·
                  rfl

theorem cell22_2477412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 4, 6].length) (baseStart_2477412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2477412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2477412 prefixEnd_2477412 := by exact prefixLift 2477412
  have htrace : WordTrace (prefixWord ++ tailWord_2477412) baseStart_2477412 baseEnd_2477412 := by
    simpa [prefixWord, tailWord_2477412, baseEnd_2477412] using wordTrace_append hprefix tailTrace_2477412
  have hstable : (prefixWord ++ tailWord_2477412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2477412).length < 2 ^ (prefixWord ++ tailWord_2477412).sum := by decide
  have hdescent : baseEnd_2477412 < baseStart_2477412 := by decide
  rcases family_descends (prefixWord ++ tailWord_2477412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2477418 : List Nat := [3, 1, 3, 3, 3, 1, 1, 3, 4]
def baseStart_2477418 : Nat := 118140960795 + 2477418 * 2 ^ 59
def prefixEnd_2477418 : Nat := 4983230072969 + 3 ^ 40 * 2477418 * 2
def baseEnd_2477418 : Nat := 282690270244554072084793

theorem tailTrace_2477418 : CollatzResearch.WordTrace tailWord_2477418 prefixEnd_2477418 282690270244554072084793 := by
  unfold tailWord_2477418
  simp only [CollatzResearch.WordTrace]
  refine ⟨22589714434686292538514227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60239238492496780102704605 22589714434686292538514227)
  ·
    refine ⟨33884571652029438807771341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22589714434686292538514227 33884571652029438807771341)
    ·
      refine ⟨12706714369511039552914253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33884571652029438807771341 12706714369511039552914253)
      ·
        refine ⟨4765017888566639832342845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12706714369511039552914253 4765017888566639832342845)
        ·
          refine ⟨1786881708212489937128567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4765017888566639832342845 1786881708212489937128567)
          ·
            refine ⟨2680322562318734905692851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1786881708212489937128567 2680322562318734905692851)
            ·
              refine ⟨4020483843478102358539277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2680322562318734905692851 4020483843478102358539277)
              ·
                refine ⟨1507681441304288384452229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4020483843478102358539277 1507681441304288384452229)
                ·
                  refine ⟨282690270244554072084793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1507681441304288384452229 282690270244554072084793)
                  ·
                    rfl

theorem cell22_2477418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 3, 4].length) (baseStart_2477418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2477418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2477418 prefixEnd_2477418 := by exact prefixLift 2477418
  have htrace : WordTrace (prefixWord ++ tailWord_2477418) baseStart_2477418 baseEnd_2477418 := by
    simpa [prefixWord, tailWord_2477418, baseEnd_2477418] using wordTrace_append hprefix tailTrace_2477418
  have hstable : (prefixWord ++ tailWord_2477418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2477418).length < 2 ^ (prefixWord ++ tailWord_2477418).sum := by decide
  have hdescent : baseEnd_2477418 < baseStart_2477418 := by decide
  rcases family_descends (prefixWord ++ tailWord_2477418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2477429 : List Nat := [1, 3, 4, 1, 4, 1, 8]
def baseStart_2477429 : Nat := 118140960795 + 2477429 * 2 ^ 59
def prefixEnd_2477429 : Nat := 4983230072969 + 3 ^ 40 * 2477429 * 2
def baseEnd_2477429 : Nat := 31410169491054142749235

theorem tailTrace_2477429 : CollatzResearch.WordTrace tailWord_2477429 prefixEnd_2477429 31410169491054142749235 := by
  unfold tailWord_2477429
  simp only [CollatzResearch.WordTrace]
  refine ⟨90359258941705319032707341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60239505961136879355138227 90359258941705319032707341)
  ·
    refine ⟨33884722103139494637265253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90359258941705319032707341 33884722103139494637265253)
    ·
      refine ⟨6353385394338655244487235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33884722103139494637265253 6353385394338655244487235)
      ·
        refine ⟨9530078091507982866730853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6353385394338655244487235 9530078091507982866730853)
        ·
          refine ⟨1786889642157746787512035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9530078091507982866730853 1786889642157746787512035)
          ·
            refine ⟨2680334463236620181268053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1786889642157746787512035 2680334463236620181268053)
            ·
              refine ⟨31410169491054142749235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2680334463236620181268053 31410169491054142749235)
              ·
                rfl

theorem cell22_2477429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 8].length) (baseStart_2477429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2477429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2477429 prefixEnd_2477429 := by exact prefixLift 2477429
  have htrace : WordTrace (prefixWord ++ tailWord_2477429) baseStart_2477429 baseEnd_2477429 := by
    simpa [prefixWord, tailWord_2477429, baseEnd_2477429] using wordTrace_append hprefix tailTrace_2477429
  have hstable : (prefixWord ++ tailWord_2477429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2477429).length < 2 ^ (prefixWord ++ tailWord_2477429).sum := by decide
  have hdescent : baseEnd_2477429 < baseStart_2477429 := by decide
  rcases family_descends (prefixWord ++ tailWord_2477429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2477444 : List Nat := [2, 3, 2, 1, 1, 3, 3, 1, 3, 3]
def baseStart_2477444 : Nat := 118140960795 + 2477444 * 2 ^ 59
def prefixEnd_2477444 : Nat := 4983230072969 + 3 ^ 40 * 2477444 * 2
def baseEnd_2477444 : Nat := 848079711065006815104299

theorem tailTrace_2477444 : CollatzResearch.WordTrace tailWord_2477444 prefixEnd_2477444 848079711065006815104299 := by
  unfold tailWord_2477444
  simp only [CollatzResearch.WordTrace]
  refine ⟨45179903018325488297251693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60239870691100651063002257 45179903018325488297251693)
  ·
    refine ⟨16942463631872058111469385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45179903018325488297251693 16942463631872058111469385)
    ·
      refine ⟨12706847723904043583602039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16942463631872058111469385 12706847723904043583602039)
      ·
        refine ⟨19060271585856065375403059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12706847723904043583602039 19060271585856065375403059)
        ·
          refine ⟨28590407378784098063104589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19060271585856065375403059 28590407378784098063104589)
          ·
            refine ⟨10721402767044036773664221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28590407378784098063104589 10721402767044036773664221)
            ·
              refine ⟨4020526037641513790124083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10721402767044036773664221 4020526037641513790124083)
              ·
                refine ⟨6030789056462270685186125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4020526037641513790124083 6030789056462270685186125)
                ·
                  refine ⟨2261545896173351506944797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6030789056462270685186125 2261545896173351506944797)
                  ·
                    refine ⟨848079711065006815104299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2261545896173351506944797 848079711065006815104299)
                    ·
                      rfl

theorem cell22_2477444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 1, 3, 3].length) (baseStart_2477444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2477444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2477444 prefixEnd_2477444 := by exact prefixLift 2477444
  have htrace : WordTrace (prefixWord ++ tailWord_2477444) baseStart_2477444 baseEnd_2477444 := by
    simpa [prefixWord, tailWord_2477444, baseEnd_2477444] using wordTrace_append hprefix tailTrace_2477444
  have hstable : (prefixWord ++ tailWord_2477444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2477444).length < 2 ^ (prefixWord ++ tailWord_2477444).sum := by decide
  have hdescent : baseEnd_2477444 < baseStart_2477444 := by decide
  rcases family_descends (prefixWord ++ tailWord_2477444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2477487 : List Nat := [1, 1, 2, 1, 2, 2, 1, 7, 1, 4]
def baseStart_2477487 : Nat := 118140960795 + 2477487 * 2 ^ 59
def prefixEnd_2477487 : Nat := 4983230072969 + 3 ^ 40 * 2477487 * 2
def baseEnd_2477487 : Nat := 848094430843769036279167

theorem tailTrace_2477487 : CollatzResearch.WordTrace tailWord_2477487 prefixEnd_2477487 848094430843769036279167 := by
  unfold tailWord_2477487
  simp only [CollatzResearch.WordTrace]
  refine ⟨90361374375495194938318715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60240916250330129958879143 90361374375495194938318715)
  ·
    refine ⟨135542061563242792407478073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90361374375495194938318715 135542061563242792407478073)
    ·
      refine ⟨101656546172432094305608555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135542061563242792407478073 101656546172432094305608555)
      ·
        refine ⟨152484819258648141458412833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101656546172432094305608555 152484819258648141458412833)
        ·
          refine ⟨114363614443986106093809625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152484819258648141458412833 114363614443986106093809625)
          ·
            refine ⟨85772710832989579570357219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114363614443986106093809625 85772710832989579570357219)
            ·
              refine ⟨128659066249484369355535829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85772710832989579570357219 128659066249484369355535829)
              ·
                refine ⟨3015446865222289906770371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 128659066249484369355535829 3015446865222289906770371)
                ·
                  refine ⟨4523170297833434860155557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3015446865222289906770371 4523170297833434860155557)
                  ·
                    refine ⟨848094430843769036279167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4523170297833434860155557 848094430843769036279167)
                    ·
                      rfl

theorem cell22_2477487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 7, 1, 4].length) (baseStart_2477487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2477487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2477487 prefixEnd_2477487 := by exact prefixLift 2477487
  have htrace : WordTrace (prefixWord ++ tailWord_2477487) baseStart_2477487 baseEnd_2477487 := by
    simpa [prefixWord, tailWord_2477487, baseEnd_2477487] using wordTrace_append hprefix tailTrace_2477487
  have hstable : (prefixWord ++ tailWord_2477487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2477487).length < 2 ^ (prefixWord ++ tailWord_2477487).sum := by decide
  have hdescent : baseEnd_2477487 < baseStart_2477487 := by decide
  rcases family_descends (prefixWord ++ tailWord_2477487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2477502 : List Nat := [4, 2, 1, 1, 1, 1, 1, 5, 6]
def baseStart_2477502 : Nat := 118140960795 + 2477502 * 2 ^ 59
def prefixEnd_2477502 : Nat := 4983230072969 + 3 ^ 40 * 2477502 * 2
def baseEnd_2477502 : Nat := 282699855216771332384707

theorem tailTrace_2477502 : CollatzResearch.WordTrace tailWord_2477502 prefixEnd_2477502 282699855216771332384707 := by
  unfold tailWord_2477502
  simp only [CollatzResearch.WordTrace]
  refine ⟨11295240183805106562514345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60241280980293901666743173 11295240183805106562514345)
  ·
    refine ⟨8471430137853829921885759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11295240183805106562514345 8471430137853829921885759)
    ·
      refine ⟨12707145206780744882828639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8471430137853829921885759 12707145206780744882828639)
      ·
        refine ⟨19060717810171117324242959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12707145206780744882828639 19060717810171117324242959)
        ·
          refine ⟨28591076715256675986364439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19060717810171117324242959 28591076715256675986364439)
          ·
            refine ⟨42886615072885013979546659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28591076715256675986364439 42886615072885013979546659)
            ·
              refine ⟨64329922609327520969319989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42886615072885013979546659 64329922609327520969319989)
              ·
                refine ⟨6030930244624455090873749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 64329922609327520969319989 6030930244624455090873749)
                ·
                  refine ⟨282699855216771332384707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6030930244624455090873749 282699855216771332384707)
                  ·
                    rfl

theorem cell22_2477502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 5, 6].length) (baseStart_2477502 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2477502 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2477502 prefixEnd_2477502 := by exact prefixLift 2477502
  have htrace : WordTrace (prefixWord ++ tailWord_2477502) baseStart_2477502 baseEnd_2477502 := by
    simpa [prefixWord, tailWord_2477502, baseEnd_2477502] using wordTrace_append hprefix tailTrace_2477502
  have hstable : (prefixWord ++ tailWord_2477502).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2477502).length < 2 ^ (prefixWord ++ tailWord_2477502).sum := by decide
  have hdescent : baseEnd_2477502 < baseStart_2477502 := by decide
  rcases family_descends (prefixWord ++ tailWord_2477502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2477637 : List Nat := [1, 3, 1, 1, 1, 4, 2, 1, 8]
def baseStart_2477637 : Nat := 118140960795 + 2477637 * 2 ^ 59
def prefixEnd_2477637 : Nat := 4983230072969 + 3 ^ 40 * 2477637 * 2
def baseEnd_2477637 : Nat := 282715259636406215009569

theorem tailTrace_2477637 : CollatzResearch.WordTrace tailWord_2477637 prefixEnd_2477637 282715259636406215009569 := by
  unfold tailWord_2477637
  simp only [CollatzResearch.WordTrace]
  refine ⟨90366845324951770556279165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60244563549967847037519443 90366845324951770556279165)
  ·
    refine ⟨33887566996856913958604687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90366845324951770556279165 33887566996856913958604687)
    ·
      refine ⟨50831350495285370937907031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33887566996856913958604687 50831350495285370937907031)
      ·
        refine ⟨76247025742928056406860547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50831350495285370937907031 76247025742928056406860547)
        ·
          refine ⟨114370538614392084610290821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76247025742928056406860547 114370538614392084610290821)
          ·
            refine ⟨21444475990198515864429529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 114370538614392084610290821 21444475990198515864429529)
            ·
              refine ⟨16083356992648886898322147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21444475990198515864429529 16083356992648886898322147)
              ·
                refine ⟨24125035488973330347483221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16083356992648886898322147 24125035488973330347483221)
                ·
                  refine ⟨282715259636406215009569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24125035488973330347483221 282715259636406215009569)
                  ·
                    rfl

theorem cell22_2477637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 1, 8].length) (baseStart_2477637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2477637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2477637 prefixEnd_2477637 := by exact prefixLift 2477637
  have htrace : WordTrace (prefixWord ++ tailWord_2477637) baseStart_2477637 baseEnd_2477637 := by
    simpa [prefixWord, tailWord_2477637, baseEnd_2477637] using wordTrace_append hprefix tailTrace_2477637
  have hstable : (prefixWord ++ tailWord_2477637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2477637).length < 2 ^ (prefixWord ++ tailWord_2477637).sum := by decide
  have hdescent : baseEnd_2477637 < baseStart_2477637 := by decide
  rcases family_descends (prefixWord ++ tailWord_2477637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2477686 : List Nat := [5, 1, 1, 2, 2, 1, 1, 3, 1, 5]
def baseStart_2477686 : Nat := 118140960795 + 2477686 * 2 ^ 59
def prefixEnd_2477686 : Nat := 4983230072969 + 3 ^ 40 * 2477686 * 2
def baseEnd_2477686 : Nat := 848162552610598850553557

theorem tailTrace_2477686 : CollatzResearch.WordTrace tailWord_2477686 prefixEnd_2477686 848162552610598850553557 := by
  unfold tailWord_2477686
  simp only [CollatzResearch.WordTrace]
  refine ⟨5648039531360890745300807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 60245755001182834616541941 5648039531360890745300807)
  ·
    refine ⟨8472059297041336117951211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5648039531360890745300807 8472059297041336117951211)
    ·
      refine ⟨12708088945562004176926817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8472059297041336117951211 12708088945562004176926817)
      ·
        refine ⟨9531066709171503132695113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12708088945562004176926817 9531066709171503132695113)
        ·
          refine ⟨7148300031878627349521335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9531066709171503132695113 7148300031878627349521335)
          ·
            refine ⟨10722450047817941024282003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7148300031878627349521335 10722450047817941024282003)
            ·
              refine ⟨16083675071726911536423005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10722450047817941024282003 16083675071726911536423005)
              ·
                refine ⟨6031378151897591826158627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16083675071726911536423005 6031378151897591826158627)
                ·
                  refine ⟨9047067227846387739237941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6031378151897591826158627 9047067227846387739237941)
                  ·
                    refine ⟨848162552610598850553557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9047067227846387739237941 848162552610598850553557)
                    ·
                      rfl

theorem cell22_2477686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 3, 1, 5].length) (baseStart_2477686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2477686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2477686 prefixEnd_2477686 := by exact prefixLift 2477686
  have htrace : WordTrace (prefixWord ++ tailWord_2477686) baseStart_2477686 baseEnd_2477686 := by
    simpa [prefixWord, tailWord_2477686, baseEnd_2477686] using wordTrace_append hprefix tailTrace_2477686
  have hstable : (prefixWord ++ tailWord_2477686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2477686).length < 2 ^ (prefixWord ++ tailWord_2477686).sum := by decide
  have hdescent : baseEnd_2477686 < baseStart_2477686 := by decide
  rcases family_descends (prefixWord ++ tailWord_2477686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2477716 : List Nat := [2, 4, 2, 2, 2, 1, 9]
def baseStart_2477716 : Nat := 118140960795 + 2477716 * 2 ^ 59
def prefixEnd_2477716 : Nat := 4983230072969 + 3 ^ 40 * 2477716 * 2
def baseEnd_2477716 : Nat := 31413808230506991566795

theorem tailTrace_2477716 : CollatzResearch.WordTrace tailWord_2477716 prefixEnd_2477716 31413808230506991566795 := by
  unfold tailWord_2477716
  simp only [CollatzResearch.WordTrace]
  refine ⟨45184863345832783524202501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60246484461110378032270001 45184863345832783524202501)
  ·
    refine ⟨8472161877343646910787969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45184863345832783524202501 8472161877343646910787969)
    ·
      refine ⟨6354121408007735183090977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8472161877343646910787969 6354121408007735183090977)
      ·
        refine ⟨4765591056005801387318233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6354121408007735183090977 4765591056005801387318233)
        ·
          refine ⟨3574193292004351040488675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4765591056005801387318233 3574193292004351040488675)
          ·
            refine ⟨5361289938006526560733013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3574193292004351040488675 5361289938006526560733013)
            ·
              refine ⟨31413808230506991566795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5361289938006526560733013 31413808230506991566795)
              ·
                rfl

theorem cell22_2477716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 9].length) (baseStart_2477716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2477716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2477716 prefixEnd_2477716 := by exact prefixLift 2477716
  have htrace : WordTrace (prefixWord ++ tailWord_2477716) baseStart_2477716 baseEnd_2477716 := by
    simpa [prefixWord, tailWord_2477716, baseEnd_2477716] using wordTrace_append hprefix tailTrace_2477716
  have hstable : (prefixWord ++ tailWord_2477716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2477716).length < 2 ^ (prefixWord ++ tailWord_2477716).sum := by decide
  have hdescent : baseEnd_2477716 < baseStart_2477716 := by decide
  rcases family_descends (prefixWord ++ tailWord_2477716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2477731 : List Nat := [1, 1, 1, 4, 1, 1, 6, 1, 3, 3]
def baseStart_2477731 : Nat := 118140960795 + 2477731 * 2 ^ 59
def prefixEnd_2477731 : Nat := 4983230072969 + 3 ^ 40 * 2477731 * 2
def baseEnd_2477731 : Nat := 848177957030233733178419

theorem tailTrace_2477731 : CollatzResearch.WordTrace tailWord_2477731 prefixEnd_2477731 848177957030233733178419 := by
  unfold tailWord_2477731
  simp only [CollatzResearch.WordTrace]
  refine ⟨90370273786611224610201047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60246849191074149740134031 90370273786611224610201047)
  ·
    refine ⟨135555410679916836915301571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90370273786611224610201047 135555410679916836915301571)
    ·
      refine ⟨203333116019875255372952357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135555410679916836915301571 203333116019875255372952357)
      ·
        refine ⟨38124959253726610382428567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 203333116019875255372952357 38124959253726610382428567)
        ·
          refine ⟨57187438880589915573642851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38124959253726610382428567 57187438880589915573642851)
          ·
            refine ⟨85781158320884873360464277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57187438880589915573642851 85781158320884873360464277)
            ·
              refine ⟨4020991796291478438771763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 85781158320884873360464277 4020991796291478438771763)
              ·
                refine ⟨6031487694437217658157645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4020991796291478438771763 6031487694437217658157645)
                ·
                  refine ⟨2261807885413956621809117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6031487694437217658157645 2261807885413956621809117)
                  ·
                    refine ⟨848177957030233733178419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2261807885413956621809117 848177957030233733178419)
                    ·
                      rfl

theorem cell22_2477731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 1, 3, 3].length) (baseStart_2477731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2477731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2477731 prefixEnd_2477731 := by exact prefixLift 2477731
  have htrace : WordTrace (prefixWord ++ tailWord_2477731) baseStart_2477731 baseEnd_2477731 := by
    simpa [prefixWord, tailWord_2477731, baseEnd_2477731] using wordTrace_append hprefix tailTrace_2477731
  have hstable : (prefixWord ++ tailWord_2477731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2477731).length < 2 ^ (prefixWord ++ tailWord_2477731).sum := by decide
  have hdescent : baseEnd_2477731 < baseStart_2477731 := by decide
  rcases family_descends (prefixWord ++ tailWord_2477731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2477744 : List Nat := [2, 1, 1, 1, 2, 1, 4, 5, 5]
def baseStart_2477744 : Nat := 118140960795 + 2477744 * 2 ^ 59
def prefixEnd_2477744 : Nat := 4983230072969 + 3 ^ 40 * 2477744 * 2
def baseEnd_2477744 : Nat := 282727469065302010867793

theorem tailTrace_2477744 : CollatzResearch.WordTrace tailWord_2477744 prefixEnd_2477744 282727469065302010867793 := by
  unfold tailWord_2477744
  simp only [CollatzResearch.WordTrace]
  refine ⟨45185373967782063915212143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60247165290376085220282857 45185373967782063915212143)
  ·
    refine ⟨67778060951673095872818215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45185373967782063915212143 67778060951673095872818215)
    ·
      refine ⟨101667091427509643809227323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67778060951673095872818215 101667091427509643809227323)
      ·
        refine ⟨152500637141264465713840985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101667091427509643809227323 152500637141264465713840985)
        ·
          refine ⟨114375477855948349285380739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152500637141264465713840985 114375477855948349285380739)
          ·
            refine ⟨171563216783922523928071109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114375477855948349285380739 171563216783922523928071109)
            ·
              refine ⟨32168103146985473236513333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 171563216783922523928071109 32168103146985473236513333)
              ·
                refine ⟨3015759670029888115923125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32168103146985473236513333 3015759670029888115923125)
                ·
                  refine ⟨282727469065302010867793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3015759670029888115923125 282727469065302010867793)
                  ·
                    rfl

theorem cell22_2477744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 5, 5].length) (baseStart_2477744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2477744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2477744 prefixEnd_2477744 := by exact prefixLift 2477744
  have htrace : WordTrace (prefixWord ++ tailWord_2477744) baseStart_2477744 baseEnd_2477744 := by
    simpa [prefixWord, tailWord_2477744, baseEnd_2477744] using wordTrace_append hprefix tailTrace_2477744
  have hstable : (prefixWord ++ tailWord_2477744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2477744).length < 2 ^ (prefixWord ++ tailWord_2477744).sum := by decide
  have hdescent : baseEnd_2477744 < baseStart_2477744 := by decide
  rcases family_descends (prefixWord ++ tailWord_2477744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2477750 : List Nat := [5, 1, 3, 1, 1, 3, 2, 6]
def baseStart_2477750 : Nat := 118140960795 + 2477750 * 2 ^ 59
def prefixEnd_2477750 : Nat := 4983230072969 + 3 ^ 40 * 2477750 * 2
def baseEnd_2477750 : Nat := 94242717902058224105929

theorem tailTrace_2477750 : CollatzResearch.WordTrace tailWord_2477750 prefixEnd_2477750 94242717902058224105929 := by
  unfold tailWord_2477750
  simp only [CollatzResearch.WordTrace]
  refine ⟨5648185423346399428446419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 60247311182361593903428469 5648185423346399428446419)
  ·
    refine ⟨8472278135019599142669629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5648185423346399428446419 8472278135019599142669629)
    ·
      refine ⟨3177104300632349678501111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8472278135019599142669629 3177104300632349678501111)
      ·
        refine ⟨4765656450948524517751667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3177104300632349678501111 4765656450948524517751667)
        ·
          refine ⟨7148484676422786776627501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4765656450948524517751667 7148484676422786776627501)
          ·
            refine ⟨2680681753658545041235313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7148484676422786776627501 2680681753658545041235313)
            ·
              refine ⟨2010511315243908780926485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2680681753658545041235313 2010511315243908780926485)
              ·
                refine ⟨94242717902058224105929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2010511315243908780926485 94242717902058224105929)
                ·
                  rfl

theorem cell22_2477750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 2, 6].length) (baseStart_2477750 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2477750 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2477750 prefixEnd_2477750 := by exact prefixLift 2477750
  have htrace : WordTrace (prefixWord ++ tailWord_2477750) baseStart_2477750 baseEnd_2477750 := by
    simpa [prefixWord, tailWord_2477750, baseEnd_2477750] using wordTrace_append hprefix tailTrace_2477750
  have hstable : (prefixWord ++ tailWord_2477750).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2477750).length < 2 ^ (prefixWord ++ tailWord_2477750).sum := by decide
  have hdescent : baseEnd_2477750 < baseStart_2477750 := by decide
  rcases family_descends (prefixWord ++ tailWord_2477750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2477795 : List Nat := [1, 1, 1, 7, 2, 2, 2, 1, 5]
def baseStart_2477795 : Nat := 118140960795 + 2477795 * 2 ^ 59
def prefixEnd_2477795 : Nat := 4983230072969 + 3 ^ 40 * 2477795 * 2
def baseEnd_2477795 : Nat := 282733288512719633192741

theorem tailTrace_2477795 : CollatzResearch.WordTrace tailWord_2477795 prefixEnd_2477795 282733288512719633192741 := by
  unfold tailWord_2477795
  simp only [CollatzResearch.WordTrace]
  refine ⟨90372608058379363540530839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60248405372252909027020559 90372608058379363540530839)
  ·
    refine ⟨135558912087569045310796259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90372608058379363540530839 135558912087569045310796259)
    ·
      refine ⟨203338368131353567966194389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135558912087569045310796259 203338368131353567966194389)
      ·
        refine ⟨4765743003078599249207681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 203338368131353567966194389 4765743003078599249207681)
        ·
          refine ⟨3574307252308949436905761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4765743003078599249207681 3574307252308949436905761)
          ·
            refine ⟨2680730439231712077679321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3574307252308949436905761 2680730439231712077679321)
            ·
              refine ⟨2010547829423784058259491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2680730439231712077679321 2010547829423784058259491)
              ·
                refine ⟨3015821744135676087389237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2010547829423784058259491 3015821744135676087389237)
                ·
                  refine ⟨282733288512719633192741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3015821744135676087389237 282733288512719633192741)
                  ·
                    rfl

theorem cell22_2477795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 2, 1, 5].length) (baseStart_2477795 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2477795 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2477795 prefixEnd_2477795 := by exact prefixLift 2477795
  have htrace : WordTrace (prefixWord ++ tailWord_2477795) baseStart_2477795 baseEnd_2477795 := by
    simpa [prefixWord, tailWord_2477795, baseEnd_2477795] using wordTrace_append hprefix tailTrace_2477795
  have hstable : (prefixWord ++ tailWord_2477795).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2477795).length < 2 ^ (prefixWord ++ tailWord_2477795).sum := by decide
  have hdescent : baseEnd_2477795 < baseStart_2477795 := by decide
  rcases family_descends (prefixWord ++ tailWord_2477795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2477821 : List Nat := [1, 4, 1, 1, 1, 1, 2, 4, 4, 3]
def baseStart_2477821 : Nat := 118140960795 + 2477821 * 2 ^ 59
def prefixEnd_2477821 : Nat := 4983230072969 + 3 ^ 40 * 2477821 * 2
def baseEnd_2477821 : Nat := 848208765869503498428143

theorem tailTrace_2477821 : CollatzResearch.WordTrace tailWord_2477821 prefixEnd_2477821 848208765869503498428143 := by
  unfold tailWord_2477821
  simp only [CollatzResearch.WordTrace]
  refine ⟨90373556356285169980977317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60249037570856779987318211 90373556356285169980977317)
  ·
    refine ⟨16945041816803469371433247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90373556356285169980977317 16945041816803469371433247)
    ·
      refine ⟨25417562725205204057149871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16945041816803469371433247 25417562725205204057149871)
      ·
        refine ⟨38126344087807806085724807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25417562725205204057149871 38126344087807806085724807)
        ·
          refine ⟨57189516131711709128587211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38126344087807806085724807 57189516131711709128587211)
          ·
            refine ⟨85784274197567563692880817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57189516131711709128587211 85784274197567563692880817)
            ·
              refine ⟨64338205648175672769660613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85784274197567563692880817 64338205648175672769660613)
              ·
                refine ⟨12063413559032938644311365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64338205648175672769660613 12063413559032938644311365)
                ·
                  refine ⟨2261890042318675995808381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12063413559032938644311365 2261890042318675995808381)
                  ·
                    refine ⟨848208765869503498428143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2261890042318675995808381 848208765869503498428143)
                    ·
                      rfl

theorem cell22_2477821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 4, 4, 3].length) (baseStart_2477821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2477821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2477821 prefixEnd_2477821 := by exact prefixLift 2477821
  have htrace : WordTrace (prefixWord ++ tailWord_2477821) baseStart_2477821 baseEnd_2477821 := by
    simpa [prefixWord, tailWord_2477821, baseEnd_2477821] using wordTrace_append hprefix tailTrace_2477821
  have hstable : (prefixWord ++ tailWord_2477821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2477821).length < 2 ^ (prefixWord ++ tailWord_2477821).sum := by decide
  have hdescent : baseEnd_2477821 < baseStart_2477821 := by decide
  rcases family_descends (prefixWord ++ tailWord_2477821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2477834 : List Nat := [3, 1, 2, 2, 1, 13]
def baseStart_2477834 : Nat := 118140960795 + 2477834 * 2 ^ 59
def prefixEnd_2477834 : Nat := 4983230072969 + 3 ^ 40 * 2477834 * 2
def baseEnd_2477834 : Nat := 10471768099199701208063

theorem tailTrace_2477834 : CollatzResearch.WordTrace tailWord_2477834 prefixEnd_2477834 10471768099199701208063 := by
  unfold tailWord_2477834
  simp only [CollatzResearch.WordTrace]
  refine ⟨22593507626309518300300139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60249353670158715467467037 22593507626309518300300139)
  ·
    refine ⟨33890261439464277450450209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22593507626309518300300139 33890261439464277450450209)
    ·
      refine ⟨25417696079598208087837657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33890261439464277450450209 25417696079598208087837657)
      ·
        refine ⟨19063272059698656065878243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25417696079598208087837657 19063272059698656065878243)
        ·
          refine ⟨28594908089547984098817365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19063272059698656065878243 28594908089547984098817365)
          ·
            refine ⟨10471768099199701208063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 28594908089547984098817365 10471768099199701208063)
            ·
              rfl

theorem cell22_2477834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 13].length) (baseStart_2477834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2477834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2477834 prefixEnd_2477834 := by exact prefixLift 2477834
  have htrace : WordTrace (prefixWord ++ tailWord_2477834) baseStart_2477834 baseEnd_2477834 := by
    simpa [prefixWord, tailWord_2477834, baseEnd_2477834] using wordTrace_append hprefix tailTrace_2477834
  have hstable : (prefixWord ++ tailWord_2477834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2477834).length < 2 ^ (prefixWord ++ tailWord_2477834).sum := by decide
  have hdescent : baseEnd_2477834 < baseStart_2477834 := by decide
  rcases family_descends (prefixWord ++ tailWord_2477834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2477836 : List Nat := [2, 2, 1, 2, 2, 1, 4, 2, 2, 4]
def baseStart_2477836 : Nat := 118140960795 + 2477836 * 2 ^ 59
def prefixEnd_2477836 : Nat := 4983230072969 + 3 ^ 40 * 2477836 * 2
def baseEnd_2477836 : Nat := 848213900676048459303097

theorem tailTrace_2477836 : CollatzResearch.WordTrace tailWord_2477836 prefixEnd_2477836 848213900676048459303097 := by
  unfold tailWord_2477836
  simp only [CollatzResearch.WordTrace]
  refine ⟨45187051725615413771386681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60249402300820551695182241 45187051725615413771386681)
  ·
    refine ⟨33890288794211560328540011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45187051725615413771386681 33890288794211560328540011)
    ·
      refine ⟨50835433191317340492810017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33890288794211560328540011 50835433191317340492810017)
      ·
        refine ⟨38126574893488005369607513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50835433191317340492810017 38126574893488005369607513)
        ·
          refine ⟨28594931170116004027205635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38126574893488005369607513 28594931170116004027205635)
          ·
            refine ⟨42892396755174006040808453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28594931170116004027205635 42892396755174006040808453)
            ·
              refine ⟨8042324391595126132651585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42892396755174006040808453 8042324391595126132651585)
              ·
                refine ⟨6031743293696344599488689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8042324391595126132651585 6031743293696344599488689)
                ·
                  refine ⟨4523807470272258449616517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6031743293696344599488689 4523807470272258449616517)
                  ·
                    refine ⟨848213900676048459303097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4523807470272258449616517 848213900676048459303097)
                    ·
                      rfl

theorem cell22_2477836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 2, 2, 4].length) (baseStart_2477836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2477836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2477836 prefixEnd_2477836 := by exact prefixLift 2477836
  have htrace : WordTrace (prefixWord ++ tailWord_2477836) baseStart_2477836 baseEnd_2477836 := by
    simpa [prefixWord, tailWord_2477836, baseEnd_2477836] using wordTrace_append hprefix tailTrace_2477836
  have hstable : (prefixWord ++ tailWord_2477836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2477836).length < 2 ^ (prefixWord ++ tailWord_2477836).sum := by decide
  have hdescent : baseEnd_2477836 < baseStart_2477836 := by decide
  rcases family_descends (prefixWord ++ tailWord_2477836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2477838 : List Nat := [4, 1, 1, 2, 1, 1, 3, 4, 2, 3]
def baseStart_2477838 : Nat := 118140960795 + 2477838 * 2 ^ 59
def prefixEnd_2477838 : Nat := 4983230072969 + 3 ^ 40 * 2477838 * 2
def baseEnd_2477838 : Nat := 848214585316921120753091

theorem tailTrace_2477838 : CollatzResearch.WordTrace tailWord_2477838 prefixEnd_2477838 848214585316921120753091 := by
  unfold tailWord_2477838
  simp only [CollatzResearch.WordTrace]
  refine ⟨11296772049652947735543271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60249450931482387922897445 11296772049652947735543271)
  ·
    refine ⟨16945158074479421603314907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11296772049652947735543271 16945158074479421603314907)
    ·
      refine ⟨25417737111719132404972361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16945158074479421603314907 25417737111719132404972361)
      ·
        refine ⟨19063302833789349303729271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25417737111719132404972361 19063302833789349303729271)
        ·
          refine ⟨28594954250684023955593907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19063302833789349303729271 28594954250684023955593907)
          ·
            refine ⟨42892431376026035933390861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28594954250684023955593907 42892431376026035933390861)
            ·
              refine ⟨16084661766009763475021573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42892431376026035933390861 16084661766009763475021573)
              ·
                refine ⟨3015874081126830651566545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16084661766009763475021573 3015874081126830651566545)
                ·
                  refine ⟨2261905560845122988674909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3015874081126830651566545 2261905560845122988674909)
                  ·
                    refine ⟨848214585316921120753091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2261905560845122988674909 848214585316921120753091)
                    ·
                      rfl

theorem cell22_2477838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 4, 2, 3].length) (baseStart_2477838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2477838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2477838 prefixEnd_2477838 := by exact prefixLift 2477838
  have htrace : WordTrace (prefixWord ++ tailWord_2477838) baseStart_2477838 baseEnd_2477838 := by
    simpa [prefixWord, tailWord_2477838, baseEnd_2477838] using wordTrace_append hprefix tailTrace_2477838
  have hstable : (prefixWord ++ tailWord_2477838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2477838).length < 2 ^ (prefixWord ++ tailWord_2477838).sum := by decide
  have hdescent : baseEnd_2477838 < baseStart_2477838 := by decide
  rcases family_descends (prefixWord ++ tailWord_2477838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2477896 : List Nat := [2, 1, 3, 1, 1, 5, 1, 1, 7]
def baseStart_2477896 : Nat := 118140960795 + 2477896 * 2 ^ 59
def prefixEnd_2477896 : Nat := 4983230072969 + 3 ^ 40 * 2477896 * 2
def baseEnd_2477896 : Nat := 282744813300742767600971

theorem tailTrace_2477896 : CollatzResearch.WordTrace tailWord_2477896 prefixEnd_2477896 282744813300742767600971 := by
  unfold tailWord_2477896
  simp only [CollatzResearch.WordTrace]
  refine ⟨45188145915506728894978771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60250861220675638526638361 45188145915506728894978771)
  ·
    refine ⟨67782218873260093342468157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45188145915506728894978771 67782218873260093342468157)
    ·
      refine ⟨25418332077472535003425559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67782218873260093342468157 25418332077472535003425559)
      ·
        refine ⟨38127498116208802505138339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25418332077472535003425559 38127498116208802505138339)
        ·
          refine ⟨57191247174313203757707509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38127498116208802505138339 57191247174313203757707509)
          ·
            refine ⟨5361679422591862852285079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 57191247174313203757707509 5361679422591862852285079)
            ·
              refine ⟨8042519133887794278427619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5361679422591862852285079 8042519133887794278427619)
              ·
                refine ⟨12063778700831691417641429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8042519133887794278427619 12063778700831691417641429)
                ·
                  refine ⟨282744813300742767600971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12063778700831691417641429 282744813300742767600971)
                  ·
                    rfl

theorem cell22_2477896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 1, 7].length) (baseStart_2477896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2477896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2477896 prefixEnd_2477896 := by exact prefixLift 2477896
  have htrace : WordTrace (prefixWord ++ tailWord_2477896) baseStart_2477896 baseEnd_2477896 := by
    simpa [prefixWord, tailWord_2477896, baseEnd_2477896] using wordTrace_append hprefix tailTrace_2477896
  have hstable : (prefixWord ++ tailWord_2477896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2477896).length < 2 ^ (prefixWord ++ tailWord_2477896).sum := by decide
  have hdescent : baseEnd_2477896 < baseStart_2477896 := by decide
  rcases family_descends (prefixWord ++ tailWord_2477896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2477900 : List Nat := [2, 2, 1, 3, 4, 1, 2, 1, 3, 3]
def baseStart_2477900 : Nat := 118140960795 + 2477900 * 2 ^ 59
def prefixEnd_2477900 : Nat := 4983230072969 + 3 ^ 40 * 2477900 * 2
def baseEnd_2477900 : Nat := 848235809183973625702901

theorem tailTrace_2477900 : CollatzResearch.WordTrace tailWord_2477900 prefixEnd_2477900 848235809183973625702901 := by
  unfold tailWord_2477900
  simp only [CollatzResearch.WordTrace]
  refine ⟨45188218861499483236551577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60250958481999310982068769 45188218861499483236551577)
  ·
    refine ⟨33891164146124612427413683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45188218861499483236551577 33891164146124612427413683)
    ·
      refine ⟨50836746219186918641120525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33891164146124612427413683 50836746219186918641120525)
      ·
        refine ⟨19063779832195094490420197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50836746219186918641120525 19063779832195094490420197)
        ·
          refine ⟨3574458718536580216953787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19063779832195094490420197 3574458718536580216953787)
          ·
            refine ⟨5361688077804870325430681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3574458718536580216953787 5361688077804870325430681)
            ·
              refine ⟨4021266058353652744073011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5361688077804870325430681 4021266058353652744073011)
              ·
                refine ⟨6031899087530479116109517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4021266058353652744073011 6031899087530479116109517)
                ·
                  refine ⟨2261962157823929668541069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6031899087530479116109517 2261962157823929668541069)
                  ·
                    refine ⟨848235809183973625702901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2261962157823929668541069 848235809183973625702901)
                    ·
                      rfl

theorem cell22_2477900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 1, 3, 3].length) (baseStart_2477900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2477900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2477900 prefixEnd_2477900 := by exact prefixLift 2477900
  have htrace : WordTrace (prefixWord ++ tailWord_2477900) baseStart_2477900 baseEnd_2477900 := by
    simpa [prefixWord, tailWord_2477900, baseEnd_2477900] using wordTrace_append hprefix tailTrace_2477900
  have hstable : (prefixWord ++ tailWord_2477900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2477900).length < 2 ^ (prefixWord ++ tailWord_2477900).sum := by decide
  have hdescent : baseEnd_2477900 < baseStart_2477900 := by decide
  rcases family_descends (prefixWord ++ tailWord_2477900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2477913 : List Nat := [1, 2, 1, 2, 2, 3, 5, 1, 5]
def baseStart_2477913 : Nat := 118140960795 + 2477913 * 2 ^ 59
def prefixEnd_2477913 : Nat := 4983230072969 + 3 ^ 40 * 2477913 * 2
def baseEnd_2477913 : Nat := 282746753116548641709287

theorem tailTrace_2477913 : CollatzResearch.WordTrace tailWord_2477913 prefixEnd_2477913 282746753116548641709287 := by
  unfold tailWord_2477913
  simp only [CollatzResearch.WordTrace]
  refine ⟨90376911871951869693326393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60251274581301246462217595 90376911871951869693326393)
  ·
    refine ⟨67782683903963902269994795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90376911871951869693326393 67782683903963902269994795)
    ·
      refine ⟨101674025855945853404992193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67782683903963902269994795 101674025855945853404992193)
      ·
        refine ⟨76255519391959390053744145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101674025855945853404992193 76255519391959390053744145)
        ·
          refine ⟨57191639543969542540308109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76255519391959390053744145 57191639543969542540308109)
          ·
            refine ⟨21446864828988578452615541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57191639543969542540308109 21446864828988578452615541)
            ·
              refine ⟨2010643577717679229932707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21446864828988578452615541 2010643577717679229932707)
              ·
                refine ⟨3015965366576518844899061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2010643577717679229932707 3015965366576518844899061)
                ·
                  refine ⟨282746753116548641709287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3015965366576518844899061 282746753116548641709287)
                  ·
                    rfl

theorem cell22_2477913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 5, 1, 5].length) (baseStart_2477913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2477913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2477913 prefixEnd_2477913 := by exact prefixLift 2477913
  have htrace : WordTrace (prefixWord ++ tailWord_2477913) baseStart_2477913 baseEnd_2477913 := by
    simpa [prefixWord, tailWord_2477913, baseEnd_2477913] using wordTrace_append hprefix tailTrace_2477913
  have hstable : (prefixWord ++ tailWord_2477913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2477913).length < 2 ^ (prefixWord ++ tailWord_2477913).sum := by decide
  have hdescent : baseEnd_2477913 < baseStart_2477913 := by decide
  rcases family_descends (prefixWord ++ tailWord_2477913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2477934 : List Nat := [4, 1, 2, 3, 1, 3, 1, 3, 1, 3]
def baseStart_2477934 : Nat := 118140960795 + 2477934 * 2 ^ 59
def prefixEnd_2477934 : Nat := 4983230072969 + 3 ^ 40 * 2477934 * 2
def baseEnd_2477934 : Nat := 848247448078808870352797

theorem tailTrace_2477934 : CollatzResearch.WordTrace tailWord_2477934 prefixEnd_2477934 848247448078808870352797 := by
  unfold tailWord_2477934
  simp only [CollatzResearch.WordTrace]
  refine ⟨11297209725609473784980107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60251785203250526853227237 11297209725609473784980107)
  ·
    refine ⟨16945814588414210677470161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11297209725609473784980107 16945814588414210677470161)
    ·
      refine ⟨12709360941310658008102621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16945814588414210677470161 12709360941310658008102621)
      ·
        refine ⟨4766010352991496753038483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12709360941310658008102621 4766010352991496753038483)
        ·
          refine ⟨7149015529487245129557725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4766010352991496753038483 7149015529487245129557725)
          ·
            refine ⟨2680880823557716923584147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7149015529487245129557725 2680880823557716923584147)
            ·
              refine ⟨4021321235336575385376221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2680880823557716923584147 4021321235336575385376221)
              ·
                refine ⟨1507995463251215769516083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4021321235336575385376221 1507995463251215769516083)
                ·
                  refine ⟨2261993194876823654274125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1507995463251215769516083 2261993194876823654274125)
                  ·
                    refine ⟨848247448078808870352797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2261993194876823654274125 848247448078808870352797)
                    ·
                      rfl

theorem cell22_2477934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 3, 1, 3].length) (baseStart_2477934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2477934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2477934 prefixEnd_2477934 := by exact prefixLift 2477934
  have htrace : WordTrace (prefixWord ++ tailWord_2477934) baseStart_2477934 baseEnd_2477934 := by
    simpa [prefixWord, tailWord_2477934, baseEnd_2477934] using wordTrace_append hprefix tailTrace_2477934
  have hstable : (prefixWord ++ tailWord_2477934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2477934).length < 2 ^ (prefixWord ++ tailWord_2477934).sum := by decide
  have hdescent : baseEnd_2477934 < baseStart_2477934 := by decide
  rcases family_descends (prefixWord ++ tailWord_2477934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2477988 : List Nat := [2, 3, 1, 2, 1, 3, 1, 3, 2, 4]
def baseStart_2477988 : Nat := 118140960795 + 2477988 * 2 ^ 59
def prefixEnd_2477988 : Nat := 4983230072969 + 3 ^ 40 * 2477988 * 2
def baseEnd_2477988 : Nat := 848265933382370729502631

theorem tailTrace_2477988 : CollatzResearch.WordTrace tailWord_2477988 prefixEnd_2477988 848265933382370729502631 := by
  unfold tailWord_2477988
  simp only [CollatzResearch.WordTrace]
  refine ⟨45189823673340078751153309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60253098231120105001537745 45189823673340078751153309)
  ·
    refine ⟨16946183877502529531682491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45189823673340078751153309 16946183877502529531682491)
    ·
      refine ⟨25419275816253794297523737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16946183877502529531682491 25419275816253794297523737)
      ·
        refine ⟨19064456862190345723142803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25419275816253794297523737 19064456862190345723142803)
        ·
          refine ⟨28596685293285518584714205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19064456862190345723142803 28596685293285518584714205)
          ·
            refine ⟨10723756984982069469267827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28596685293285518584714205 10723756984982069469267827)
            ·
              refine ⟨16085635477473104203901741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10723756984982069469267827 16085635477473104203901741)
              ·
                refine ⟨6032113304052414076463153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16085635477473104203901741 6032113304052414076463153)
                ·
                  refine ⟨4524084978039310557347365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6032113304052414076463153 4524084978039310557347365)
                  ·
                    refine ⟨848265933382370729502631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4524084978039310557347365 848265933382370729502631)
                    ·
                      rfl

theorem cell22_2477988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 3, 2, 4].length) (baseStart_2477988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2477988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2477988 prefixEnd_2477988 := by exact prefixLift 2477988
  have htrace : WordTrace (prefixWord ++ tailWord_2477988) baseStart_2477988 baseEnd_2477988 := by
    simpa [prefixWord, tailWord_2477988, baseEnd_2477988] using wordTrace_append hprefix tailTrace_2477988
  have hstable : (prefixWord ++ tailWord_2477988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2477988).length < 2 ^ (prefixWord ++ tailWord_2477988).sum := by decide
  have hdescent : baseEnd_2477988 < baseStart_2477988 := by decide
  rcases family_descends (prefixWord ++ tailWord_2477988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2478016 : List Nat := [2, 1, 1, 2, 3, 2, 1, 1, 1, 8]
def baseStart_2478016 : Nat := 118140960795 + 2478016 * 2 ^ 59
def prefixEnd_2478016 : Nat := 4983230072969 + 3 ^ 40 * 2478016 * 2
def baseEnd_2478016 : Nat := 848275518354587989802545

theorem tailTrace_2478016 : CollatzResearch.WordTrace tailWord_2478016 prefixEnd_2478016 848275518354587989802545 := by
  unfold tailWord_2478016
  simp only [CollatzResearch.WordTrace]
  refine ⟨45190334295289359142162951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60253779060385812189550601 45190334295289359142162951)
  ·
    refine ⟨67785501442934038713244427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45190334295289359142162951 67785501442934038713244427)
    ·
      refine ⟨101678252164401058069866641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67785501442934038713244427 101678252164401058069866641)
      ·
        refine ⟨76258689123300793552399981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101678252164401058069866641 76258689123300793552399981)
        ·
          refine ⟨28597008421237797582149993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76258689123300793552399981 28597008421237797582149993)
          ·
            refine ⟨21447756315928348186612495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28597008421237797582149993 21447756315928348186612495)
            ·
              refine ⟨32171634473892522279918743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21447756315928348186612495 32171634473892522279918743)
              ·
                refine ⟨48257451710838783419878115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32171634473892522279918743 48257451710838783419878115)
                ·
                  refine ⟨72386177566258175129817173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48257451710838783419878115 72386177566258175129817173)
                  ·
                    refine ⟨848275518354587989802545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 72386177566258175129817173 848275518354587989802545)
                    ·
                      rfl

theorem cell22_2478016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 1, 8].length) (baseStart_2478016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2478016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2478016 prefixEnd_2478016 := by exact prefixLift 2478016
  have htrace : WordTrace (prefixWord ++ tailWord_2478016) baseStart_2478016 baseEnd_2478016 := by
    simpa [prefixWord, tailWord_2478016, baseEnd_2478016] using wordTrace_append hprefix tailTrace_2478016
  have hstable : (prefixWord ++ tailWord_2478016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2478016).length < 2 ^ (prefixWord ++ tailWord_2478016).sum := by decide
  have hdescent : baseEnd_2478016 < baseStart_2478016 := by decide
  rcases family_descends (prefixWord ++ tailWord_2478016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2478052 : List Nat := [2, 3, 1, 1, 1, 1, 6, 3, 1, 3]
def baseStart_2478052 : Nat := 118140960795 + 2478052 * 2 ^ 59
def prefixEnd_2478052 : Nat := 4983230072969 + 3 ^ 40 * 2478052 * 2
def baseEnd_2478052 : Nat := 848287841890295895902435

theorem tailTrace_2478052 : CollatzResearch.WordTrace tailWord_2478052 prefixEnd_2478052 848287841890295895902435 := by
  unfold tailWord_2478052
  simp only [CollatzResearch.WordTrace]
  refine ⟨45190990809224148216318205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60254654412298864288424273 45190990809224148216318205)
  ·
    refine ⟨16946621553459055581119327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45190990809224148216318205 16946621553459055581119327)
    ·
      refine ⟨25419932330188583371678991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16946621553459055581119327 25419932330188583371678991)
      ·
        refine ⟨38129898495282875057518487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25419932330188583371678991 38129898495282875057518487)
        ·
          refine ⟨57194847742924312586277731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38129898495282875057518487 57194847742924312586277731)
          ·
            refine ⟨85792271614386468879416597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57194847742924312586277731 85792271614386468879416597)
            ·
              refine ⟨4021512731924365728722653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 85792271614386468879416597 4021512731924365728722653)
              ·
                refine ⟨1508067274471637148270995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4021512731924365728722653 1508067274471637148270995)
                ·
                  refine ⟨2262100911707455722406493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1508067274471637148270995 2262100911707455722406493)
                  ·
                    refine ⟨848287841890295895902435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2262100911707455722406493 848287841890295895902435)
                    ·
                      rfl

theorem cell22_2478052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 3, 1, 3].length) (baseStart_2478052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2478052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2478052 prefixEnd_2478052 := by exact prefixLift 2478052
  have htrace : WordTrace (prefixWord ++ tailWord_2478052) baseStart_2478052 baseEnd_2478052 := by
    simpa [prefixWord, tailWord_2478052, baseEnd_2478052] using wordTrace_append hprefix tailTrace_2478052
  have hstable : (prefixWord ++ tailWord_2478052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2478052).length < 2 ^ (prefixWord ++ tailWord_2478052).sum := by decide
  have hdescent : baseEnd_2478052 < baseStart_2478052 := by decide
  rcases family_descends (prefixWord ++ tailWord_2478052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2478157 : List Nat := [1, 6, 1, 1, 1, 1, 4, 1, 2, 4]
def baseStart_2478157 : Nat := 118140960795 + 2478157 * 2 ^ 59
def prefixEnd_2478157 : Nat := 4983230072969 + 3 ^ 40 * 2478157 * 2
def baseEnd_2478157 : Nat := 848323785536110622027113

theorem tailTrace_2478157 : CollatzResearch.WordTrace tailWord_2478157 prefixEnd_2478157 848323785536110622027113 := by
  unfold tailWord_2478157
  simp only [CollatzResearch.WordTrace]
  refine ⟨90385811283067899365208725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60257207522045266243472483 90385811283067899365208725)
  ·
    refine ⟨4236834903893807782744159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 90385811283067899365208725 4236834903893807782744159)
    ·
      refine ⟨6355252355840711674116239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4236834903893807782744159 6355252355840711674116239)
      ·
        refine ⟨9532878533761067511174359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6355252355840711674116239 9532878533761067511174359)
        ·
          refine ⟨14299317800641601266761539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9532878533761067511174359 14299317800641601266761539)
          ·
            refine ⟨21448976700962401900142309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14299317800641601266761539 21448976700962401900142309)
            ·
              refine ⟨4021683131430450356276683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21448976700962401900142309 4021683131430450356276683)
              ·
                refine ⟨6032524697145675534415025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4021683131430450356276683 6032524697145675534415025)
                ·
                  refine ⟨4524393522859256650811269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6032524697145675534415025 4524393522859256650811269)
                  ·
                    refine ⟨848323785536110622027113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4524393522859256650811269 848323785536110622027113)
                    ·
                      rfl

theorem cell22_2478157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_2478157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2478157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2478157 prefixEnd_2478157 := by exact prefixLift 2478157
  have htrace : WordTrace (prefixWord ++ tailWord_2478157) baseStart_2478157 baseEnd_2478157 := by
    simpa [prefixWord, tailWord_2478157, baseEnd_2478157] using wordTrace_append hprefix tailTrace_2478157
  have hstable : (prefixWord ++ tailWord_2478157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2478157).length < 2 ^ (prefixWord ++ tailWord_2478157).sum := by decide
  have hdescent : baseEnd_2478157 < baseStart_2478157 := by decide
  rcases family_descends (prefixWord ++ tailWord_2478157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2478178 : List Nat := [3, 3, 2, 2, 3, 1, 2, 2, 4]
def baseStart_2478178 : Nat := 118140960795 + 2478178 * 2 ^ 59
def prefixEnd_2478178 : Nat := 4983230072969 + 3 ^ 40 * 2478178 * 2
def baseEnd_2478178 : Nat := 282776991421757855750683

theorem tailTrace_2478178 : CollatzResearch.WordTrace tailWord_2478178 prefixEnd_2478178 282776991421757855750683 := by
  unfold tailWord_2478178
  simp only [CollatzResearch.WordTrace]
  refine ⟨22596644303997954987930797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60257718143994546634482125 22596644303997954987930797)
  ·
    refine ⟨8473741613999233120474049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22596644303997954987930797 8473741613999233120474049)
    ·
      refine ⟨6355306210499424840355537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8473741613999233120474049 6355306210499424840355537)
      ·
        refine ⟨4766479657874568630266653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6355306210499424840355537 4766479657874568630266653)
        ·
          refine ⟨1787429871702963236349995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4766479657874568630266653 1787429871702963236349995)
          ·
            refine ⟨2681144807554444854524993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1787429871702963236349995 2681144807554444854524993)
            ·
              refine ⟨2010858605665833640893745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2681144807554444854524993 2010858605665833640893745)
              ·
                refine ⟨1508143954249375230670309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2010858605665833640893745 1508143954249375230670309)
                ·
                  refine ⟨282776991421757855750683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1508143954249375230670309 282776991421757855750683)
                  ·
                    rfl

theorem cell22_2478178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 2, 2, 4].length) (baseStart_2478178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2478178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2478178 prefixEnd_2478178 := by exact prefixLift 2478178
  have htrace : WordTrace (prefixWord ++ tailWord_2478178) baseStart_2478178 baseEnd_2478178 := by
    simpa [prefixWord, tailWord_2478178, baseEnd_2478178] using wordTrace_append hprefix tailTrace_2478178
  have hstable : (prefixWord ++ tailWord_2478178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2478178).length < 2 ^ (prefixWord ++ tailWord_2478178).sum := by decide
  have hdescent : baseEnd_2478178 < baseStart_2478178 := by decide
  rcases family_descends (prefixWord ++ tailWord_2478178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2478234 : List Nat := [3, 1, 1, 5, 2, 2, 1, 2, 5]
def baseStart_2478234 : Nat := 118140960795 + 2478234 * 2 ^ 59
def prefixEnd_2478234 : Nat := 4983230072969 + 3 ^ 40 * 2478234 * 2
def baseEnd_2478234 : Nat := 282783381403236029283959

theorem tailTrace_2478234 : CollatzResearch.WordTrace tailWord_2478234 prefixEnd_2478234 282783381403236029283959 := by
  unfold tailWord_2478234
  simp only [CollatzResearch.WordTrace]
  refine ⟨22597154925947235378940439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60259079802525961010507837 22597154925947235378940439)
  ·
    refine ⟨33895732388920853068410659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22597154925947235378940439 33895732388920853068410659)
    ·
      refine ⟨50843598583381279602615989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33895732388920853068410659 50843598583381279602615989)
      ·
        refine ⟨4766587367191994962745249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 50843598583381279602615989 4766587367191994962745249)
        ·
          refine ⟨3574940525393996222058937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4766587367191994962745249 3574940525393996222058937)
          ·
            refine ⟨2681205394045497166544203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3574940525393996222058937 2681205394045497166544203)
            ·
              refine ⟨4021808091068245749816305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2681205394045497166544203 4021808091068245749816305)
              ·
                refine ⟨3016356068301184312362229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4021808091068245749816305 3016356068301184312362229)
                ·
                  refine ⟨282783381403236029283959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3016356068301184312362229 282783381403236029283959)
                  ·
                    rfl

theorem cell22_2478234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 2, 5].length) (baseStart_2478234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2478234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2478234 prefixEnd_2478234 := by exact prefixLift 2478234
  have htrace : WordTrace (prefixWord ++ tailWord_2478234) baseStart_2478234 baseEnd_2478234 := by
    simpa [prefixWord, tailWord_2478234, baseEnd_2478234] using wordTrace_append hprefix tailTrace_2478234
  have hstable : (prefixWord ++ tailWord_2478234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2478234).length < 2 ^ (prefixWord ++ tailWord_2478234).sum := by decide
  have hdescent : baseEnd_2478234 < baseStart_2478234 := by decide
  rcases family_descends (prefixWord ++ tailWord_2478234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2478243 : List Nat := [1, 1, 1, 4, 1, 1, 1, 1, 2, 9]
def baseStart_2478243 : Nat := 118140960795 + 2478243 * 2 ^ 59
def prefixEnd_2478243 : Nat := 4983230072969 + 3 ^ 40 * 2478243 * 2
def baseEnd_2478243 : Nat := 848353225093635064376849

theorem tailTrace_2478243 : CollatzResearch.WordTrace tailWord_2478243 prefixEnd_2478243 848353225093635064376849 := by
  unfold tailWord_2478243
  simp only [CollatzResearch.WordTrace]
  refine ⟨90388947960756336052839383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60259298640504224035226255 90388947960756336052839383)
  ·
    refine ⟨135583421941134504079259075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90388947960756336052839383 135583421941134504079259075)
    ·
      refine ⟨203375132911701756118888613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135583421941134504079259075 203375132911701756118888613)
      ·
        refine ⟨38132837420944079272291615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 203375132911701756118888613 38132837420944079272291615)
        ·
          refine ⟨57199256131416118908437423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38132837420944079272291615 57199256131416118908437423)
          ·
            refine ⟨85798884197124178362656135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57199256131416118908437423 85798884197124178362656135)
            ·
              refine ⟨128698326295686267543984203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85798884197124178362656135 128698326295686267543984203)
              ·
                refine ⟨193047489443529401315976305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 128698326295686267543984203 193047489443529401315976305)
                ·
                  refine ⟨144785617082647050986982229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 193047489443529401315976305 144785617082647050986982229)
                  ·
                    refine ⟨848353225093635064376849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 144785617082647050986982229 848353225093635064376849)
                    ·
                      rfl

theorem cell22_2478243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 9].length) (baseStart_2478243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2478243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2478243 prefixEnd_2478243 := by exact prefixLift 2478243
  have htrace : WordTrace (prefixWord ++ tailWord_2478243) baseStart_2478243 baseEnd_2478243 := by
    simpa [prefixWord, tailWord_2478243, baseEnd_2478243] using wordTrace_append hprefix tailTrace_2478243
  have hstable : (prefixWord ++ tailWord_2478243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2478243).length < 2 ^ (prefixWord ++ tailWord_2478243).sum := by decide
  have hdescent : baseEnd_2478243 < baseStart_2478243 := by decide
  rcases family_descends (prefixWord ++ tailWord_2478243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2478245 : List Nat := [1, 3, 1, 2, 1, 3, 4, 1, 6]
def baseStart_2478245 : Nat := 118140960795 + 2478245 * 2 ^ 59
def prefixEnd_2478245 : Nat := 4983230072969 + 3 ^ 40 * 2478245 * 2
def baseEnd_2478245 : Nat := 282784636578169241942281

theorem tailTrace_2478245 : CollatzResearch.WordTrace tailWord_2478245 prefixEnd_2478245 282784636578169241942281 := by
  unfold tailWord_2478245
  simp only [CollatzResearch.WordTrace]
  refine ⟨90389020906749090394412189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60259347271166060262941459 90389020906749090394412189)
  ·
    refine ⟨33895882840030908897904571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90389020906749090394412189 33895882840030908897904571)
    ·
      refine ⟨50843824260046363346856857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33895882840030908897904571 50843824260046363346856857)
      ·
        refine ⟨38132868195034772510142643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50843824260046363346856857 38132868195034772510142643)
        ·
          refine ⟨57199302292552158765213965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38132868195034772510142643 57199302292552158765213965)
          ·
            refine ⟨21449738359707059536955237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57199302292552158765213965 21449738359707059536955237)
            ·
              refine ⟨4021825942445073663179107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21449738359707059536955237 4021825942445073663179107)
              ·
                refine ⟨6032738913667610494768661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4021825942445073663179107 6032738913667610494768661)
                ·
                  refine ⟨282784636578169241942281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6032738913667610494768661 282784636578169241942281)
                  ·
                    rfl

theorem cell22_2478245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 1, 6].length) (baseStart_2478245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2478245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2478245 prefixEnd_2478245 := by exact prefixLift 2478245
  have htrace : WordTrace (prefixWord ++ tailWord_2478245) baseStart_2478245 baseEnd_2478245 := by
    simpa [prefixWord, tailWord_2478245, baseEnd_2478245] using wordTrace_append hprefix tailTrace_2478245
  have hstable : (prefixWord ++ tailWord_2478245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2478245).length < 2 ^ (prefixWord ++ tailWord_2478245).sum := by decide
  have hdescent : baseEnd_2478245 < baseStart_2478245 := by decide
  rcases family_descends (prefixWord ++ tailWord_2478245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2478290 : List Nat := [3, 2, 2, 2, 1, 2, 10]
def baseStart_2478290 : Nat := 118140960795 + 2478290 * 2 ^ 59
def prefixEnd_2478290 : Nat := 4983230072969 + 3 ^ 40 * 2478290 * 2
def baseEnd_2478290 : Nat := 31421085709412689201915

theorem tailTrace_2478290 : CollatzResearch.WordTrace tailWord_2478290 prefixEnd_2478290 31421085709412689201915 := by
  unfold tailWord_2478290
  simp only [CollatzResearch.WordTrace]
  refine ⟨22597665547896515769950081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60260441461057375386533549 22597665547896515769950081)
  ·
    refine ⟨16948249160922386827462561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22597665547896515769950081 16948249160922386827462561)
    ·
      refine ⟨12711186870691790120596921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16948249160922386827462561 12711186870691790120596921)
      ·
        refine ⟨9533390153018842590447691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12711186870691790120596921 9533390153018842590447691)
        ·
          refine ⟨14300085229528263885671537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9533390153018842590447691 14300085229528263885671537)
          ·
            refine ⟨10725063922146197914253653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14300085229528263885671537 10725063922146197914253653)
            ·
              refine ⟨31421085709412689201915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 10725063922146197914253653 31421085709412689201915)
              ·
                rfl

theorem cell22_2478290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 10].length) (baseStart_2478290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2478290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2478290 prefixEnd_2478290 := by exact prefixLift 2478290
  have htrace : WordTrace (prefixWord ++ tailWord_2478290) baseStart_2478290 baseEnd_2478290 := by
    simpa [prefixWord, tailWord_2478290, baseEnd_2478290] using wordTrace_append hprefix tailTrace_2478290
  have hstable : (prefixWord ++ tailWord_2478290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2478290).length < 2 ^ (prefixWord ++ tailWord_2478290).sum := by decide
  have hdescent : baseEnd_2478290 < baseStart_2478290 := by decide
  rcases family_descends (prefixWord ++ tailWord_2478290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2478311 : List Nat := [1, 1, 5, 3, 1, 1, 4, 1, 2, 3]
def baseStart_2478311 : Nat := 118140960795 + 2478311 * 2 ^ 59
def prefixEnd_2478311 : Nat := 4983230072969 + 3 ^ 40 * 2478311 * 2
def baseEnd_2478311 : Nat := 848376502883305553676641

theorem tailTrace_2478311 : CollatzResearch.WordTrace tailWord_2478311 prefixEnd_2478311 848376502883305553676641 := by
  unfold tailWord_2478311
  simp only [CollatzResearch.WordTrace]
  refine ⟨90391428124509983666314787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60260952083006655777543191 90391428124509983666314787)
  ·
    refine ⟨135587142186764975499472181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90391428124509983666314787 135587142186764975499472181)
    ·
      refine ⟨12711294580009216453075517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 135587142186764975499472181 12711294580009216453075517)
      ·
        refine ⟨4766735467503456169903319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12711294580009216453075517 4766735467503456169903319)
        ·
          refine ⟨7150103201255184254854979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4766735467503456169903319 7150103201255184254854979)
          ·
            refine ⟨10725154801882776382282469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7150103201255184254854979 10725154801882776382282469)
            ·
              refine ⟨2010966525353020571677963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10725154801882776382282469 2010966525353020571677963)
              ·
                refine ⟨3016449788029530857516945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2010966525353020571677963 3016449788029530857516945)
                ·
                  refine ⟨2262337341022148143137709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3016449788029530857516945 2262337341022148143137709)
                  ·
                    refine ⟨848376502883305553676641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2262337341022148143137709 848376502883305553676641)
                    ·
                      rfl

theorem cell22_2478311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 4, 1, 2, 3].length) (baseStart_2478311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2478311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2478311 prefixEnd_2478311 := by exact prefixLift 2478311
  have htrace : WordTrace (prefixWord ++ tailWord_2478311) baseStart_2478311 baseEnd_2478311 := by
    simpa [prefixWord, tailWord_2478311, baseEnd_2478311] using wordTrace_append hprefix tailTrace_2478311
  have hstable : (prefixWord ++ tailWord_2478311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2478311).length < 2 ^ (prefixWord ++ tailWord_2478311).sum := by decide
  have hdescent : baseEnd_2478311 < baseStart_2478311 := by decide
  rcases family_descends (prefixWord ++ tailWord_2478311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2478339 : List Nat := [1, 1, 1, 3, 2, 3, 2, 5, 1, 3]
def baseStart_2478339 : Nat := 118140960795 + 2478339 * 2 ^ 59
def prefixEnd_2478339 : Nat := 4983230072969 + 3 ^ 40 * 2478339 * 2
def baseEnd_2478339 : Nat := 848386087855522813976555

theorem tailTrace_2478339 : CollatzResearch.WordTrace tailWord_2478339 prefixEnd_2478339 848386087855522813976555 := by
  unfold tailWord_2478339
  simp only [CollatzResearch.WordTrace]
  refine ⟨90392449368408544448334071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60261632912272362965556047 90392449368408544448334071)
  ·
    refine ⟨135588674052612816672501107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90392449368408544448334071 135588674052612816672501107)
    ·
      refine ⟨203383011078919225008751661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135588674052612816672501107 203383011078919225008751661)
      ·
        refine ⟨76268629154594709378281873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 203383011078919225008751661 76268629154594709378281873)
        ·
          refine ⟨57201471865946032033711405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76268629154594709378281873 57201471865946032033711405)
          ·
            refine ⟨21450551949729762012641777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57201471865946032033711405 21450551949729762012641777)
            ·
              refine ⟨16087913962297321509481333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21450551949729762012641777 16087913962297321509481333)
              ·
                refine ⟨1508241933965373891513875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16087913962297321509481333 1508241933965373891513875)
                ·
                  refine ⟨2262362900948060837270813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1508241933965373891513875 2262362900948060837270813)
                  ·
                    refine ⟨848386087855522813976555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2262362900948060837270813 848386087855522813976555)
                    ·
                      rfl

theorem cell22_2478339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 5, 1, 3].length) (baseStart_2478339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2478339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2478339 prefixEnd_2478339 := by exact prefixLift 2478339
  have htrace : WordTrace (prefixWord ++ tailWord_2478339) baseStart_2478339 baseEnd_2478339 := by
    simpa [prefixWord, tailWord_2478339, baseEnd_2478339] using wordTrace_append hprefix tailTrace_2478339
  have hstable : (prefixWord ++ tailWord_2478339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2478339).length < 2 ^ (prefixWord ++ tailWord_2478339).sum := by decide
  have hdescent : baseEnd_2478339 < baseStart_2478339 := by decide
  rcases family_descends (prefixWord ++ tailWord_2478339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2478367 : List Nat := [1, 1, 2, 4, 3, 2, 1, 1, 2, 5]
def baseStart_2478367 : Nat := 118140960795 + 2478367 * 2 ^ 59
def prefixEnd_2478367 : Nat := 4983230072969 + 3 ^ 40 * 2478367 * 2
def baseEnd_2478367 : Nat := 848395672827740074276469

theorem tailTrace_2478367 : CollatzResearch.WordTrace tailWord_2478367 prefixEnd_2478367 848395672827740074276469 := by
  unfold tailWord_2478367
  simp only [CollatzResearch.WordTrace]
  refine ⟨90393470612307105230353355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60262313741538070153568903 90393470612307105230353355)
  ·
    refine ⟨135590205918460657845530033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90393470612307105230353355 135590205918460657845530033)
    ·
      refine ⟨101692654438845493384147525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135590205918460657845530033 101692654438845493384147525)
      ·
        refine ⟨19067372707283530009527661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 101692654438845493384147525 19067372707283530009527661)
        ·
          refine ⟨7150264765231323753572873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19067372707283530009527661 7150264765231323753572873)
          ·
            refine ⟨5362698573923492815179655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7150264765231323753572873 5362698573923492815179655)
            ·
              refine ⟨8044047860885239222769483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5362698573923492815179655 8044047860885239222769483)
              ·
                refine ⟨12066071791327858834154225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8044047860885239222769483 12066071791327858834154225)
                ·
                  refine ⟨9049553843495894125615669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12066071791327858834154225 9049553843495894125615669)
                  ·
                    refine ⟨848395672827740074276469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9049553843495894125615669 848395672827740074276469)
                    ·
                      rfl

theorem cell22_2478367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 1, 2, 5].length) (baseStart_2478367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2478367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2478367 prefixEnd_2478367 := by exact prefixLift 2478367
  have htrace : WordTrace (prefixWord ++ tailWord_2478367) baseStart_2478367 baseEnd_2478367 := by
    simpa [prefixWord, tailWord_2478367, baseEnd_2478367] using wordTrace_append hprefix tailTrace_2478367
  have hstable : (prefixWord ++ tailWord_2478367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2478367).length < 2 ^ (prefixWord ++ tailWord_2478367).sum := by decide
  have hdescent : baseEnd_2478367 < baseStart_2478367 := by decide
  rcases family_descends (prefixWord ++ tailWord_2478367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2478380 : List Nat := [2, 2, 1, 1, 1, 3, 3, 1, 8]
def baseStart_2478380 : Nat := 118140960795 + 2478380 * 2 ^ 59
def prefixEnd_2478380 : Nat := 4983230072969 + 3 ^ 40 * 2478380 * 2
def baseEnd_2478380 : Nat := 282800040997804124567143

theorem tailTrace_2478380 : CollatzResearch.WordTrace tailWord_2478380 prefixEnd_2478380 282800040997804124567143 := by
  unfold tailWord_2478380
  simp only [CollatzResearch.WordTrace]
  refine ⟨45196972380630004225288297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60262629840840005633717729 45196972380630004225288297)
  ·
    refine ⟨33897729285472503168966223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45196972380630004225288297 33897729285472503168966223)
    ·
      refine ⟨50846593928208754753449335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33897729285472503168966223 50846593928208754753449335)
      ·
        refine ⟨76269890892313132130174003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50846593928208754753449335 76269890892313132130174003)
        ·
          refine ⟨114404836338469698195261005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76269890892313132130174003 114404836338469698195261005)
          ·
            refine ⟨42901813626926136823222877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 114404836338469698195261005 42901813626926136823222877)
            ·
              refine ⟨16088180110097301308708579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42901813626926136823222877 16088180110097301308708579)
              ·
                refine ⟨24132270165145951963062869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16088180110097301308708579 24132270165145951963062869)
                ·
                  refine ⟨282800040997804124567143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24132270165145951963062869 282800040997804124567143)
                  ·
                    rfl

theorem cell22_2478380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 8].length) (baseStart_2478380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2478380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2478380 prefixEnd_2478380 := by exact prefixLift 2478380
  have htrace : WordTrace (prefixWord ++ tailWord_2478380) baseStart_2478380 baseEnd_2478380 := by
    simpa [prefixWord, tailWord_2478380, baseEnd_2478380] using wordTrace_append hprefix tailTrace_2478380
  have hstable : (prefixWord ++ tailWord_2478380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2478380).length < 2 ^ (prefixWord ++ tailWord_2478380).sum := by decide
  have hdescent : baseEnd_2478380 < baseStart_2478380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2478380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2478425 : List Nat := [1, 2, 1, 2, 2, 2, 1, 11]
def baseStart_2478425 : Nat := 118140960795 + 2478425 * 2 ^ 59
def prefixEnd_2478425 : Nat := 4983230072969 + 3 ^ 40 * 2478425 * 2
def baseEnd_2478425 : Nat := 94268391934783028480699

theorem tailTrace_2478425 : CollatzResearch.WordTrace tailWord_2478425 prefixEnd_2478425 94268391934783028480699 := by
  unfold tailWord_2478425
  simp only [CollatzResearch.WordTrace]
  refine ⟨90395586046096981135964729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60263724030731320757309819 90395586046096981135964729)
  ·
    refine ⟨67796689534572735851973547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90395586046096981135964729 67796689534572735851973547)
    ·
      refine ⟨101695034301859103777960321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67796689534572735851973547 101695034301859103777960321)
      ·
        refine ⟨76271275726394327833470241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101695034301859103777960321 76271275726394327833470241)
        ·
          refine ⟨57203456794795745875102681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76271275726394327833470241 57203456794795745875102681)
          ·
            refine ⟨42902592596096809406327011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57203456794795745875102681 42902592596096809406327011)
            ·
              refine ⟨64353888894145214109490517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42902592596096809406327011 64353888894145214109490517)
              ·
                refine ⟨94268391934783028480699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 64353888894145214109490517 94268391934783028480699)
                ·
                  rfl

theorem cell22_2478425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 11].length) (baseStart_2478425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2478425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2478425 prefixEnd_2478425 := by exact prefixLift 2478425
  have htrace : WordTrace (prefixWord ++ tailWord_2478425) baseStart_2478425 baseEnd_2478425 := by
    simpa [prefixWord, tailWord_2478425, baseEnd_2478425] using wordTrace_append hprefix tailTrace_2478425
  have hstable : (prefixWord ++ tailWord_2478425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2478425).length < 2 ^ (prefixWord ++ tailWord_2478425).sum := by decide
  have hdescent : baseEnd_2478425 < baseStart_2478425 := by decide
  rcases family_descends (prefixWord ++ tailWord_2478425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2478472 : List Nat := [2, 1, 3, 3, 1, 1, 2, 1, 2, 6]
def baseStart_2478472 : Nat := 118140960795 + 2478472 * 2 ^ 59
def prefixEnd_2478472 : Nat := 4983230072969 + 3 ^ 40 * 2478472 * 2
def baseEnd_2478472 : Nat := 848431616473554800401147

theorem tailTrace_2478472 : CollatzResearch.WordTrace tailWord_2478472 prefixEnd_2478472 848431616473554800401147 := by
  unfold tailWord_2478472
  simp only [CollatzResearch.WordTrace]
  refine ⟨45198650138463354081462835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60264866851284472108617113 45198650138463354081462835)
  ·
    refine ⟨67797975207695031122194253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45198650138463354081462835 67797975207695031122194253)
    ·
      refine ⟨25424240702885636670822845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67797975207695031122194253 25424240702885636670822845)
      ·
        refine ⟨9534090263582113751558567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25424240702885636670822845 9534090263582113751558567)
        ·
          refine ⟨14301135395373170627337851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9534090263582113751558567 14301135395373170627337851)
          ·
            refine ⟨21451703093059755941006777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14301135395373170627337851 21451703093059755941006777)
            ·
              refine ⟨16088777319794816955755083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21451703093059755941006777 16088777319794816955755083)
              ·
                refine ⟨24133165979692225433632625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16088777319794816955755083 24133165979692225433632625)
                ·
                  refine ⟨18099874484769169075224469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24133165979692225433632625 18099874484769169075224469)
                  ·
                    refine ⟨848431616473554800401147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18099874484769169075224469 848431616473554800401147)
                    ·
                      rfl

theorem cell22_2478472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 1, 2, 6].length) (baseStart_2478472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2478472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2478472 prefixEnd_2478472 := by exact prefixLift 2478472
  have htrace : WordTrace (prefixWord ++ tailWord_2478472) baseStart_2478472 baseEnd_2478472 := by
    simpa [prefixWord, tailWord_2478472, baseEnd_2478472] using wordTrace_append hprefix tailTrace_2478472
  have hstable : (prefixWord ++ tailWord_2478472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2478472).length < 2 ^ (prefixWord ++ tailWord_2478472).sum := by decide
  have hdescent : baseEnd_2478472 < baseStart_2478472 := by decide
  rcases family_descends (prefixWord ++ tailWord_2478472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2478525 : List Nat := [1, 4, 1, 2, 2, 4, 2, 2, 1, 3]
def baseStart_2478525 : Nat := 118140960795 + 2478525 * 2 ^ 59
def prefixEnd_2478525 : Nat := 4983230072969 + 3 ^ 40 * 2478525 * 2
def baseEnd_2478525 : Nat := 848449759456680328825985

theorem tailTrace_2478525 : CollatzResearch.WordTrace tailWord_2478525 prefixEnd_2478525 848449759456680328825985 := by
  unfold tailWord_2478525
  simp only [CollatzResearch.WordTrace]
  refine ⟨90399233345734698214605029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60266155563823132143070019 90399233345734698214605029)
  ·
    refine ⟨16949856252325255915238443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90399233345734698214605029 16949856252325255915238443)
    ·
      refine ⟨25424784378487883872857665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16949856252325255915238443 25424784378487883872857665)
      ·
        refine ⟨19068588283865912904643249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25424784378487883872857665 19068588283865912904643249)
        ·
          refine ⟨14301441212899434678482437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19068588283865912904643249 14301441212899434678482437)
          ·
            refine ⟨2681520227418644002215457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14301441212899434678482437 2681520227418644002215457)
            ·
              refine ⟨2011140170563983001661593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2681520227418644002215457 2011140170563983001661593)
              ·
                refine ⟨1508355127922987251246195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2011140170563983001661593 1508355127922987251246195)
                ·
                  refine ⟨2262532691884480876869293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1508355127922987251246195 2262532691884480876869293)
                  ·
                    refine ⟨848449759456680328825985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2262532691884480876869293 848449759456680328825985)
                    ·
                      rfl

theorem cell22_2478525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 2, 2, 1, 3].length) (baseStart_2478525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2478525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2478525 prefixEnd_2478525 := by exact prefixLift 2478525
  have htrace : WordTrace (prefixWord ++ tailWord_2478525) baseStart_2478525 baseEnd_2478525 := by
    simpa [prefixWord, tailWord_2478525, baseEnd_2478525] using wordTrace_append hprefix tailTrace_2478525
  have hstable : (prefixWord ++ tailWord_2478525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2478525).length < 2 ^ (prefixWord ++ tailWord_2478525).sum := by decide
  have hdescent : baseEnd_2478525 < baseStart_2478525 := by decide
  rcases family_descends (prefixWord ++ tailWord_2478525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2478549 : List Nat := [1, 3, 2, 3, 1, 3, 1, 2, 6]
def baseStart_2478549 : Nat := 118140960795 + 2478549 * 2 ^ 59
def prefixEnd_2478549 : Nat := 4983230072969 + 3 ^ 40 * 2478549 * 2
def baseEnd_2478549 : Nat := 282819325049050755408637

theorem tailTrace_2478549 : CollatzResearch.WordTrace tailWord_2478549 prefixEnd_2478549 282819325049050755408637 := by
  unfold tailWord_2478549
  simp only [CollatzResearch.WordTrace]
  refine ⟨90400108697647750313478701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60266739131765166875652467 90400108697647750313478701)
  ·
    refine ⟨33900040761617906367554513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90400108697647750313478701 33900040761617906367554513)
    ·
      refine ⟨25425030571213429775665885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33900040761617906367554513 25425030571213429775665885)
      ·
        refine ⟨9534386464205036165874707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25425030571213429775665885 9534386464205036165874707)
        ·
          refine ⟨14301579696307554248812061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9534386464205036165874707 14301579696307554248812061)
          ·
            refine ⟨5363092386115332843304523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14301579696307554248812061 5363092386115332843304523)
            ·
              refine ⟨8044638579172999264956785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5363092386115332843304523 8044638579172999264956785)
              ·
                refine ⟨6033478934379749448717589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8044638579172999264956785 6033478934379749448717589)
                ·
                  refine ⟨282819325049050755408637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6033478934379749448717589 282819325049050755408637)
                  ·
                    rfl

theorem cell22_2478549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 2, 6].length) (baseStart_2478549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2478549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2478549 prefixEnd_2478549 := by exact prefixLift 2478549
  have htrace : WordTrace (prefixWord ++ tailWord_2478549) baseStart_2478549 baseEnd_2478549 := by
    simpa [prefixWord, tailWord_2478549, baseEnd_2478549] using wordTrace_append hprefix tailTrace_2478549
  have hstable : (prefixWord ++ tailWord_2478549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2478549).length < 2 ^ (prefixWord ++ tailWord_2478549).sum := by decide
  have hdescent : baseEnd_2478549 < baseStart_2478549 := by decide
  rcases family_descends (prefixWord ++ tailWord_2478549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2478568 : List Nat := [2, 1, 4, 1, 1, 5, 2, 1, 1, 4]
def baseStart_2478568 : Nat := 118140960795 + 2478568 * 2 ^ 59
def prefixEnd_2478568 : Nat := 4983230072969 + 3 ^ 40 * 2478568 * 2
def baseEnd_2478568 : Nat := 848464479235442550000853

theorem tailTrace_2478568 : CollatzResearch.WordTrace tailWord_2478568 prefixEnd_2478568 848464479235442550000853 := by
  unfold tailWord_2478568
  simp only [CollatzResearch.WordTrace]
  refine ⟨45200400842289458279210179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60267201123052611038946905 45200400842289458279210179)
  ·
    refine ⟨67800601263434187418815269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45200400842289458279210179 67800601263434187418815269)
    ·
      refine ⟨12712612736893910141027863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67800601263434187418815269 12712612736893910141027863)
      ·
        refine ⟨19068919105340865211541795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12712612736893910141027863 19068919105340865211541795)
        ·
          refine ⟨28603378658011297817312693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19068919105340865211541795 28603378658011297817312693)
          ·
            refine ⟨2681566749188559170373065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28603378658011297817312693 2681566749188559170373065)
            ·
              refine ⟨2011175061891419377779799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2681566749188559170373065 2011175061891419377779799)
              ·
                refine ⟨3016762592837129066669699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2011175061891419377779799 3016762592837129066669699)
                ·
                  refine ⟨4525143889255693600004549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3016762592837129066669699 4525143889255693600004549)
                  ·
                    refine ⟨848464479235442550000853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4525143889255693600004549 848464479235442550000853)
                    ·
                      rfl

theorem cell22_2478568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 2, 1, 1, 4].length) (baseStart_2478568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2478568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2478568 prefixEnd_2478568 := by exact prefixLift 2478568
  have htrace : WordTrace (prefixWord ++ tailWord_2478568) baseStart_2478568 baseEnd_2478568 := by
    simpa [prefixWord, tailWord_2478568, baseEnd_2478568] using wordTrace_append hprefix tailTrace_2478568
  have hstable : (prefixWord ++ tailWord_2478568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2478568).length < 2 ^ (prefixWord ++ tailWord_2478568).sum := by decide
  have hdescent : baseEnd_2478568 < baseStart_2478568 := by decide
  rcases family_descends (prefixWord ++ tailWord_2478568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2478577 : List Nat := [1, 2, 2, 2, 3, 1, 11]
def baseStart_2478577 : Nat := 118140960795 + 2478577 * 2 ^ 59
def prefixEnd_2478577 : Nat := 4983230072969 + 3 ^ 40 * 2478577 * 2
def baseEnd_2478577 : Nat := 31424724448865538019475

theorem tailTrace_2478577 : CollatzResearch.WordTrace tailWord_2478577 prefixEnd_2478577 31424724448865538019475 := by
  unfold tailWord_2478577
  simp only [CollatzResearch.WordTrace]
  refine ⟨90401129941546311095497985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60267419961030874063665323 90401129941546311095497985)
  ·
    refine ⟨67800847456159733321623489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90401129941546311095497985 67800847456159733321623489)
    ·
      refine ⟨50850635592119799991217617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67800847456159733321623489 50850635592119799991217617)
      ·
        refine ⟨38137976694089849993413213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50850635592119799991217617 38137976694089849993413213)
        ·
          refine ⟨14301741260283693747529955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38137976694089849993413213 14301741260283693747529955)
          ·
            refine ⟨21452611890425540621294933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14301741260283693747529955 21452611890425540621294933)
            ·
              refine ⟨31424724448865538019475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 21452611890425540621294933 31424724448865538019475)
              ·
                rfl

theorem cell22_2478577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 11].length) (baseStart_2478577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2478577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2478577 prefixEnd_2478577 := by exact prefixLift 2478577
  have htrace : WordTrace (prefixWord ++ tailWord_2478577) baseStart_2478577 baseEnd_2478577 := by
    simpa [prefixWord, tailWord_2478577, baseEnd_2478577] using wordTrace_append hprefix tailTrace_2478577
  have hstable : (prefixWord ++ tailWord_2478577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2478577).length < 2 ^ (prefixWord ++ tailWord_2478577).sum := by decide
  have hdescent : baseEnd_2478577 < baseStart_2478577 := by decide
  rcases family_descends (prefixWord ++ tailWord_2478577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2478607 : List Nat := [1, 1, 2, 1, 1, 1, 2, 3, 4, 6]
def baseStart_2478607 : Nat := 118140960795 + 2478607 * 2 ^ 59
def prefixEnd_2478607 : Nat := 4983230072969 + 3 ^ 40 * 2478607 * 2
def baseEnd_2478607 : Nat := 848477829732459448275733

theorem tailTrace_2478607 : CollatzResearch.WordTrace tailWord_2478607 prefixEnd_2478607 848477829732459448275733 := by
  unfold tailWord_2478607
  simp only [CollatzResearch.WordTrace]
  refine ⟨90402224131437626219090075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60268149420958417479393383 90402224131437626219090075)
  ·
    refine ⟨135603336197156439328635113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90402224131437626219090075 135603336197156439328635113)
    ·
      refine ⟨101702502147867329496476335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135603336197156439328635113 101702502147867329496476335)
      ·
        refine ⟨152553753221800994244714503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101702502147867329496476335 152553753221800994244714503)
        ·
          refine ⟨228830629832701491367071755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152553753221800994244714503 228830629832701491367071755)
          ·
            refine ⟨343245944749052237050607633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 228830629832701491367071755 343245944749052237050607633)
            ·
              refine ⟨257434458561789177787955725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 343245944749052237050607633 257434458561789177787955725)
              ·
                refine ⟨96537921960670941670483397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 257434458561789177787955725 96537921960670941670483397)
                ·
                  refine ⟨18100860367625801563215637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 96537921960670941670483397 18100860367625801563215637)
                  ·
                    refine ⟨848477829732459448275733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18100860367625801563215637 848477829732459448275733)
                    ·
                      rfl

theorem cell22_2478607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 4, 6].length) (baseStart_2478607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2478607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2478607 prefixEnd_2478607 := by exact prefixLift 2478607
  have htrace : WordTrace (prefixWord ++ tailWord_2478607) baseStart_2478607 baseEnd_2478607 := by
    simpa [prefixWord, tailWord_2478607, baseEnd_2478607] using wordTrace_append hprefix tailTrace_2478607
  have hstable : (prefixWord ++ tailWord_2478607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2478607).length < 2 ^ (prefixWord ++ tailWord_2478607).sum := by decide
  have hdescent : baseEnd_2478607 < baseStart_2478607 := by decide
  rcases family_descends (prefixWord ++ tailWord_2478607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2478609 : List Nat := [1, 2, 2, 1, 1, 2, 2, 3, 5, 3]
def baseStart_2478609 : Nat := 118140960795 + 2478609 * 2 ^ 59
def prefixEnd_2478609 : Nat := 4983230072969 + 3 ^ 40 * 2478609 * 2
def baseEnd_2478609 : Nat := 848478514373332109725727

theorem tailTrace_2478609 : CollatzResearch.WordTrace tailWord_2478609 prefixEnd_2478609 848478514373332109725727 := by
  unfold tailWord_2478609
  simp only [CollatzResearch.WordTrace]
  refine ⟨90402297077430380560662881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60268198051620253707108587 90402297077430380560662881)
  ·
    refine ⟨67801722808072785420497161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90402297077430380560662881 67801722808072785420497161)
    ·
      refine ⟨50851292106054589065372871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67801722808072785420497161 50851292106054589065372871)
      ·
        refine ⟨76276938159081883598059307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50851292106054589065372871 76276938159081883598059307)
        ·
          refine ⟨114415407238622825397088961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76276938159081883598059307 114415407238622825397088961)
          ·
            refine ⟨85811555428967119047816721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114415407238622825397088961 85811555428967119047816721)
            ·
              refine ⟨64358666571725339285862541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85811555428967119047816721 64358666571725339285862541)
              ·
                refine ⟨24134499964397002232198453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64358666571725339285862541 24134499964397002232198453)
                ·
                  refine ⟨2262609371662218959268605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24134499964397002232198453 2262609371662218959268605)
                  ·
                    refine ⟨848478514373332109725727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2262609371662218959268605 848478514373332109725727)
                    ·
                      rfl

theorem cell22_2478609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 3, 5, 3].length) (baseStart_2478609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2478609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2478609 prefixEnd_2478609 := by exact prefixLift 2478609
  have htrace : WordTrace (prefixWord ++ tailWord_2478609) baseStart_2478609 baseEnd_2478609 := by
    simpa [prefixWord, tailWord_2478609, baseEnd_2478609] using wordTrace_append hprefix tailTrace_2478609
  have hstable : (prefixWord ++ tailWord_2478609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2478609).length < 2 ^ (prefixWord ++ tailWord_2478609).sum := by decide
  have hdescent : baseEnd_2478609 < baseStart_2478609 := by decide
  rcases family_descends (prefixWord ++ tailWord_2478609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2478628 : List Nat := [2, 3, 1, 5, 2, 1, 8]
def baseStart_2478628 : Nat := 118140960795 + 2478628 * 2 ^ 59
def prefixEnd_2478628 : Nat := 4983230072969 + 3 ^ 40 * 2478628 * 2
def baseEnd_2478628 : Nat := 31425371054134162722247

theorem tailTrace_2478628 : CollatzResearch.WordTrace tailWord_2478628 prefixEnd_2478628 31425371054134162722247 := by
  unfold tailWord_2478628
  simp only [CollatzResearch.WordTrace]
  refine ⟨45201495032180773402802269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60268660042907697870403025 45201495032180773402802269)
  ·
    refine ⟨16950560637067790026050851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45201495032180773402802269 16950560637067790026050851)
    ·
      refine ⟨25425840955601685039076277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16950560637067790026050851 25425840955601685039076277)
      ·
        refine ⟨2383672589587657972413401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25425840955601685039076277 2383672589587657972413401)
        ·
          refine ⟨1787754442190743479310051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2383672589587657972413401 1787754442190743479310051)
          ·
            refine ⟨2681631663286115218965077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1787754442190743479310051 2681631663286115218965077)
            ·
              refine ⟨31425371054134162722247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2681631663286115218965077 31425371054134162722247)
              ·
                rfl

theorem cell22_2478628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 8].length) (baseStart_2478628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2478628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2478628 prefixEnd_2478628 := by exact prefixLift 2478628
  have htrace : WordTrace (prefixWord ++ tailWord_2478628) baseStart_2478628 baseEnd_2478628 := by
    simpa [prefixWord, tailWord_2478628, baseEnd_2478628] using wordTrace_append hprefix tailTrace_2478628
  have hstable : (prefixWord ++ tailWord_2478628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2478628).length < 2 ^ (prefixWord ++ tailWord_2478628).sum := by decide
  have hdescent : baseEnd_2478628 < baseStart_2478628 := by decide
  rcases family_descends (prefixWord ++ tailWord_2478628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2478656 : List Nat := [2, 1, 1, 2, 2, 2, 6, 1, 5]
def baseStart_2478656 : Nat := 118140960795 + 2478656 * 2 ^ 59
def prefixEnd_2478656 : Nat := 4983230072969 + 3 ^ 40 * 2478656 * 2
def baseEnd_2478656 : Nat := 282831534477946551266861

theorem tailTrace_2478656 : CollatzResearch.WordTrace tailWord_2478656 prefixEnd_2478656 282831534477946551266861 := by
  unfold tailWord_2478656
  simp only [CollatzResearch.WordTrace]
  refine ⟨45202005654130053793811911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60269340872173405058415881 45202005654130053793811911)
  ·
    refine ⟨67803008481195080690717867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45202005654130053793811911 67803008481195080690717867)
    ·
      refine ⟨101704512721792621036076801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67803008481195080690717867 101704512721792621036076801)
      ·
        refine ⟨76278384541344465777057601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101704512721792621036076801 76278384541344465777057601)
        ·
          refine ⟨57208788406008349332793201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76278384541344465777057601 57208788406008349332793201)
          ·
            refine ⟨42906591304506261999594901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57208788406008349332793201 42906591304506261999594901)
            ·
              refine ⟨2011246467398731031231011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 42906591304506261999594901 2011246467398731031231011)
              ·
                refine ⟨3016869701098096546846517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2011246467398731031231011 3016869701098096546846517)
                ·
                  refine ⟨282831534477946551266861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3016869701098096546846517 282831534477946551266861)
                  ·
                    rfl

theorem cell22_2478656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 6, 1, 5].length) (baseStart_2478656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2478656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2478656 prefixEnd_2478656 := by exact prefixLift 2478656
  have htrace : WordTrace (prefixWord ++ tailWord_2478656) baseStart_2478656 baseEnd_2478656 := by
    simpa [prefixWord, tailWord_2478656, baseEnd_2478656] using wordTrace_append hprefix tailTrace_2478656
  have hstable : (prefixWord ++ tailWord_2478656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2478656).length < 2 ^ (prefixWord ++ tailWord_2478656).sum := by decide
  have hdescent : baseEnd_2478656 < baseStart_2478656 := by decide
  rcases family_descends (prefixWord ++ tailWord_2478656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2478690 : List Nat := [3, 3, 2, 3, 1, 1, 2, 2, 5]
def baseStart_2478690 : Nat := 118140960795 + 2478690 * 2 ^ 59
def prefixEnd_2478690 : Nat := 4983230072969 + 3 ^ 40 * 2478690 * 2
def baseEnd_2478690 : Nat := 282835414109558299483493

theorem tailTrace_2478690 : CollatzResearch.WordTrace tailWord_2478690 prefixEnd_2478690 282835414109558299483493 := by
  unfold tailWord_2478690
  simp only [CollatzResearch.WordTrace]
  refine ⟨22601312847534232848590381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60270167593424620929574349 22601312847534232848590381)
  ·
    refine ⟨8475492317825337318221393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22601312847534232848590381 8475492317825337318221393)
    ·
      refine ⟨6356619238369002988666045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8475492317825337318221393 6356619238369002988666045)
      ·
        refine ⟨2383732214388376120749767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6356619238369002988666045 2383732214388376120749767)
        ·
          refine ⟨3575598321582564181124651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2383732214388376120749767 3575598321582564181124651)
          ·
            refine ⟨5363397482373846271686977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3575598321582564181124651 5363397482373846271686977)
            ·
              refine ⟨4022548111780384703765233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5363397482373846271686977 4022548111780384703765233)
              ·
                refine ⟨3016911083835288527823925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4022548111780384703765233 3016911083835288527823925)
                ·
                  refine ⟨282835414109558299483493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3016911083835288527823925 282835414109558299483493)
                  ·
                    rfl

theorem cell22_2478690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 2, 5].length) (baseStart_2478690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2478690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2478690 prefixEnd_2478690 := by exact prefixLift 2478690
  have htrace : WordTrace (prefixWord ++ tailWord_2478690) baseStart_2478690 baseEnd_2478690 := by
    simpa [prefixWord, tailWord_2478690, baseEnd_2478690] using wordTrace_append hprefix tailTrace_2478690
  have hstable : (prefixWord ++ tailWord_2478690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2478690).length < 2 ^ (prefixWord ++ tailWord_2478690).sum := by decide
  have hdescent : baseEnd_2478690 < baseStart_2478690 := by decide
  rcases family_descends (prefixWord ++ tailWord_2478690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2478761 : List Nat := [1, 2, 1, 1, 1, 1, 2, 7, 3, 3]
def baseStart_2478761 : Nat := 118140960795 + 2478761 * 2 ^ 59
def prefixEnd_2478761 : Nat := 4983230072969 + 3 ^ 40 * 2478761 * 2
def baseEnd_2478761 : Nat := 848530547079654379925261

theorem tailTrace_2478761 : CollatzResearch.WordTrace tailWord_2478761 prefixEnd_2478761 848530547079654379925261 := by
  unfold tailWord_2478761
  simp only [CollatzResearch.WordTrace]
  refine ⟨90407840972879710520196137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60271893981919807013464091 90407840972879710520196137)
  ·
    refine ⟨67805880729659782890147103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90407840972879710520196137 67805880729659782890147103)
    ·
      refine ⟨101708821094489674335220655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67805880729659782890147103 101708821094489674335220655)
      ·
        refine ⟨152563231641734511502830983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101708821094489674335220655 152563231641734511502830983)
        ·
          refine ⟨228844847462601767254246475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152563231641734511502830983 228844847462601767254246475)
          ·
            refine ⟨343267271193902650881369713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 228844847462601767254246475 343267271193902650881369713)
            ·
              refine ⟨257450453395426988161027285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 343267271193902650881369713 257450453395426988161027285)
              ·
                refine ⟨6033995001455320035024077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 257450453395426988161027285 6033995001455320035024077)
                ·
                  refine ⟨2262748125545745013134029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6033995001455320035024077 2262748125545745013134029)
                  ·
                    refine ⟨848530547079654379925261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2262748125545745013134029 848530547079654379925261)
                    ·
                      rfl

theorem cell22_2478761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 7, 3, 3].length) (baseStart_2478761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2478761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2478761 prefixEnd_2478761 := by exact prefixLift 2478761
  have htrace : WordTrace (prefixWord ++ tailWord_2478761) baseStart_2478761 baseEnd_2478761 := by
    simpa [prefixWord, tailWord_2478761, baseEnd_2478761] using wordTrace_append hprefix tailTrace_2478761
  have hstable : (prefixWord ++ tailWord_2478761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2478761).length < 2 ^ (prefixWord ++ tailWord_2478761).sum := by decide
  have hdescent : baseEnd_2478761 < baseStart_2478761 := by decide
  rcases family_descends (prefixWord ++ tailWord_2478761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2478812 : List Nat := [2, 2, 5, 1, 1, 3, 1, 1, 3, 3]
def baseStart_2478812 : Nat := 118140960795 + 2478812 * 2 ^ 59
def prefixEnd_2478812 : Nat := 4983230072969 + 3 ^ 40 * 2478812 * 2
def baseEnd_2478812 : Nat := 848548005421907246900105

theorem tailTrace_2478812 : CollatzResearch.WordTrace tailWord_2478812 prefixEnd_2478812 848548005421907246900105 := by
  unfold tailWord_2478812
  simp only [CollatzResearch.WordTrace]
  refine ⟨45204850547847473115151345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60273134063796630820201793 45204850547847473115151345)
  ·
    refine ⟨33903637910885604836363509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45204850547847473115151345 33903637910885604836363509)
    ·
      refine ⟨3178466054145525453409079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33903637910885604836363509 3178466054145525453409079)
      ·
        refine ⟨4767699081218288180113619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3178466054145525453409079 4767699081218288180113619)
        ·
          refine ⟨7151548621827432270170429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4767699081218288180113619 7151548621827432270170429)
          ·
            refine ⟨2681830733185287101313911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7151548621827432270170429 2681830733185287101313911)
            ·
              refine ⟨4022746099777930651970867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2681830733185287101313911 4022746099777930651970867)
              ·
                refine ⟨6034119149666895977956301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4022746099777930651970867 6034119149666895977956301)
                ·
                  refine ⟨2262794681125085991733613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6034119149666895977956301 2262794681125085991733613)
                  ·
                    refine ⟨848548005421907246900105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2262794681125085991733613 848548005421907246900105)
                    ·
                      rfl

theorem cell22_2478812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_2478812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2478812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2478812 prefixEnd_2478812 := by exact prefixLift 2478812
  have htrace : WordTrace (prefixWord ++ tailWord_2478812) baseStart_2478812 baseEnd_2478812 := by
    simpa [prefixWord, tailWord_2478812, baseEnd_2478812] using wordTrace_append hprefix tailTrace_2478812
  have hstable : (prefixWord ++ tailWord_2478812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2478812).length < 2 ^ (prefixWord ++ tailWord_2478812).sum := by decide
  have hdescent : baseEnd_2478812 < baseStart_2478812 := by decide
  rcases family_descends (prefixWord ++ tailWord_2478812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2478838 : List Nat := [5, 1, 1, 1, 1, 2, 3, 1, 3, 4]
def baseStart_2478838 : Nat := 118140960795 + 2478838 * 2 ^ 59
def prefixEnd_2478838 : Nat := 4983230072969 + 3 ^ 40 * 2478838 * 2
def baseEnd_2478838 : Nat := 848556905753251845750025

theorem tailTrace_2478838 : CollatzResearch.WordTrace tailWord_2478838 prefixEnd_2478838 848556905753251845750025 := by
  unfold tailWord_2478838
  simp only [CollatzResearch.WordTrace]
  refine ⟨5650665587100047041921823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 60273766262400501780499445 5650665587100047041921823)
  ·
    refine ⟨8475998380650070562882735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5650665587100047041921823 8475998380650070562882735)
    ·
      refine ⟨12713997570975105844324103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8475998380650070562882735 12713997570975105844324103)
      ·
        refine ⟨19070996356462658766486155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12713997570975105844324103 19070996356462658766486155)
        ·
          refine ⟨28606494534693988149729233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19070996356462658766486155 28606494534693988149729233)
          ·
            refine ⟨21454870901020491112296925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28606494534693988149729233 21454870901020491112296925)
            ·
              refine ⟨8045576587882684167111347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21454870901020491112296925 8045576587882684167111347)
              ·
                refine ⟨12068364881824026250667021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8045576587882684167111347 12068364881824026250667021)
                ·
                  refine ⟨4525636830684009844000133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12068364881824026250667021 4525636830684009844000133)
                  ·
                    refine ⟨848556905753251845750025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4525636830684009844000133 848556905753251845750025)
                    ·
                      rfl

theorem cell22_2478838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 1, 3, 4].length) (baseStart_2478838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2478838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2478838 prefixEnd_2478838 := by exact prefixLift 2478838
  have htrace : WordTrace (prefixWord ++ tailWord_2478838) baseStart_2478838 baseEnd_2478838 := by
    simpa [prefixWord, tailWord_2478838, baseEnd_2478838] using wordTrace_append hprefix tailTrace_2478838
  have hstable : (prefixWord ++ tailWord_2478838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2478838).length < 2 ^ (prefixWord ++ tailWord_2478838).sum := by decide
  have hdescent : baseEnd_2478838 < baseStart_2478838 := by decide
  rcases family_descends (prefixWord ++ tailWord_2478838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2478898 : List Nat := [3, 2, 1, 1, 3, 1, 5, 6]
def baseStart_2478898 : Nat := 118140960795 + 2478898 * 2 ^ 59
def prefixEnd_2478898 : Nat := 4983230072969 + 3 ^ 40 * 2478898 * 2
def baseEnd_2478898 : Nat := 94286382775492409916649

theorem tailTrace_2478898 : CollatzResearch.WordTrace tailWord_2478898 prefixEnd_2478898 94286382775492409916649 := by
  unfold tailWord_2478898
  simp only [CollatzResearch.WordTrace]
  refine ⟨22603209443345845729483337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60275225182255588611955565 22603209443345845729483337)
  ·
    refine ⟨16952407082509384297112503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22603209443345845729483337 16952407082509384297112503)
    ·
      refine ⟨25428610623764076445668755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16952407082509384297112503 25428610623764076445668755)
      ·
        refine ⟨38142915935646114668503133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25428610623764076445668755 38142915935646114668503133)
        ·
          refine ⟨14303593475867293000688675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38142915935646114668503133 14303593475867293000688675)
          ·
            refine ⟨21455390213800939501033013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14303593475867293000688675 21455390213800939501033013)
            ·
              refine ⟨2011442832543838078221845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21455390213800939501033013 2011442832543838078221845)
              ·
                refine ⟨94286382775492409916649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2011442832543838078221845 94286382775492409916649)
                ·
                  rfl

theorem cell22_2478898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 5, 6].length) (baseStart_2478898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2478898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2478898 prefixEnd_2478898 := by exact prefixLift 2478898
  have htrace : WordTrace (prefixWord ++ tailWord_2478898) baseStart_2478898 baseEnd_2478898 := by
    simpa [prefixWord, tailWord_2478898, baseEnd_2478898] using wordTrace_append hprefix tailTrace_2478898
  have hstable : (prefixWord ++ tailWord_2478898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2478898).length < 2 ^ (prefixWord ++ tailWord_2478898).sum := by decide
  have hdescent : baseEnd_2478898 < baseStart_2478898 := by decide
  rcases family_descends (prefixWord ++ tailWord_2478898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2478900 : List Nat := [2, 5, 1, 1, 3, 1, 1, 1, 1, 6]
def baseStart_2478900 : Nat := 118140960795 + 2478900 * 2 ^ 59
def prefixEnd_2478900 : Nat := 4983230072969 + 3 ^ 40 * 2478900 * 2
def baseEnd_2478900 : Nat := 848578129620304350699835

theorem tailTrace_2478900 : CollatzResearch.WordTrace tailWord_2478900 prefixEnd_2478900 848578129620304350699835 := by
  unfold tailWord_2478900
  simp only [CollatzResearch.WordTrace]
  refine ⟨45206455359688068629753077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60275273812917424839670769 45206455359688068629753077)
  ·
    refine ⟨4238105189970756434039351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 45206455359688068629753077 4238105189970756434039351)
    ·
      refine ⟨6357157784956134651059027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4238105189970756434039351 6357157784956134651059027)
      ·
        refine ⟨9535736677434201976588541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6357157784956134651059027 9535736677434201976588541)
        ·
          refine ⟨3575901254037825741220703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9535736677434201976588541 3575901254037825741220703)
          ·
            refine ⟨5363851881056738611831055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3575901254037825741220703 5363851881056738611831055)
            ·
              refine ⟨8045777821585107917746583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5363851881056738611831055 8045777821585107917746583)
              ·
                refine ⟨12068666732377661876619875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8045777821585107917746583 12068666732377661876619875)
                ·
                  refine ⟨18103000098566492814929813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12068666732377661876619875 18103000098566492814929813)
                  ·
                    refine ⟨848578129620304350699835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18103000098566492814929813 848578129620304350699835)
                    ·
                      rfl

theorem cell22_2478900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_2478900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2478900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2478900 prefixEnd_2478900 := by exact prefixLift 2478900
  have htrace : WordTrace (prefixWord ++ tailWord_2478900) baseStart_2478900 baseEnd_2478900 := by
    simpa [prefixWord, tailWord_2478900, baseEnd_2478900] using wordTrace_append hprefix tailTrace_2478900
  have hstable : (prefixWord ++ tailWord_2478900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2478900).length < 2 ^ (prefixWord ++ tailWord_2478900).sum := by decide
  have hdescent : baseEnd_2478900 < baseStart_2478900 := by decide
  rcases family_descends (prefixWord ++ tailWord_2478900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2478930 : List Nat := [3, 2, 2, 1, 1, 2, 4, 1, 3, 3]
def baseStart_2478930 : Nat := 118140960795 + 2478930 * 2 ^ 59
def prefixEnd_2478930 : Nat := 4983230072969 + 3 ^ 40 * 2478930 * 2
def baseEnd_2478930 : Nat := 848588399233394272449743

theorem tailTrace_2478930 : CollatzResearch.WordTrace tailWord_2478930 prefixEnd_2478930 848588399233394272449743 := by
  unfold tailWord_2478930
  simp only [CollatzResearch.WordTrace]
  refine ⟨22603501227316863095774561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60276003272844968255398829 22603501227316863095774561)
  ·
    refine ⟨16952625920487647321830921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22603501227316863095774561 16952625920487647321830921)
    ·
      refine ⟨12714469440365735491373191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16952625920487647321830921 12714469440365735491373191)
      ·
        refine ⟨19071704160548603237059787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12714469440365735491373191 19071704160548603237059787)
        ·
          refine ⟨28607556240822904855589681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19071704160548603237059787 28607556240822904855589681)
          ·
            refine ⟨21455667180617178641692261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28607556240822904855589681 21455667180617178641692261)
            ·
              refine ⟨4022937596365720995317299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21455667180617178641692261 4022937596365720995317299)
              ·
                refine ⟨6034406394548581492975949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4022937596365720995317299 6034406394548581492975949)
                ·
                  refine ⟨2262902397955718059865981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6034406394548581492975949 2262902397955718059865981)
                  ·
                    refine ⟨848588399233394272449743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2262902397955718059865981 848588399233394272449743)
                    ·
                      rfl

theorem cell22_2478930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 1, 3, 3].length) (baseStart_2478930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2478930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2478930 prefixEnd_2478930 := by exact prefixLift 2478930
  have htrace : WordTrace (prefixWord ++ tailWord_2478930) baseStart_2478930 baseEnd_2478930 := by
    simpa [prefixWord, tailWord_2478930, baseEnd_2478930] using wordTrace_append hprefix tailTrace_2478930
  have hstable : (prefixWord ++ tailWord_2478930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2478930).length < 2 ^ (prefixWord ++ tailWord_2478930).sum := by decide
  have hdescent : baseEnd_2478930 < baseStart_2478930 := by decide
  rcases family_descends (prefixWord ++ tailWord_2478930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2478971 : List Nat := [1, 1, 1, 1, 1, 5, 2, 2, 8]
def baseStart_2478971 : Nat := 118140960795 + 2478971 * 2 ^ 59
def prefixEnd_2478971 : Nat := 4983230072969 + 3 ^ 40 * 2478971 * 2
def baseEnd_2478971 : Nat := 282867478123761277391539

theorem tailTrace_2478971 : CollatzResearch.WordTrace tailWord_2478971 prefixEnd_2478971 282867478123761277391539 := by
  unfold tailWord_2478971
  simp only [CollatzResearch.WordTrace]
  refine ⟨90415500302118916385340767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60277000201412610923560511 90415500302118916385340767)
  ·
    refine ⟨135623250453178374578011151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90415500302118916385340767 135623250453178374578011151)
    ·
      refine ⟨203434875679767561867016727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135623250453178374578011151 203434875679767561867016727)
      ·
        refine ⟨305152313519651342800525091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203434875679767561867016727 305152313519651342800525091)
        ·
          refine ⟨457728470279477014200787637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 305152313519651342800525091 457728470279477014200787637)
          ·
            refine ⟨42912044088700970081323841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 457728470279477014200787637 42912044088700970081323841)
            ·
              refine ⟨32184033066525727560992881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42912044088700970081323841 32184033066525727560992881)
              ·
                refine ⟨24138024799894295670744661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32184033066525727560992881 24138024799894295670744661)
                ·
                  refine ⟨282867478123761277391539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24138024799894295670744661 282867478123761277391539)
                  ·
                    rfl

theorem cell22_2478971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 2, 8].length) (baseStart_2478971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2478971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2478971 prefixEnd_2478971 := by exact prefixLift 2478971
  have htrace : WordTrace (prefixWord ++ tailWord_2478971) baseStart_2478971 baseEnd_2478971 := by
    simpa [prefixWord, tailWord_2478971, baseEnd_2478971] using wordTrace_append hprefix tailTrace_2478971
  have hstable : (prefixWord ++ tailWord_2478971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2478971).length < 2 ^ (prefixWord ++ tailWord_2478971).sum := by decide
  have hdescent : baseEnd_2478971 < baseStart_2478971 := by decide
  rcases family_descends (prefixWord ++ tailWord_2478971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2478988 : List Nat := [2, 2, 1, 2, 1, 2, 5, 1, 6]
def baseStart_2478988 : Nat := 118140960795 + 2478988 * 2 ^ 59
def prefixEnd_2478988 : Nat := 4983230072969 + 3 ^ 40 * 2478988 * 2
def baseEnd_2478988 : Nat := 282869417939567151499855

theorem tailTrace_2478988 : CollatzResearch.WordTrace tailWord_2478988 prefixEnd_2478988 282869417939567151499855 := by
  unfold tailWord_2478988
  simp only [CollatzResearch.WordTrace]
  refine ⟨45208060171528664144354809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60277413562038218859139745 45208060171528664144354809)
  ·
    refine ⟨33906045128646498108266107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45208060171528664144354809 33906045128646498108266107)
    ·
      refine ⟨50859067692969747162399161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33906045128646498108266107 50859067692969747162399161)
      ·
        refine ⟨38144300769727310371799371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50859067692969747162399161 38144300769727310371799371)
        ·
          refine ⟨57216451154590965557699057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38144300769727310371799371 57216451154590965557699057)
          ·
            refine ⟨42912338365943224168274293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57216451154590965557699057 42912338365943224168274293)
            ·
              refine ⟨4023031721807177265775715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42912338365943224168274293 4023031721807177265775715)
              ·
                refine ⟨6034547582710765898663573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4023031721807177265775715 6034547582710765898663573)
                ·
                  refine ⟨282869417939567151499855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6034547582710765898663573 282869417939567151499855)
                  ·
                    rfl

theorem cell22_2478988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 1, 6].length) (baseStart_2478988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2478988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2478988 prefixEnd_2478988 := by exact prefixLift 2478988
  have htrace : WordTrace (prefixWord ++ tailWord_2478988) baseStart_2478988 baseEnd_2478988 := by
    simpa [prefixWord, tailWord_2478988, baseEnd_2478988] using wordTrace_append hprefix tailTrace_2478988
  have hstable : (prefixWord ++ tailWord_2478988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2478988).length < 2 ^ (prefixWord ++ tailWord_2478988).sum := by decide
  have hdescent : baseEnd_2478988 < baseStart_2478988 := by decide
  rcases family_descends (prefixWord ++ tailWord_2478988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2478994 : List Nat := [3, 2, 3, 2, 2, 2, 2, 1, 5]
def baseStart_2478994 : Nat := 118140960795 + 2478994 * 2 ^ 59
def prefixEnd_2478994 : Nat := 4983230072969 + 3 ^ 40 * 2478994 * 2
def baseEnd_2478994 : Nat := 282870102580439812949849

theorem tailTrace_2478994 : CollatzResearch.WordTrace tailWord_2478994 prefixEnd_2478994 282870102580439812949849 := by
  unfold tailWord_2478994
  simp only [CollatzResearch.WordTrace]
  refine ⟨22604084795258897828357009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60277559454023727542285357 22604084795258897828357009)
  ·
    refine ⟨16953063596444173371267757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22604084795258897828357009 16953063596444173371267757)
    ·
      refine ⟨6357398848666565014225409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16953063596444173371267757 6357398848666565014225409)
      ·
        refine ⟨4768049136499923760669057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6357398848666565014225409 4768049136499923760669057)
        ·
          refine ⟨3576036852374942820501793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4768049136499923760669057 3576036852374942820501793)
          ·
            refine ⟨2682027639281207115376345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3576036852374942820501793 2682027639281207115376345)
            ·
              refine ⟨2011520729460905336532259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2682027639281207115376345 2011520729460905336532259)
              ·
                refine ⟨3017281094191358004798389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2011520729460905336532259 3017281094191358004798389)
                ·
                  refine ⟨282870102580439812949849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3017281094191358004798389 282870102580439812949849)
                  ·
                    rfl

theorem cell22_2478994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 2, 1, 5].length) (baseStart_2478994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2478994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2478994 prefixEnd_2478994 := by exact prefixLift 2478994
  have htrace : WordTrace (prefixWord ++ tailWord_2478994) baseStart_2478994 baseEnd_2478994 := by
    simpa [prefixWord, tailWord_2478994, baseEnd_2478994] using wordTrace_append hprefix tailTrace_2478994
  have hstable : (prefixWord ++ tailWord_2478994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2478994).length < 2 ^ (prefixWord ++ tailWord_2478994).sum := by decide
  have hdescent : baseEnd_2478994 < baseStart_2478994 := by decide
  rcases family_descends (prefixWord ++ tailWord_2478994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2479007 : List Nat := [1, 1, 2, 5, 2, 3, 1, 2, 1, 4]
def baseStart_2479007 : Nat := 118140960795 + 2479007 * 2 ^ 59
def prefixEnd_2479007 : Nat := 4983230072969 + 3 ^ 40 * 2479007 * 2
def baseEnd_2479007 : Nat := 848614757906991738274507

theorem tailTrace_2479007 : CollatzResearch.WordTrace tailWord_2479007 prefixEnd_2479007 848614757906991738274507 := by
  unfold tailWord_2479007
  simp only [CollatzResearch.WordTrace]
  refine ⟨90416813329988494533651275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60277875553325663022434183 90416813329988494533651275)
  ·
    refine ⟨135625219994982741800476913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90416813329988494533651275 135625219994982741800476913)
    ·
      refine ⟨101718914996237056350357685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135625219994982741800476913 101718914996237056350357685)
      ·
        refine ⟨9536148280897224032846033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 101718914996237056350357685 9536148280897224032846033)
        ·
          refine ⟨7152111210672918024634525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9536148280897224032846033 7152111210672918024634525)
          ·
            refine ⟨2682041704002344259237947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7152111210672918024634525 2682041704002344259237947)
            ·
              refine ⟨4023062556003516388856921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2682041704002344259237947 4023062556003516388856921)
              ·
                refine ⟨3017296917002637291642691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4023062556003516388856921 3017296917002637291642691)
                ·
                  refine ⟨4525945375503955937464037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3017296917002637291642691 4525945375503955937464037)
                  ·
                    refine ⟨848614757906991738274507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4525945375503955937464037 848614757906991738274507)
                    ·
                      rfl

theorem cell22_2479007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 2, 1, 4].length) (baseStart_2479007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2479007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2479007 prefixEnd_2479007 := by exact prefixLift 2479007
  have htrace : WordTrace (prefixWord ++ tailWord_2479007) baseStart_2479007 baseEnd_2479007 := by
    simpa [prefixWord, tailWord_2479007, baseEnd_2479007] using wordTrace_append hprefix tailTrace_2479007
  have hstable : (prefixWord ++ tailWord_2479007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2479007).length < 2 ^ (prefixWord ++ tailWord_2479007).sum := by decide
  have hdescent : baseEnd_2479007 < baseStart_2479007 := by decide
  rcases family_descends (prefixWord ++ tailWord_2479007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2479065 : List Nat := [1, 2, 1, 2, 5, 1, 1, 1, 5, 3]
def baseStart_2479065 : Nat := 118140960795 + 2479065 * 2 ^ 59
def prefixEnd_2479065 : Nat := 4983230072969 + 3 ^ 40 * 2479065 * 2
def baseEnd_2479065 : Nat := 848634612492298920324329

theorem tailTrace_2479065 : CollatzResearch.WordTrace tailWord_2479065 prefixEnd_2479065 848634612492298920324329 := by
  unfold tailWord_2479065
  simp only [CollatzResearch.WordTrace]
  refine ⟨90418928763778370439262649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60279285842518913626175099 90418928763778370439262649)
  ·
    refine ⟨67814196572833777829446987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90418928763778370439262649 67814196572833777829446987)
    ·
      refine ⟨101721294859250666744170481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67814196572833777829446987 101721294859250666744170481)
      ·
        refine ⟨76290971144438000058127861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101721294859250666744170481 76290971144438000058127861)
        ·
          refine ⟨7152278544791062505449487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 76290971144438000058127861 7152278544791062505449487)
          ·
            refine ⟨10728417817186593758174231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7152278544791062505449487 10728417817186593758174231)
            ·
              refine ⟨16092626725779890637261347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10728417817186593758174231 16092626725779890637261347)
              ·
                refine ⟨24138940088669835955892021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16092626725779890637261347 24138940088669835955892021)
                ·
                  refine ⟨2263025633312797120864877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24138940088669835955892021 2263025633312797120864877)
                  ·
                    refine ⟨848634612492298920324329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2263025633312797120864877 848634612492298920324329)
                    ·
                      rfl

theorem cell22_2479065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 1, 5, 3].length) (baseStart_2479065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2479065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2479065 prefixEnd_2479065 := by exact prefixLift 2479065
  have htrace : WordTrace (prefixWord ++ tailWord_2479065) baseStart_2479065 baseEnd_2479065 := by
    simpa [prefixWord, tailWord_2479065, baseEnd_2479065] using wordTrace_append hprefix tailTrace_2479065
  have hstable : (prefixWord ++ tailWord_2479065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2479065).length < 2 ^ (prefixWord ++ tailWord_2479065).sum := by decide
  have hdescent : baseEnd_2479065 < baseStart_2479065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2479065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2479112 : List Nat := [2, 1, 3, 2, 1, 4, 3, 1, 5]
def baseStart_2479112 : Nat := 118140960795 + 2479112 * 2 ^ 59
def prefixEnd_2479112 : Nat := 4983230072969 + 3 ^ 40 * 2479112 * 2
def baseEnd_2479112 : Nat := 282883567184268821466395

theorem tailTrace_2479112 : CollatzResearch.WordTrace tailWord_2479112 prefixEnd_2479112 282883567184268821466395 := by
  unfold tailWord_2479112
  simp only [CollatzResearch.WordTrace]
  refine ⟨45210321497304048733111795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60280428663072064977482393 45210321497304048733111795)
  ·
    refine ⟨67815482245956073099667693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45210321497304048733111795 67815482245956073099667693)
    ·
      refine ⟨25430805842233527412375385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67815482245956073099667693 25430805842233527412375385)
      ·
        refine ⟨19073104381675145559281539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25430805842233527412375385 19073104381675145559281539)
        ·
          refine ⟨28609656572512718338922309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19073104381675145559281539 28609656572512718338922309)
          ·
            refine ⟨5364310607346134688547933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28609656572512718338922309 5364310607346134688547933)
            ·
              refine ⟨2011616477754800508205475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5364310607346134688547933 2011616477754800508205475)
              ·
                refine ⟨3017424716632200762308213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2011616477754800508205475 3017424716632200762308213)
                ·
                  refine ⟨282883567184268821466395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3017424716632200762308213 282883567184268821466395)
                  ·
                    rfl

theorem cell22_2479112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 3, 1, 5].length) (baseStart_2479112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2479112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2479112 prefixEnd_2479112 := by exact prefixLift 2479112
  have htrace : WordTrace (prefixWord ++ tailWord_2479112) baseStart_2479112 baseEnd_2479112 := by
    simpa [prefixWord, tailWord_2479112, baseEnd_2479112] using wordTrace_append hprefix tailTrace_2479112
  have hstable : (prefixWord ++ tailWord_2479112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2479112).length < 2 ^ (prefixWord ++ tailWord_2479112).sum := by decide
  have hdescent : baseEnd_2479112 < baseStart_2479112 := by decide
  rcases family_descends (prefixWord ++ tailWord_2479112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2479133 : List Nat := [1, 4, 2, 2, 4, 1, 1, 3, 1, 3]
def baseStart_2479133 : Nat := 118140960795 + 2479133 * 2 ^ 59
def prefixEnd_2479133 : Nat := 4983230072969 + 3 ^ 40 * 2479133 * 2
def baseEnd_2479133 : Nat := 848657890281969409624121

theorem tailTrace_2479133 : CollatzResearch.WordTrace tailWord_2479133 prefixEnd_2479133 848657890281969409624121 := by
  unfold tailWord_2479133
  simp only [CollatzResearch.WordTrace]
  refine ⟨90421408927532018052738053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60280939285021345368492035 90421408927532018052738053)
  ·
    refine ⟨16954014173912253384888385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90421408927532018052738053 16954014173912253384888385)
    ·
      refine ⟨12715510630434190038666289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16954014173912253384888385 12715510630434190038666289)
      ·
        refine ⟨9536632972825642528999717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12715510630434190038666289 9536632972825642528999717)
        ·
          refine ⟨1788118682404807974187447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9536632972825642528999717 1788118682404807974187447)
          ·
            refine ⟨2682178023607211961281171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1788118682404807974187447 2682178023607211961281171)
            ·
              refine ⟨4023267035410817941921757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2682178023607211961281171 4023267035410817941921757)
              ·
                refine ⟨1508725138279056728220659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4023267035410817941921757 1508725138279056728220659)
                ·
                  refine ⟨2263087707418585092330989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1508725138279056728220659 2263087707418585092330989)
                  ·
                    refine ⟨848657890281969409624121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2263087707418585092330989 848657890281969409624121)
                    ·
                      rfl

theorem cell22_2479133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 3, 1, 3].length) (baseStart_2479133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2479133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2479133 prefixEnd_2479133 := by exact prefixLift 2479133
  have htrace : WordTrace (prefixWord ++ tailWord_2479133) baseStart_2479133 baseEnd_2479133 := by
    simpa [prefixWord, tailWord_2479133, baseEnd_2479133] using wordTrace_append hprefix tailTrace_2479133
  have hstable : (prefixWord ++ tailWord_2479133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2479133).length < 2 ^ (prefixWord ++ tailWord_2479133).sum := by decide
  have hdescent : baseEnd_2479133 < baseStart_2479133 := by decide
  rcases family_descends (prefixWord ++ tailWord_2479133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2479208 : List Nat := [2, 1, 4, 4, 1, 2, 2, 2, 4]
def baseStart_2479208 : Nat := 118140960795 + 2479208 * 2 ^ 59
def prefixEnd_2479208 : Nat := 4983230072969 + 3 ^ 40 * 2479208 * 2
def baseEnd_2479208 : Nat := 282894521438231404666297

theorem tailTrace_2479208 : CollatzResearch.WordTrace tailWord_2479208 prefixEnd_2479208 282894521438231404666297 := by
  unfold tailWord_2479208
  simp only [CollatzResearch.WordTrace]
  refine ⟨45212072201130152930859139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60282762934840203907812185 45212072201130152930859139)
  ·
    refine ⟨67818108301695229396288709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45212072201130152930859139 67818108301695229396288709)
    ·
      refine ⟨12715895306567855511804133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67818108301695229396288709 12715895306567855511804133)
      ·
        refine ⟨2384230369981472908463275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12715895306567855511804133 2384230369981472908463275)
        ·
          refine ⟨3576345554972209362694913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2384230369981472908463275 3576345554972209362694913)
          ·
            refine ⟨2682259166229157022021185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3576345554972209362694913 2682259166229157022021185)
            ·
              refine ⟨2011694374671867766515889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2682259166229157022021185 2011694374671867766515889)
              ·
                refine ⟨1508770781003900824886917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2011694374671867766515889 1508770781003900824886917)
                ·
                  refine ⟨282894521438231404666297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1508770781003900824886917 282894521438231404666297)
                  ·
                    rfl

theorem cell22_2479208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 2, 2, 4].length) (baseStart_2479208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2479208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2479208 prefixEnd_2479208 := by exact prefixLift 2479208
  have htrace : WordTrace (prefixWord ++ tailWord_2479208) baseStart_2479208 baseEnd_2479208 := by
    simpa [prefixWord, tailWord_2479208, baseEnd_2479208] using wordTrace_append hprefix tailTrace_2479208
  have hstable : (prefixWord ++ tailWord_2479208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2479208).length < 2 ^ (prefixWord ++ tailWord_2479208).sum := by decide
  have hdescent : baseEnd_2479208 < baseStart_2479208 := by decide
  rcases family_descends (prefixWord ++ tailWord_2479208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2479292 : List Nat := [2, 2, 2, 3, 2, 1, 2, 2, 6]
def baseStart_2479292 : Nat := 118140960795 + 2479292 * 2 ^ 59
def prefixEnd_2479292 : Nat := 4983230072969 + 3 ^ 40 * 2479292 * 2
def baseEnd_2479292 : Nat := 282904106410448664966211

theorem tailTrace_2479292 : CollatzResearch.WordTrace tailWord_2479292 prefixEnd_2479292 282904106410448664966211 := by
  unfold tailWord_2479292
  simp only [CollatzResearch.WordTrace]
  refine ⟨45213604066977994103888065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60284805422637325471850753 45213604066977994103888065)
  ·
    refine ⟨33910203050233495577916049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45213604066977994103888065 33910203050233495577916049)
    ·
      refine ⟨25432652287675121683437037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33910203050233495577916049 25432652287675121683437037)
      ·
        refine ⟨9537244607878170631288889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25432652287675121683437037 9537244607878170631288889)
        ·
          refine ⟨7152933455908627973466667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9537244607878170631288889 7152933455908627973466667)
          ·
            refine ⟨10729400183862941960200001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7152933455908627973466667 10729400183862941960200001)
            ·
              refine ⟨8047050137897206470150001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10729400183862941960200001 8047050137897206470150001)
              ·
                refine ⟨6035287603422904852612501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8047050137897206470150001 6035287603422904852612501)
                ·
                  refine ⟨282904106410448664966211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6035287603422904852612501 282904106410448664966211)
                  ·
                    rfl

theorem cell22_2479292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 2, 6].length) (baseStart_2479292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2479292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2479292 prefixEnd_2479292 := by exact prefixLift 2479292
  have htrace : WordTrace (prefixWord ++ tailWord_2479292) baseStart_2479292 baseEnd_2479292 := by
    simpa [prefixWord, tailWord_2479292, baseEnd_2479292] using wordTrace_append hprefix tailTrace_2479292
  have hstable : (prefixWord ++ tailWord_2479292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2479292).length < 2 ^ (prefixWord ++ tailWord_2479292).sum := by decide
  have hdescent : baseEnd_2479292 < baseStart_2479292 := by decide
  rcases family_descends (prefixWord ++ tailWord_2479292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2479294 : List Nat := [4, 2, 1, 1, 3, 1, 1, 4, 1, 4]
def baseStart_2479294 : Nat := 118140960795 + 2479294 * 2 ^ 59
def prefixEnd_2479294 : Nat := 4983230072969 + 3 ^ 40 * 2479294 * 2
def baseEnd_2479294 : Nat := 848713003872218656348627

theorem tailTrace_2479294 : CollatzResearch.WordTrace tailWord_2479294 prefixEnd_2479294 848713003872218656348627 := by
  unfold tailWord_2479294
  simp only [CollatzResearch.WordTrace]
  refine ⟨11303410134993592818668617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60284854053299161699565957 11303410134993592818668617)
  ·
    refine ⟨8477557601245194614001463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11303410134993592818668617 8477557601245194614001463)
    ·
      refine ⟨12716336401867791921002195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8477557601245194614001463 12716336401867791921002195)
      ·
        refine ⟨19074504602801687881503293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12716336401867791921002195 19074504602801687881503293)
        ·
          refine ⟨7152939226050632955563735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19074504602801687881503293 7152939226050632955563735)
          ·
            refine ⟨10729408839075949433345603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7152939226050632955563735 10729408839075949433345603)
            ·
              refine ⟨16094113258613924150018405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10729408839075949433345603 16094113258613924150018405)
              ·
                refine ⟨3017646235990110778128451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16094113258613924150018405 3017646235990110778128451)
                ·
                  refine ⟨4526469353985166167192677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3017646235990110778128451 4526469353985166167192677)
                  ·
                    refine ⟨848713003872218656348627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4526469353985166167192677 848713003872218656348627)
                    ·
                      rfl

theorem cell22_2479294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 4, 1, 4].length) (baseStart_2479294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2479294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2479294 prefixEnd_2479294 := by exact prefixLift 2479294
  have htrace : WordTrace (prefixWord ++ tailWord_2479294) baseStart_2479294 baseEnd_2479294 := by
    simpa [prefixWord, tailWord_2479294, baseEnd_2479294] using wordTrace_append hprefix tailTrace_2479294
  have hstable : (prefixWord ++ tailWord_2479294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2479294).length < 2 ^ (prefixWord ++ tailWord_2479294).sum := by decide
  have hdescent : baseEnd_2479294 < baseStart_2479294 := by decide
  rcases family_descends (prefixWord ++ tailWord_2479294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2479341 : List Nat := [1, 5, 1, 2, 2, 2, 1, 3, 2, 3]
def baseStart_2479341 : Nat := 118140960795 + 2479341 * 2 ^ 59
def prefixEnd_2479341 : Nat := 4983230072969 + 3 ^ 40 * 2479341 * 2
def baseEnd_2479341 : Nat := 848729092932726200423483

theorem tailTrace_2479341 : CollatzResearch.WordTrace tailWord_2479341 prefixEnd_2479341 848729092932726200423483 := by
  unfold tailWord_2479341
  simp only [CollatzResearch.WordTrace]
  refine ⟨90428995310778469576309877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60285996873852313050873251 90428995310778469576309877)
  ·
    refine ⟨8477718310385481522779051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 90428995310778469576309877 8477718310385481522779051)
    ·
      refine ⟨12716577465578222284168577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8477718310385481522779051 12716577465578222284168577)
      ·
        refine ⟨9537433099183666713126433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12716577465578222284168577 9537433099183666713126433)
        ·
          refine ⟨7153074824387750034844825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9537433099183666713126433 7153074824387750034844825)
          ·
            refine ⟨5364806118290812526133619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7153074824387750034844825 5364806118290812526133619)
            ·
              refine ⟨8047209177436218789200429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5364806118290812526133619 8047209177436218789200429)
              ·
                refine ⟨3017703441538582045950161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8047209177436218789200429 3017703441538582045950161)
                ·
                  refine ⟨2263277581153936534462621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3017703441538582045950161 2263277581153936534462621)
                  ·
                    refine ⟨848729092932726200423483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2263277581153936534462621 848729092932726200423483)
                    ·
                      rfl

theorem cell22_2479341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 3, 2, 3].length) (baseStart_2479341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2479341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2479341 prefixEnd_2479341 := by exact prefixLift 2479341
  have htrace : WordTrace (prefixWord ++ tailWord_2479341) baseStart_2479341 baseEnd_2479341 := by
    simpa [prefixWord, tailWord_2479341, baseEnd_2479341] using wordTrace_append hprefix tailTrace_2479341
  have hstable : (prefixWord ++ tailWord_2479341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2479341).length < 2 ^ (prefixWord ++ tailWord_2479341).sum := by decide
  have hdescent : baseEnd_2479341 < baseStart_2479341 := by decide
  rcases family_descends (prefixWord ++ tailWord_2479341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2479397 : List Nat := [1, 3, 1, 2, 4, 1, 1, 1, 1, 7]
def baseStart_2479397 : Nat := 118140960795 + 2479397 * 2 ^ 59
def prefixEnd_2479397 : Nat := 4983230072969 + 3 ^ 40 * 2479397 * 2
def baseEnd_2479397 : Nat := 848748262877160721023311

theorem tailTrace_2479397 : CollatzResearch.WordTrace tailWord_2479397 prefixEnd_2479397 848748262877160721023311 := by
  unfold tailWord_2479397
  simp only [CollatzResearch.WordTrace]
  refine ⟨90431037798575591140348445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60287358532383727426898963 90431037798575591140348445)
  ·
    refine ⟨33911639174465846677630667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90431037798575591140348445 33911639174465846677630667)
    ·
      refine ⟨50867458761698770016446001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33911639174465846677630667 50867458761698770016446001)
      ·
        refine ⟨38150594071274077512334501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50867458761698770016446001 38150594071274077512334501)
        ·
          refine ⟨7153236388363889533562719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38150594071274077512334501 7153236388363889533562719)
          ·
            refine ⟨10729854582545834300344079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7153236388363889533562719 10729854582545834300344079)
            ·
              refine ⟨16094781873818751450516119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10729854582545834300344079 16094781873818751450516119)
              ·
                refine ⟨24142172810728127175774179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16094781873818751450516119 24142172810728127175774179)
                ·
                  refine ⟨36213259216092190763661269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24142172810728127175774179 36213259216092190763661269)
                  ·
                    refine ⟨848748262877160721023311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36213259216092190763661269 848748262877160721023311)
                    ·
                      rfl

theorem cell22_2479397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 1, 1, 7].length) (baseStart_2479397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2479397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2479397 prefixEnd_2479397 := by exact prefixLift 2479397
  have htrace : WordTrace (prefixWord ++ tailWord_2479397) baseStart_2479397 baseEnd_2479397 := by
    simpa [prefixWord, tailWord_2479397, baseEnd_2479397] using wordTrace_append hprefix tailTrace_2479397
  have hstable : (prefixWord ++ tailWord_2479397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2479397).length < 2 ^ (prefixWord ++ tailWord_2479397).sum := by decide
  have hdescent : baseEnd_2479397 < baseStart_2479397 := by decide
  rcases family_descends (prefixWord ++ tailWord_2479397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2479444 : List Nat := [2, 4, 1, 1, 2, 1, 4, 1, 6]
def baseStart_2479444 : Nat := 118140960795 + 2479444 * 2 ^ 59
def prefixEnd_2479444 : Nat := 4983230072969 + 3 ^ 40 * 2479444 * 2
def baseEnd_2479444 : Nat := 282921450645889421699389

theorem tailTrace_2479444 : CollatzResearch.WordTrace tailWord_2479444 prefixEnd_2479444 282921450645889421699389 := by
  unfold tailWord_2479444
  simp only [CollatzResearch.WordTrace]
  refine ⟨45216376014702659083654693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60288501352936878778206257 45216376014702659083654693)
  ·
    refine ⟨8478070502756748578185255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45216376014702659083654693 8478070502756748578185255)
    ·
      refine ⟨12717105754135122867277883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8478070502756748578185255 12717105754135122867277883)
      ·
        refine ⟨19075658631202684300916825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12717105754135122867277883 19075658631202684300916825)
        ·
          refine ⟨14306743973402013225687619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19075658631202684300916825 14306743973402013225687619)
          ·
            refine ⟨21460115960103019838531429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14306743973402013225687619 21460115960103019838531429)
            ·
              refine ⟨4023771742519316219724643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21460115960103019838531429 4023771742519316219724643)
              ·
                refine ⟨6035657613778974329586965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4023771742519316219724643 6035657613778974329586965)
                ·
                  refine ⟨282921450645889421699389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6035657613778974329586965 282921450645889421699389)
                  ·
                    rfl

theorem cell22_2479444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 1, 6].length) (baseStart_2479444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2479444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2479444 prefixEnd_2479444 := by exact prefixLift 2479444
  have htrace : WordTrace (prefixWord ++ tailWord_2479444) baseStart_2479444 baseEnd_2479444 := by
    simpa [prefixWord, tailWord_2479444, baseEnd_2479444] using wordTrace_append hprefix tailTrace_2479444
  have hstable : (prefixWord ++ tailWord_2479444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2479444).length < 2 ^ (prefixWord ++ tailWord_2479444).sum := by decide
  have hdescent : baseEnd_2479444 < baseStart_2479444 := by decide
  rcases family_descends (prefixWord ++ tailWord_2479444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2479459 : List Nat := [1, 1, 1, 5, 2, 2, 3, 1, 1, 5]
def baseStart_2479459 : Nat := 118140960795 + 2479459 * 2 ^ 59
def prefixEnd_2479459 : Nat := 4983230072969 + 3 ^ 40 * 2479459 * 2
def baseEnd_2479459 : Nat := 848769486744213225973121

theorem tailTrace_2479459 : CollatzResearch.WordTrace tailWord_2479459 prefixEnd_2479459 848769486744213225973121 := by
  unfold tailWord_2479459
  simp only [CollatzResearch.WordTrace]
  refine ⟨90433299124350975729105431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60288866082900650486070287 90433299124350975729105431)
  ·
    refine ⟨135649948686526463593658147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90433299124350975729105431 135649948686526463593658147)
    ·
      refine ⟨203474923029789695390487221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135649948686526463593658147 203474923029789695390487221)
      ·
        refine ⟨19075774034042783942858177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 203474923029789695390487221 19075774034042783942858177)
        ·
          refine ⟨14306830525532087957143633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19075774034042783942858177 14306830525532087957143633)
          ·
            refine ⟨10730122894149065967857725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14306830525532087957143633 10730122894149065967857725)
            ·
              refine ⟨4023796085305899737946647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10730122894149065967857725 4023796085305899737946647)
              ·
                refine ⟨6035694127958849606919971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4023796085305899737946647 6035694127958849606919971)
                ·
                  refine ⟨9053541191938274410379957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6035694127958849606919971 9053541191938274410379957)
                  ·
                    refine ⟨848769486744213225973121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9053541191938274410379957 848769486744213225973121)
                    ·
                      rfl

theorem cell22_2479459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 1, 1, 5].length) (baseStart_2479459 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2479459 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2479459 prefixEnd_2479459 := by exact prefixLift 2479459
  have htrace : WordTrace (prefixWord ++ tailWord_2479459) baseStart_2479459 baseEnd_2479459 := by
    simpa [prefixWord, tailWord_2479459, baseEnd_2479459] using wordTrace_append hprefix tailTrace_2479459
  have hstable : (prefixWord ++ tailWord_2479459).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2479459).length < 2 ^ (prefixWord ++ tailWord_2479459).sum := by decide
  have hdescent : baseEnd_2479459 < baseStart_2479459 := by decide
  rcases family_descends (prefixWord ++ tailWord_2479459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2479472 : List Nat := [2, 1, 1, 1, 4, 2, 3, 8]
def baseStart_2479472 : Nat := 118140960795 + 2479472 * 2 ^ 59
def prefixEnd_2479472 : Nat := 4983230072969 + 3 ^ 40 * 2479472 * 2
def baseEnd_2479472 : Nat := 94308215212209502822009

theorem tailTrace_2479472 : CollatzResearch.WordTrace tailWord_2479472 prefixEnd_2479472 94308215212209502822009 := by
  unfold tailWord_2479472
  simp only [CollatzResearch.WordTrace]
  refine ⟨45216886636651939474664335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60289182182202585966219113 45216886636651939474664335)
  ·
    refine ⟨67825329954977909211996503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45216886636651939474664335 67825329954977909211996503)
    ·
      refine ⟨101737994932466863817994755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67825329954977909211996503 101737994932466863817994755)
      ·
        refine ⟨152606992398700295726992133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101737994932466863817994755 152606992398700295726992133)
        ·
          refine ⟨28613811074756305448811025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 152606992398700295726992133 28613811074756305448811025)
          ·
            refine ⟨21460358306067229086608269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28613811074756305448811025 21460358306067229086608269)
            ·
              refine ⟨8047634364775210907478101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21460358306067229086608269 8047634364775210907478101)
              ·
                refine ⟨94308215212209502822009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8047634364775210907478101 94308215212209502822009)
                ·
                  rfl

theorem cell22_2479472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 8].length) (baseStart_2479472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2479472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2479472 prefixEnd_2479472 := by exact prefixLift 2479472
  have htrace : WordTrace (prefixWord ++ tailWord_2479472) baseStart_2479472 baseEnd_2479472 := by
    simpa [prefixWord, tailWord_2479472, baseEnd_2479472] using wordTrace_append hprefix tailTrace_2479472
  have hstable : (prefixWord ++ tailWord_2479472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2479472).length < 2 ^ (prefixWord ++ tailWord_2479472).sum := by decide
  have hdescent : baseEnd_2479472 < baseStart_2479472 := by decide
  rcases family_descends (prefixWord ++ tailWord_2479472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2479474 : List Nat := [3, 2, 1, 2, 1, 2, 2, 3, 2, 4]
def baseStart_2479474 : Nat := 118140960795 + 2479474 * 2 ^ 59
def prefixEnd_2479474 : Nat := 4983230072969 + 3 ^ 40 * 2479474 * 2
def baseEnd_2479474 : Nat := 848774621550758186848075

theorem tailTrace_2479474 : CollatzResearch.WordTrace tailWord_2479474 prefixEnd_2479474 848774621550758186848075 := by
  unfold tailWord_2479474
  simp only [CollatzResearch.WordTrace]
  refine ⟨22608461554824158322725369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60289230812864422193934317 22608461554824158322725369)
  ·
    refine ⟨16956346166118118742044027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22608461554824158322725369 16956346166118118742044027)
    ·
      refine ⟨25434519249177178113066041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16956346166118118742044027 25434519249177178113066041)
      ·
        refine ⟨19075889436882883584799531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25434519249177178113066041 19075889436882883584799531)
        ·
          refine ⟨28613834155324325377199297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19075889436882883584799531 28613834155324325377199297)
          ·
            refine ⟨21460375616493244032899473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28613834155324325377199297 21460375616493244032899473)
            ·
              refine ⟨16095281712369933024674605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21460375616493244032899473 16095281712369933024674605)
              ·
                refine ⟨6035730642138724884252977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16095281712369933024674605 6035730642138724884252977)
                ·
                  refine ⟨4526797981604043663189733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6035730642138724884252977 4526797981604043663189733)
                  ·
                    refine ⟨848774621550758186848075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4526797981604043663189733 848774621550758186848075)
                    ·
                      rfl

theorem cell22_2479474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 3, 2, 4].length) (baseStart_2479474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2479474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2479474 prefixEnd_2479474 := by exact prefixLift 2479474
  have htrace : WordTrace (prefixWord ++ tailWord_2479474) baseStart_2479474 baseEnd_2479474 := by
    simpa [prefixWord, tailWord_2479474, baseEnd_2479474] using wordTrace_append hprefix tailTrace_2479474
  have hstable : (prefixWord ++ tailWord_2479474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2479474).length < 2 ^ (prefixWord ++ tailWord_2479474).sum := by decide
  have hdescent : baseEnd_2479474 < baseStart_2479474 := by decide
  rcases family_descends (prefixWord ++ tailWord_2479474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2479549 : List Nat := [1, 4, 1, 2, 2, 1, 2, 2, 2, 5]
def baseStart_2479549 : Nat := 118140960795 + 2479549 * 2 ^ 59
def prefixEnd_2479549 : Nat := 4983230072969 + 3 ^ 40 * 2479549 * 2
def baseEnd_2479549 : Nat := 848800295583482991222845

theorem tailTrace_2479549 : CollatzResearch.WordTrace tailWord_2479549 prefixEnd_2479549 848800295583482991222845 := by
  unfold tailWord_2479549
  simp only [CollatzResearch.WordTrace]
  refine ⟨90436581694024921099881701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60291054462683280733254467 90436581694024921099881701)
  ·
    refine ⟨16956859067629672706227819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90436581694024921099881701 16956859067629672706227819)
    ·
      refine ⟨25435288601444509059341729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16956859067629672706227819 25435288601444509059341729)
      ·
        refine ⟨19076466451083381794506297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25435288601444509059341729 19076466451083381794506297)
        ·
          refine ⟨14307349838312536345879723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19076466451083381794506297 14307349838312536345879723)
          ·
            refine ⟨21461024757468804518819585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14307349838312536345879723 21461024757468804518819585)
            ·
              refine ⟨16095768568101603389114689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21461024757468804518819585 16095768568101603389114689)
              ·
                refine ⟨12071826426076202541836017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16095768568101603389114689 12071826426076202541836017)
                ·
                  refine ⟨9053869819557151906377013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12071826426076202541836017 9053869819557151906377013)
                  ·
                    refine ⟨848800295583482991222845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9053869819557151906377013 848800295583482991222845)
                    ·
                      rfl

theorem cell22_2479549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 2, 2, 5].length) (baseStart_2479549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2479549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2479549 prefixEnd_2479549 := by exact prefixLift 2479549
  have htrace : WordTrace (prefixWord ++ tailWord_2479549) baseStart_2479549 baseEnd_2479549 := by
    simpa [prefixWord, tailWord_2479549, baseEnd_2479549] using wordTrace_append hprefix tailTrace_2479549
  have hstable : (prefixWord ++ tailWord_2479549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2479549).length < 2 ^ (prefixWord ++ tailWord_2479549).sum := by decide
  have hdescent : baseEnd_2479549 < baseStart_2479549 := by decide
  rcases family_descends (prefixWord ++ tailWord_2479549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2479581 : List Nat := [1, 4, 3, 1, 1, 2, 2, 1, 3, 4]
def baseStart_2479581 : Nat := 118140960795 + 2479581 * 2 ^ 59
def prefixEnd_2479581 : Nat := 4983230072969 + 3 ^ 40 * 2479581 * 2
def baseEnd_2479581 : Nat := 848811249837445574422747

theorem tailTrace_2479581 : CollatzResearch.WordTrace tailWord_2479581 prefixEnd_2479581 848811249837445574422747 := by
  unfold tailWord_2479581
  simp only [CollatzResearch.WordTrace]
  refine ⟨90437748829908990565046597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60291832553272660376697731 90437748829908990565046597)
  ·
    refine ⟨16957077905607935730946237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90437748829908990565046597 16957077905607935730946237)
    ·
      refine ⟨6358904214602975899104839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16957077905607935730946237 6358904214602975899104839)
      ·
        refine ⟨9538356321904463848657259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6358904214602975899104839 9538356321904463848657259)
        ·
          refine ⟨14307534482856695772985889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9538356321904463848657259 14307534482856695772985889)
          ·
            refine ⟨10730650862142521829739417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14307534482856695772985889 10730650862142521829739417)
            ·
              refine ⟨8047988146606891372304563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10730650862142521829739417 8047988146606891372304563)
              ·
                refine ⟨12071982219910337058456845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8047988146606891372304563 12071982219910337058456845)
                ·
                  refine ⟨4526993332466376396921317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12071982219910337058456845 4526993332466376396921317)
                  ·
                    refine ⟨848811249837445574422747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4526993332466376396921317 848811249837445574422747)
                    ·
                      rfl

theorem cell22_2479581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_2479581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2479581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2479581 prefixEnd_2479581 := by exact prefixLift 2479581
  have htrace : WordTrace (prefixWord ++ tailWord_2479581) baseStart_2479581 baseEnd_2479581 := by
    simpa [prefixWord, tailWord_2479581, baseEnd_2479581] using wordTrace_append hprefix tailTrace_2479581
  have hstable : (prefixWord ++ tailWord_2479581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2479581).length < 2 ^ (prefixWord ++ tailWord_2479581).sum := by decide
  have hdescent : baseEnd_2479581 < baseStart_2479581 := by decide
  rcases family_descends (prefixWord ++ tailWord_2479581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2479609 : List Nat := [1, 2, 1, 3, 1, 2, 1, 3, 4, 4]
def baseStart_2479609 : Nat := 118140960795 + 2479609 * 2 ^ 59
def prefixEnd_2479609 : Nat := 4983230072969 + 3 ^ 40 * 2479609 * 2
def baseEnd_2479609 : Nat := 848820834809662834722661

theorem tailTrace_2479609 : CollatzResearch.WordTrace tailWord_2479609 prefixEnd_2479609 848820834809662834722661 := by
  unfold tailWord_2479609
  simp only [CollatzResearch.WordTrace]
  refine ⟨90438770073807551347065881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60292513382538367564710587 90438770073807551347065881)
  ·
    refine ⟨67829077555355663510299411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90438770073807551347065881 67829077555355663510299411)
    ·
      refine ⟨101743616333033495265449117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67829077555355663510299411 101743616333033495265449117)
      ·
        refine ⟨38153856124887560724543419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101743616333033495265449117 38153856124887560724543419)
        ·
          refine ⟨57230784187331341086815129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38153856124887560724543419 57230784187331341086815129)
          ·
            refine ⟨42923088140498505815111347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57230784187331341086815129 42923088140498505815111347)
            ·
              refine ⟨64384632210747758722667021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42923088140498505815111347 64384632210747758722667021)
              ·
                refine ⟨24144237079030409521000133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64384632210747758722667021 24144237079030409521000133)
                ·
                  refine ⟨4527044452318201785187525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24144237079030409521000133 4527044452318201785187525)
                  ·
                    refine ⟨848820834809662834722661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4527044452318201785187525 848820834809662834722661)
                    ·
                      rfl

theorem cell22_2479609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 3, 4, 4].length) (baseStart_2479609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2479609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2479609 prefixEnd_2479609 := by exact prefixLift 2479609
  have htrace : WordTrace (prefixWord ++ tailWord_2479609) baseStart_2479609 baseEnd_2479609 := by
    simpa [prefixWord, tailWord_2479609, baseEnd_2479609] using wordTrace_append hprefix tailTrace_2479609
  have hstable : (prefixWord ++ tailWord_2479609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2479609).length < 2 ^ (prefixWord ++ tailWord_2479609).sum := by decide
  have hdescent : baseEnd_2479609 < baseStart_2479609 := by decide
  rcases family_descends (prefixWord ++ tailWord_2479609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2479628 : List Nat := [2, 2, 1, 2, 5, 2, 1, 1, 1, 5]
def baseStart_2479628 : Nat := 118140960795 + 2479628 * 2 ^ 59
def prefixEnd_2479628 : Nat := 4983230072969 + 3 ^ 40 * 2479628 * 2
def baseEnd_2479628 : Nat := 848827338897953118497603

theorem tailTrace_2479628 : CollatzResearch.WordTrace tailWord_2479628 prefixEnd_2479628 848827338897953118497603 := by
  unfold tailWord_2479628
  simp only [CollatzResearch.WordTrace]
  refine ⟨45219731530369358796003769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60292975373825811728005025 45219731530369358796003769)
  ·
    refine ⟨33914798647777019097002827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45219731530369358796003769 33914798647777019097002827)
    ·
      refine ⟨50872197971665528645504241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33914798647777019097002827 50872197971665528645504241)
      ·
        refine ⟨38154148478749146484128181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50872197971665528645504241 38154148478749146484128181)
        ·
          refine ⟨3576951419882732482887017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38154148478749146484128181 3576951419882732482887017)
          ·
            refine ⟨2682713564912049362165263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3576951419882732482887017 2682713564912049362165263)
            ·
              refine ⟨4024070347368074043247895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2682713564912049362165263 4024070347368074043247895)
              ·
                refine ⟨6036105521052111064871843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4024070347368074043247895 6036105521052111064871843)
                ·
                  refine ⟨9054158281578166597307765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6036105521052111064871843 9054158281578166597307765)
                  ·
                    refine ⟨848827338897953118497603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9054158281578166597307765 848827338897953118497603)
                    ·
                      rfl

theorem cell22_2479628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 1, 1, 5].length) (baseStart_2479628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2479628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2479628 prefixEnd_2479628 := by exact prefixLift 2479628
  have htrace : WordTrace (prefixWord ++ tailWord_2479628) baseStart_2479628 baseEnd_2479628 := by
    simpa [prefixWord, tailWord_2479628, baseEnd_2479628] using wordTrace_append hprefix tailTrace_2479628
  have hstable : (prefixWord ++ tailWord_2479628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2479628).length < 2 ^ (prefixWord ++ tailWord_2479628).sum := by decide
  have hdescent : baseEnd_2479628 < baseStart_2479628 := by decide
  rcases family_descends (prefixWord ++ tailWord_2479628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2479673 : List Nat := [1, 2, 1, 5, 1, 2, 3, 1, 3, 3]
def baseStart_2479673 : Nat := 118140960795 + 2479673 * 2 ^ 59
def prefixEnd_2479673 : Nat := 4983230072969 + 3 ^ 40 * 2479673 * 2
def baseEnd_2479673 : Nat := 848842743317588001122465

theorem tailTrace_2479673 : CollatzResearch.WordTrace tailWord_2479673 prefixEnd_2479673 848842743317588001122465 := by
  unfold tailWord_2479673
  simp only [CollatzResearch.WordTrace]
  refine ⟨90441104345575690277395673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60294069563717126851597115 90441104345575690277395673)
  ·
    refine ⟨67830828259181767708046755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90441104345575690277395673 67830828259181767708046755)
    ·
      refine ⟨101746242388772651562070133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67830828259181767708046755 101746242388772651562070133)
      ·
        refine ⟨9538710223947436083944075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 101746242388772651562070133 9538710223947436083944075)
        ·
          refine ⟨14308065335921154125916113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9538710223947436083944075 14308065335921154125916113)
          ·
            refine ⟨10731049001940865594437085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14308065335921154125916113 10731049001940865594437085)
            ·
              refine ⟨4024143375727824597913907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10731049001940865594437085 4024143375727824597913907)
              ·
                refine ⟨6036215063591736896870861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4024143375727824597913907 6036215063591736896870861)
                ·
                  refine ⟨2263580648846901336326573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6036215063591736896870861 2263580648846901336326573)
                  ·
                    refine ⟨848842743317588001122465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2263580648846901336326573 848842743317588001122465)
                    ·
                      rfl

theorem cell22_2479673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 1, 3, 3].length) (baseStart_2479673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2479673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2479673 prefixEnd_2479673 := by exact prefixLift 2479673
  have htrace : WordTrace (prefixWord ++ tailWord_2479673) baseStart_2479673 baseEnd_2479673 := by
    simpa [prefixWord, tailWord_2479673, baseEnd_2479673] using wordTrace_append hprefix tailTrace_2479673
  have hstable : (prefixWord ++ tailWord_2479673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2479673).length < 2 ^ (prefixWord ++ tailWord_2479673).sum := by decide
  have hdescent : baseEnd_2479673 < baseStart_2479673 := by decide
  rcases family_descends (prefixWord ++ tailWord_2479673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2479733 : List Nat := [1, 3, 4, 2, 1, 1, 1, 2, 3, 4]
def baseStart_2479733 : Nat := 118140960795 + 2479733 * 2 ^ 59
def prefixEnd_2479733 : Nat := 4983230072969 + 3 ^ 40 * 2479733 * 2
def baseEnd_2479733 : Nat := 848863282543767844622281

theorem tailTrace_2479733 : CollatzResearch.WordTrace tailWord_2479733 prefixEnd_2479733 848863282543767844622281 := by
  unfold tailWord_2479733
  simp only [CollatzResearch.WordTrace]
  refine ⟨90443292725358320524579853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60295528483572213683053235 90443292725358320524579853)
  ·
    refine ⟨33916234772009370196717445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90443292725358320524579853 33916234772009370196717445)
    ·
      refine ⟨6359294019751756911884521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33916234772009370196717445 6359294019751756911884521)
      ·
        refine ⟨4769470514813817683913391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6359294019751756911884521 4769470514813817683913391)
        ·
          refine ⟨7154205772220726525870087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4769470514813817683913391 7154205772220726525870087)
          ·
            refine ⟨10731308658331089788805131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7154205772220726525870087 10731308658331089788805131)
            ·
              refine ⟨16096962987496634683207697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10731308658331089788805131 16096962987496634683207697)
              ·
                refine ⟨12072722240622476012405773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16096962987496634683207697 12072722240622476012405773)
                ·
                  refine ⟨4527270840233428504652165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12072722240622476012405773 4527270840233428504652165)
                  ·
                    refine ⟨848863282543767844622281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4527270840233428504652165 848863282543767844622281)
                    ·
                      rfl

theorem cell22_2479733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_2479733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2479733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2479733 prefixEnd_2479733 := by exact prefixLift 2479733
  have htrace : WordTrace (prefixWord ++ tailWord_2479733) baseStart_2479733 baseEnd_2479733 := by
    simpa [prefixWord, tailWord_2479733, baseEnd_2479733] using wordTrace_append hprefix tailTrace_2479733
  have hstable : (prefixWord ++ tailWord_2479733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2479733).length < 2 ^ (prefixWord ++ tailWord_2479733).sum := by decide
  have hdescent : baseEnd_2479733 < baseStart_2479733 := by decide
  rcases family_descends (prefixWord ++ tailWord_2479733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2479748 : List Nat := [2, 3, 2, 1, 4, 1, 1, 2, 6]
def baseStart_2479748 : Nat := 118140960795 + 2479748 * 2 ^ 59
def prefixEnd_2479748 : Nat := 4983230072969 + 3 ^ 40 * 2479748 * 2
def baseEnd_2479748 : Nat := 282956139116770935165745

theorem tailTrace_2479748 : CollatzResearch.WordTrace tailWord_2479748 prefixEnd_2479748 282956139116770935165745 := by
  unfold tailWord_2479748
  simp only [CollatzResearch.WordTrace]
  refine ⟨45221919910151989043187949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60295893213535985390917265 45221919910151989043187949)
  ·
    refine ⟨16958219966306995891195481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45221919910151989043187949 16958219966306995891195481)
    ·
      refine ⟨12718664974730246918396611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16958219966306995891195481 12718664974730246918396611)
      ·
        refine ⟨19077997462095370377594917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12718664974730246918396611 19077997462095370377594917)
        ·
          refine ⟨3577124524142881945799047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19077997462095370377594917 3577124524142881945799047)
          ·
            refine ⟨5365686786214322918698571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3577124524142881945799047 5365686786214322918698571)
            ·
              refine ⟨8048530179321484378047857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5365686786214322918698571 8048530179321484378047857)
              ·
                refine ⟨6036397634491113283535893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8048530179321484378047857 6036397634491113283535893)
                ·
                  refine ⟨282956139116770935165745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6036397634491113283535893 282956139116770935165745)
                  ·
                    rfl

theorem cell22_2479748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 2, 6].length) (baseStart_2479748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2479748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2479748 prefixEnd_2479748 := by exact prefixLift 2479748
  have htrace : WordTrace (prefixWord ++ tailWord_2479748) baseStart_2479748 baseEnd_2479748 := by
    simpa [prefixWord, tailWord_2479748, baseEnd_2479748] using wordTrace_append hprefix tailTrace_2479748
  have hstable : (prefixWord ++ tailWord_2479748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2479748).length < 2 ^ (prefixWord ++ tailWord_2479748).sum := by decide
  have hdescent : baseEnd_2479748 < baseStart_2479748 := by decide
  rcases family_descends (prefixWord ++ tailWord_2479748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2479761 : List Nat := [1, 2, 2, 1, 1, 1, 1, 7, 2, 4]
def baseStart_2479761 : Nat := 118140960795 + 2479761 * 2 ^ 59
def prefixEnd_2479761 : Nat := 4983230072969 + 3 ^ 40 * 2479761 * 2
def baseEnd_2479761 : Nat := 848872867515985104922195

theorem tailTrace_2479761 : CollatzResearch.WordTrace tailWord_2479761 prefixEnd_2479761 848872867515985104922195 := by
  unfold tailWord_2479761
  simp only [CollatzResearch.WordTrace]
  refine ⟨90444313969256881306599137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60296209312837920871066091 90444313969256881306599137)
  ·
    refine ⟨67833235476942660979949353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90444313969256881306599137 67833235476942660979949353)
    ·
      refine ⟨50874926607706995734962015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67833235476942660979949353 50874926607706995734962015)
      ·
        refine ⟨76312389911560493602443023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50874926607706995734962015 76312389911560493602443023)
        ·
          refine ⟨114468584867340740403664535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76312389911560493602443023 114468584867340740403664535)
          ·
            refine ⟨171702877301011110605496803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114468584867340740403664535 171702877301011110605496803)
            ·
              refine ⟨257554315951516665908245205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 171702877301011110605496803 257554315951516665908245205)
              ·
                refine ⟨6036429280113671857224497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 257554315951516665908245205 6036429280113671857224497)
                ·
                  refine ⟨4527321960085253892918373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6036429280113671857224497 4527321960085253892918373)
                  ·
                    refine ⟨848872867515985104922195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4527321960085253892918373 848872867515985104922195)
                    ·
                      rfl

theorem cell22_2479761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 4].length) (baseStart_2479761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2479761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2479761 prefixEnd_2479761 := by exact prefixLift 2479761
  have htrace : WordTrace (prefixWord ++ tailWord_2479761) baseStart_2479761 baseEnd_2479761 := by
    simpa [prefixWord, tailWord_2479761, baseEnd_2479761] using wordTrace_append hprefix tailTrace_2479761
  have hstable : (prefixWord ++ tailWord_2479761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2479761).length < 2 ^ (prefixWord ++ tailWord_2479761).sum := by decide
  have hdescent : baseEnd_2479761 < baseStart_2479761 := by decide
  rcases family_descends (prefixWord ++ tailWord_2479761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2479776 : List Nat := [2, 1, 1, 4, 3, 2, 9]
def baseStart_2479776 : Nat := 118140960795 + 2479776 * 2 ^ 59
def prefixEnd_2479776 : Nat := 4983230072969 + 3 ^ 40 * 2479776 * 2
def baseEnd_2479776 : Nat := 31439926011945557992487

theorem tailTrace_2479776 : CollatzResearch.WordTrace tailWord_2479776 prefixEnd_2479776 31439926011945557992487 := by
  unfold tailWord_2479776
  simp only [CollatzResearch.WordTrace]
  refine ⟨45222430532101269434197591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60296574042801692578930121 45222430532101269434197591)
  ·
    refine ⟨67833645798151904151296387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45222430532101269434197591 67833645798151904151296387)
    ·
      refine ⟨101750468697227856226944581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67833645798151904151296387 101750468697227856226944581)
      ·
        refine ⟨19078212880730223042552109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 101750468697227856226944581 19078212880730223042552109)
        ·
          refine ⟨7154329830273833640957041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19078212880730223042552109 7154329830273833640957041)
          ·
            refine ⟨5365747372705375230717781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7154329830273833640957041 5365747372705375230717781)
            ·
              refine ⟨31439926011945557992487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5365747372705375230717781 31439926011945557992487)
              ·
                rfl

theorem cell22_2479776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 9].length) (baseStart_2479776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2479776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2479776 prefixEnd_2479776 := by exact prefixLift 2479776
  have htrace : WordTrace (prefixWord ++ tailWord_2479776) baseStart_2479776 baseEnd_2479776 := by
    simpa [prefixWord, tailWord_2479776, baseEnd_2479776] using wordTrace_append hprefix tailTrace_2479776
  have hstable : (prefixWord ++ tailWord_2479776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2479776).length < 2 ^ (prefixWord ++ tailWord_2479776).sum := by decide
  have hdescent : baseEnd_2479776 < baseStart_2479776 := by decide
  rcases family_descends (prefixWord ++ tailWord_2479776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2479780 : List Nat := [2, 3, 1, 2, 2, 2, 3, 2, 2, 3]
def baseStart_2479780 : Nat := 118140960795 + 2479780 * 2 ^ 59
def prefixEnd_2479780 : Nat := 4983230072969 + 3 ^ 40 * 2479780 * 2
def baseEnd_2479780 : Nat := 848879371604275388697137

theorem tailTrace_2479780 : CollatzResearch.WordTrace tailWord_2479780 prefixEnd_2479780 848879371604275388697137 := by
  unfold tailWord_2479780
  simp only [CollatzResearch.WordTrace]
  refine ⟨45222503478094023775770397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60296671304125365034360529 45222503478094023775770397)
  ·
    refine ⟨16958438804285258915913899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45222503478094023775770397 16958438804285258915913899)
    ·
      refine ⟨25437658206427888373870849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16958438804285258915913899 25437658206427888373870849)
      ·
        refine ⟨19078243654820916280403137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25437658206427888373870849 19078243654820916280403137)
        ·
          refine ⟨14308682741115687210302353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19078243654820916280403137 14308682741115687210302353)
          ·
            refine ⟨10731512055836765407726765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14308682741115687210302353 10731512055836765407726765)
            ·
              refine ⟨4024317020938787027897537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10731512055836765407726765 4024317020938787027897537)
              ·
                refine ⟨3018237765704090270923153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4024317020938787027897537 3018237765704090270923153)
                ·
                  refine ⟨2263678324278067703192365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3018237765704090270923153 2263678324278067703192365)
                  ·
                    refine ⟨848879371604275388697137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2263678324278067703192365 848879371604275388697137)
                    ·
                      rfl

theorem cell22_2479780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 2, 2, 3].length) (baseStart_2479780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2479780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2479780 prefixEnd_2479780 := by exact prefixLift 2479780
  have htrace : WordTrace (prefixWord ++ tailWord_2479780) baseStart_2479780 baseEnd_2479780 := by
    simpa [prefixWord, tailWord_2479780, baseEnd_2479780] using wordTrace_append hprefix tailTrace_2479780
  have hstable : (prefixWord ++ tailWord_2479780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2479780).length < 2 ^ (prefixWord ++ tailWord_2479780).sum := by decide
  have hdescent : baseEnd_2479780 < baseStart_2479780 := by decide
  rcases family_descends (prefixWord ++ tailWord_2479780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2479797 : List Nat := [1, 3, 3, 3, 3, 1, 1, 1, 1, 5]
def baseStart_2479797 : Nat := 118140960795 + 2479797 * 2 ^ 59
def prefixEnd_2479797 : Nat := 4983230072969 + 3 ^ 40 * 2479797 * 2
def baseEnd_2479797 : Nat := 848885191051693011022085

theorem tailTrace_2479797 : CollatzResearch.WordTrace tailWord_2479797 prefixEnd_2479797 848885191051693011022085 := by
  unfold tailWord_2479797
  simp only [CollatzResearch.WordTrace]
  refine ⟨90445626997126459454909645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60297084664750972969939763 90445626997126459454909645)
  ·
    refine ⟨33917110123922422295591117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90445626997126459454909645 33917110123922422295591117)
    ·
      refine ⟨12718916296470908360846669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33917110123922422295591117 12718916296470908360846669)
      ·
        refine ⟨4769593611176590635317501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12718916296470908360846669 4769593611176590635317501)
        ·
          refine ⟨1788597604191221488244063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4769593611176590635317501 1788597604191221488244063)
          ·
            refine ⟨2682896406286832232366095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1788597604191221488244063 2682896406286832232366095)
            ·
              refine ⟨4024344609430248348549143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2682896406286832232366095 4024344609430248348549143)
              ·
                refine ⟨6036516914145372522823715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4024344609430248348549143 6036516914145372522823715)
                ·
                  refine ⟨9054775371218058784235573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6036516914145372522823715 9054775371218058784235573)
                  ·
                    refine ⟨848885191051693011022085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9054775371218058784235573 848885191051693011022085)
                    ·
                      rfl

theorem cell22_2479797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 1, 1, 5].length) (baseStart_2479797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2479797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2479797 prefixEnd_2479797 := by exact prefixLift 2479797
  have htrace : WordTrace (prefixWord ++ tailWord_2479797) baseStart_2479797 baseEnd_2479797 := by
    simpa [prefixWord, tailWord_2479797, baseEnd_2479797] using wordTrace_append hprefix tailTrace_2479797
  have hstable : (prefixWord ++ tailWord_2479797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2479797).length < 2 ^ (prefixWord ++ tailWord_2479797).sum := by decide
  have hdescent : baseEnd_2479797 < baseStart_2479797 := by decide
  rcases family_descends (prefixWord ++ tailWord_2479797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2479808 : List Nat := [2, 1, 1, 2, 4, 1, 1, 4, 3, 3]
def baseStart_2479808 : Nat := 118140960795 + 2479808 * 2 ^ 59
def prefixEnd_2479808 : Nat := 4983230072969 + 3 ^ 40 * 2479808 * 2
def baseEnd_2479808 : Nat := 848888956576492648997051

theorem tailTrace_2479808 : CollatzResearch.WordTrace tailWord_2479808 prefixEnd_2479808 848888956576492648997051 := by
  unfold tailWord_2479808
  simp only [CollatzResearch.WordTrace]
  refine ⟨45223014100043304166780039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60297352133391072222373385 45223014100043304166780039)
  ·
    refine ⟨67834521150064956250170059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45223014100043304166780039 67834521150064956250170059)
    ·
      refine ⟨101751781725097434375255089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67834521150064956250170059 101751781725097434375255089)
      ·
        refine ⟨76313836293823075781441317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101751781725097434375255089 76313836293823075781441317)
        ·
          refine ⟨14308844305091826709020247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76313836293823075781441317 14308844305091826709020247)
          ·
            refine ⟨21463266457637740063530371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14308844305091826709020247 21463266457637740063530371)
            ·
              refine ⟨32194899686456610095295557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21463266457637740063530371 32194899686456610095295557)
              ·
                refine ⟨6036543691210614392867917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32194899686456610095295557 6036543691210614392867917)
                ·
                  refine ⟨2263703884203980397325469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6036543691210614392867917 2263703884203980397325469)
                  ·
                    refine ⟨848888956576492648997051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2263703884203980397325469 848888956576492648997051)
                    ·
                      rfl

theorem cell22_2479808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 4, 3, 3].length) (baseStart_2479808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2479808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2479808 prefixEnd_2479808 := by exact prefixLift 2479808
  have htrace : WordTrace (prefixWord ++ tailWord_2479808) baseStart_2479808 baseEnd_2479808 := by
    simpa [prefixWord, tailWord_2479808, baseEnd_2479808] using wordTrace_append hprefix tailTrace_2479808
  have hstable : (prefixWord ++ tailWord_2479808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2479808).length < 2 ^ (prefixWord ++ tailWord_2479808).sum := by decide
  have hdescent : baseEnd_2479808 < baseStart_2479808 := by decide
  rcases family_descends (prefixWord ++ tailWord_2479808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2479866 : List Nat := [3, 1, 1, 1, 1, 3, 1, 3, 8]
def baseStart_2479866 : Nat := 118140960795 + 2479866 * 2 ^ 59
def prefixEnd_2479866 : Nat := 4983230072969 + 3 ^ 40 * 2479866 * 2
def baseEnd_2479866 : Nat := 282969603720599943682291

theorem tailTrace_2479866 : CollatzResearch.WordTrace tailWord_2479866 prefixEnd_2479866 282969603720599943682291 := by
  unfold tailWord_2479866
  simp only [CollatzResearch.WordTrace]
  refine ⟨22612035908469121059792863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60298762422584322826114301 22612035908469121059792863)
  ·
    refine ⟨33918053862703681589689295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22612035908469121059792863 33918053862703681589689295)
    ·
      refine ⟨50877080794055522384533943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33918053862703681589689295 50877080794055522384533943)
      ·
        refine ⟨76315621191083283576800915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50877080794055522384533943 76315621191083283576800915)
        ·
          refine ⟨114473431786624925365201373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76315621191083283576800915 114473431786624925365201373)
          ·
            refine ⟨42927536919984347011950515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 114473431786624925365201373 42927536919984347011950515)
            ·
              refine ⟨64391305379976520517925773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42927536919984347011950515 64391305379976520517925773)
              ·
                refine ⟨24146739517491195194222165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64391305379976520517925773 24146739517491195194222165)
                ·
                  refine ⟨282969603720599943682291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24146739517491195194222165 282969603720599943682291)
                  ·
                    rfl

theorem cell22_2479866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 3, 8].length) (baseStart_2479866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2479866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2479866 prefixEnd_2479866 := by exact prefixLift 2479866
  have htrace : WordTrace (prefixWord ++ tailWord_2479866) baseStart_2479866 baseEnd_2479866 := by
    simpa [prefixWord, tailWord_2479866, baseEnd_2479866] using wordTrace_append hprefix tailTrace_2479866
  have hstable : (prefixWord ++ tailWord_2479866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2479866).length < 2 ^ (prefixWord ++ tailWord_2479866).sum := by decide
  have hdescent : baseEnd_2479866 < baseStart_2479866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2479866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2479868 : List Nat := [2, 2, 2, 1, 3, 1, 3, 1, 3, 4]
def baseStart_2479868 : Nat := 118140960795 + 2479868 * 2 ^ 59
def prefixEnd_2479868 : Nat := 4983230072969 + 3 ^ 40 * 2479868 * 2
def baseEnd_2479868 : Nat := 848909495802672492496867

theorem tailTrace_2479868 : CollatzResearch.WordTrace tailWord_2479868 prefixEnd_2479868 848909495802672492496867 := by
  unfold tailWord_2479868
  simp only [CollatzResearch.WordTrace]
  refine ⟨45224108289934619290372129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60298811053246159053829505 45224108289934619290372129)
  ·
    refine ⟨33918081217450964467779097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45224108289934619290372129 33918081217450964467779097)
    ·
      refine ⟨25438560913088223350834323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33918081217450964467779097 25438560913088223350834323)
      ·
        refine ⟨38157841369632335026251485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25438560913088223350834323 38157841369632335026251485)
        ·
          refine ⟨14309190513612125634844307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38157841369632335026251485 14309190513612125634844307)
          ·
            refine ⟨21463785770418188452266461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14309190513612125634844307 21463785770418188452266461)
            ·
              refine ⟨8048919663906820669599923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21463785770418188452266461 8048919663906820669599923)
              ·
                refine ⟨12073379495860231004399885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8048919663906820669599923 12073379495860231004399885)
                ·
                  refine ⟨4527517310947586626649957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12073379495860231004399885 4527517310947586626649957)
                  ·
                    refine ⟨848909495802672492496867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4527517310947586626649957 848909495802672492496867)
                    ·
                      rfl

theorem cell22_2479868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 1, 3, 4].length) (baseStart_2479868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2479868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2479868 prefixEnd_2479868 := by exact prefixLift 2479868
  have htrace : WordTrace (prefixWord ++ tailWord_2479868) baseStart_2479868 baseEnd_2479868 := by
    simpa [prefixWord, tailWord_2479868, baseEnd_2479868] using wordTrace_append hprefix tailTrace_2479868
  have hstable : (prefixWord ++ tailWord_2479868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2479868).length < 2 ^ (prefixWord ++ tailWord_2479868).sum := by decide
  have hdescent : baseEnd_2479868 < baseStart_2479868 := by decide
  rcases family_descends (prefixWord ++ tailWord_2479868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2479900 : List Nat := [2, 2, 3, 1, 1, 2, 3, 4, 4]
def baseStart_2479900 : Nat := 118140960795 + 2479900 * 2 ^ 59
def prefixEnd_2479900 : Nat := 4983230072969 + 3 ^ 40 * 2479900 * 2
def baseEnd_2479900 : Nat := 282973483352211691898923

theorem tailTrace_2479900 : CollatzResearch.WordTrace tailWord_2479900 prefixEnd_2479900 282973483352211691898923 := by
  unfold tailWord_2479900
  simp only [CollatzResearch.WordTrace]
  refine ⟨45224691857876654022954577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60299589143835538697272769 45224691857876654022954577)
  ·
    refine ⟨33918518893407490517215933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45224691857876654022954577 33918518893407490517215933)
    ·
      refine ⟨12719444585027808943955975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33918518893407490517215933 12719444585027808943955975)
      ·
        refine ⟨19079166877541713415933963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12719444585027808943955975 19079166877541713415933963)
        ·
          refine ⟨28618750316312570123900945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19079166877541713415933963 28618750316312570123900945)
          ·
            refine ⟨21464062737234427592925709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28618750316312570123900945 21464062737234427592925709)
            ·
              refine ⟨8049023526462910347347141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21464062737234427592925709 8049023526462910347347141)
              ·
                refine ⟨1509191911211795690127589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8049023526462910347347141 1509191911211795690127589)
                ·
                  refine ⟨282973483352211691898923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1509191911211795690127589 282973483352211691898923)
                  ·
                    rfl

theorem cell22_2479900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 4, 4].length) (baseStart_2479900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2479900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2479900 prefixEnd_2479900 := by exact prefixLift 2479900
  have htrace : WordTrace (prefixWord ++ tailWord_2479900) baseStart_2479900 baseEnd_2479900 := by
    simpa [prefixWord, tailWord_2479900, baseEnd_2479900] using wordTrace_append hprefix tailTrace_2479900
  have hstable : (prefixWord ++ tailWord_2479900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2479900).length < 2 ^ (prefixWord ++ tailWord_2479900).sum := by decide
  have hdescent : baseEnd_2479900 < baseStart_2479900 := by decide
  rcases family_descends (prefixWord ++ tailWord_2479900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2479930 : List Nat := [3, 1, 1, 1, 5, 1, 3, 1, 2, 4]
def baseStart_2479930 : Nat := 118140960795 + 2479930 * 2 ^ 59
def prefixEnd_2479930 : Nat := 4983230072969 + 3 ^ 40 * 2479930 * 2
def baseEnd_2479930 : Nat := 848930719669724997446677

theorem tailTrace_2479930 : CollatzResearch.WordTrace tailWord_2479930 prefixEnd_2479930 848930719669724997446677 := by
  unfold tailWord_2479930
  simp only [CollatzResearch.WordTrace]
  refine ⟨22612619476411155792375311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60300318603763082113000829 22612619476411155792375311)
  ·
    refine ⟨33918929214616733688562967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22612619476411155792375311 33918929214616733688562967)
    ·
      refine ⟨50878393821925100532844451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33918929214616733688562967 50878393821925100532844451)
      ·
        refine ⟨76317590732887650799266677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50878393821925100532844451 76317590732887650799266677)
        ·
          refine ⟨7154774131208217262431251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 76317590732887650799266677 7154774131208217262431251)
          ·
            refine ⟨10732161196812325893646877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7154774131208217262431251 10732161196812325893646877)
            ·
              refine ⟨4024560448804622210117579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10732161196812325893646877 4024560448804622210117579)
              ·
                refine ⟨6036840673206933315176369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4024560448804622210117579 6036840673206933315176369)
                ·
                  refine ⟨4527630504905199986382277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6036840673206933315176369 4527630504905199986382277)
                  ·
                    refine ⟨848930719669724997446677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4527630504905199986382277 848930719669724997446677)
                    ·
                      rfl

theorem cell22_2479930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 1, 2, 4].length) (baseStart_2479930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2479930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2479930 prefixEnd_2479930 := by exact prefixLift 2479930
  have htrace : WordTrace (prefixWord ++ tailWord_2479930) baseStart_2479930 baseEnd_2479930 := by
    simpa [prefixWord, tailWord_2479930, baseEnd_2479930] using wordTrace_append hprefix tailTrace_2479930
  have hstable : (prefixWord ++ tailWord_2479930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2479930).length < 2 ^ (prefixWord ++ tailWord_2479930).sum := by decide
  have hdescent : baseEnd_2479930 < baseStart_2479930 := by decide
  rcases family_descends (prefixWord ++ tailWord_2479930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2479949 : List Nat := [1, 6, 1, 2, 1, 1, 3, 2, 2, 3]
def baseStart_2479949 : Nat := 118140960795 + 2479949 * 2 ^ 59
def prefixEnd_2479949 : Nat := 4983230072969 + 3 ^ 40 * 2479949 * 2
def baseEnd_2479949 : Nat := 848937223758015281221619

theorem tailTrace_2479949 : CollatzResearch.WordTrace tailWord_2479949 prefixEnd_2479949 848937223758015281221619 := by
  unfold tailWord_2479949
  simp only [CollatzResearch.WordTrace]
  refine ⟨90451170892575789414442901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60300780595050526276295267 90451170892575789414442901)
  ·
    refine ⟨4239898635589490128802011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 90451170892575789414442901 4239898635589490128802011)
    ·
      refine ⟨6359847953384235193203017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4239898635589490128802011 6359847953384235193203017)
      ·
        refine ⟨4769885965038176394902263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6359847953384235193203017 4769885965038176394902263)
        ·
          refine ⟨7154828947557264592353395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4769885965038176394902263 7154828947557264592353395)
          ·
            refine ⟨10732243421335896888530093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7154828947557264592353395 10732243421335896888530093)
            ·
              refine ⟨4024591283000961333198785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10732243421335896888530093 4024591283000961333198785)
              ·
                refine ⟨3018443462250720999899089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4024591283000961333198785 3018443462250720999899089)
                ·
                  refine ⟨2263832596688040749924317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3018443462250720999899089 2263832596688040749924317)
                  ·
                    refine ⟨848937223758015281221619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2263832596688040749924317 848937223758015281221619)
                    ·
                      rfl

theorem cell22_2479949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 2, 2, 3].length) (baseStart_2479949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2479949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2479949 prefixEnd_2479949 := by exact prefixLift 2479949
  have htrace : WordTrace (prefixWord ++ tailWord_2479949) baseStart_2479949 baseEnd_2479949 := by
    simpa [prefixWord, tailWord_2479949, baseEnd_2479949] using wordTrace_append hprefix tailTrace_2479949
  have hstable : (prefixWord ++ tailWord_2479949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2479949).length < 2 ^ (prefixWord ++ tailWord_2479949).sum := by decide
  have hdescent : baseEnd_2479949 < baseStart_2479949 := by decide
  rcases family_descends (prefixWord ++ tailWord_2479949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2480050 : List Nat := [3, 2, 1, 1, 1, 1, 1, 3, 6, 3]
def baseStart_2480050 : Nat := 118140960795 + 2480050 * 2 ^ 59
def prefixEnd_2480050 : Nat := 4983230072969 + 3 ^ 40 * 2480050 * 2
def baseEnd_2480050 : Nat := 848971798122084684446309

theorem tailTrace_2480050 : CollatzResearch.WordTrace tailWord_2480050 prefixEnd_2480050 848971798122084684446309 := by
  unfold tailWord_2480050
  simp only [CollatzResearch.WordTrace]
  refine ⟨22613713666302470915967401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60303236443473255775913069 22613713666302470915967401)
  ·
    refine ⟨16960285249726853186975551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22613713666302470915967401 16960285249726853186975551)
    ·
      refine ⟨25440427874590279780463327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16960285249726853186975551 25440427874590279780463327)
      ·
        refine ⟨38160641811885419670694991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25440427874590279780463327 38160641811885419670694991)
        ·
          refine ⟨57240962717828129506042487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38160641811885419670694991 57240962717828129506042487)
          ·
            refine ⟨85861444076742194259063731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57240962717828129506042487 85861444076742194259063731)
            ·
              refine ⟨128792166115113291388595597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85861444076742194259063731 128792166115113291388595597)
              ·
                refine ⟨48297062293167484270723349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 128792166115113291388595597 48297062293167484270723349)
                ·
                  refine ⟨2263924794992225825190157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 48297062293167484270723349 2263924794992225825190157)
                  ·
                    refine ⟨848971798122084684446309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2263924794992225825190157 848971798122084684446309)
                    ·
                      rfl

theorem cell22_2480050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 6, 3].length) (baseStart_2480050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2480050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2480050 prefixEnd_2480050 := by exact prefixLift 2480050
  have htrace : WordTrace (prefixWord ++ tailWord_2480050) baseStart_2480050 baseEnd_2480050 := by
    simpa [prefixWord, tailWord_2480050, baseEnd_2480050] using wordTrace_append hprefix tailTrace_2480050
  have hstable : (prefixWord ++ tailWord_2480050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2480050).length < 2 ^ (prefixWord ++ tailWord_2480050).sum := by decide
  have hdescent : baseEnd_2480050 < baseStart_2480050 := by decide
  rcases family_descends (prefixWord ++ tailWord_2480050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2480118 : List Nat := [5, 1, 1, 1, 5, 1, 1, 2, 2, 3]
def baseStart_2480118 : Nat := 118140960795 + 2480118 * 2 ^ 59
def prefixEnd_2480118 : Nat := 4983230072969 + 3 ^ 40 * 2480118 * 2
def baseEnd_2480118 : Nat := 848995075911755173746101

theorem tailTrace_2480118 : CollatzResearch.WordTrace tailWord_2480118 prefixEnd_2480118 848995075911755173746101 := by
  unfold tailWord_2480118
  simp only [CollatzResearch.WordTrace]
  refine ⟨5653583426810220704834063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 60304889885975687518230005 5653583426810220704834063)
  ·
    refine ⟨8480375140215331057251095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5653583426810220704834063 8480375140215331057251095)
    ·
      refine ⟨12720562710322996585876643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8480375140215331057251095 12720562710322996585876643)
      ·
        refine ⟨19080844065484494878814965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12720562710322996585876643 19080844065484494878814965)
        ·
          refine ⟨1788829131139171394888903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19080844065484494878814965 1788829131139171394888903)
          ·
            refine ⟨2683243696708757092333355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1788829131139171394888903 2683243696708757092333355)
            ·
              refine ⟨4024865545063135638500033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2683243696708757092333355 4024865545063135638500033)
              ·
                refine ⟨3018649158797351728875025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4024865545063135638500033 3018649158797351728875025)
                ·
                  refine ⟨2263986869098013796656269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3018649158797351728875025 2263986869098013796656269)
                  ·
                    refine ⟨848995075911755173746101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2263986869098013796656269 848995075911755173746101)
                    ·
                      rfl

theorem cell22_2480118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 2, 2, 3].length) (baseStart_2480118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2480118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2480118 prefixEnd_2480118 := by exact prefixLift 2480118
  have htrace : WordTrace (prefixWord ++ tailWord_2480118) baseStart_2480118 baseEnd_2480118 := by
    simpa [prefixWord, tailWord_2480118, baseEnd_2480118] using wordTrace_append hprefix tailTrace_2480118
  have hstable : (prefixWord ++ tailWord_2480118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2480118).length < 2 ^ (prefixWord ++ tailWord_2480118).sum := by decide
  have hdescent : baseEnd_2480118 < baseStart_2480118 := by decide
  rcases family_descends (prefixWord ++ tailWord_2480118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2480129 : List Nat := [1, 2, 4, 1, 2, 1, 1, 6, 1, 3]
def baseStart_2480129 : Nat := 118140960795 + 2480129 * 2 ^ 59
def prefixEnd_2480129 : Nat := 4983230072969 + 3 ^ 40 * 2480129 * 2
def baseEnd_2480129 : Nat := 848998841436554811721067

theorem tailTrace_2480129 : CollatzResearch.WordTrace tailWord_2480129 prefixEnd_2480129 848998841436554811721067 := by
  unfold tailWord_2480129
  simp only [CollatzResearch.WordTrace]
  refine ⟨90457736031923680155995441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60305157354615786770663627 90457736031923680155995441)
  ·
    refine ⟨67843302023942760116996581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90457736031923680155995441 67843302023942760116996581)
    ·
      refine ⟨12720619129489267521936859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67843302023942760116996581 12720619129489267521936859)
      ·
        refine ⟨19080928694233901282905289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12720619129489267521936859 19080928694233901282905289)
        ·
          refine ⟨14310696520675425962178967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19080928694233901282905289 14310696520675425962178967)
          ·
            refine ⟨21466044781013138943268451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14310696520675425962178967 21466044781013138943268451)
            ·
              refine ⟨32199067171519708414902677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21466044781013138943268451 32199067171519708414902677)
              ·
                refine ⟨1509331273664986331948563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 32199067171519708414902677 1509331273664986331948563)
                ·
                  refine ⟨2263996910497479497922845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1509331273664986331948563 2263996910497479497922845)
                  ·
                    refine ⟨848998841436554811721067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2263996910497479497922845 848998841436554811721067)
                    ·
                      rfl

theorem cell22_2480129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 6, 1, 3].length) (baseStart_2480129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2480129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2480129 prefixEnd_2480129 := by exact prefixLift 2480129
  have htrace : WordTrace (prefixWord ++ tailWord_2480129) baseStart_2480129 baseEnd_2480129 := by
    simpa [prefixWord, tailWord_2480129, baseEnd_2480129] using wordTrace_append hprefix tailTrace_2480129
  have hstable : (prefixWord ++ tailWord_2480129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2480129).length < 2 ^ (prefixWord ++ tailWord_2480129).sum := by decide
  have hdescent : baseEnd_2480129 < baseStart_2480129 := by decide
  rcases family_descends (prefixWord ++ tailWord_2480129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2480140 : List Nat := [2, 2, 1, 2, 3, 1, 1, 3, 2, 5]
def baseStart_2480140 : Nat := 118140960795 + 2480140 * 2 ^ 59
def prefixEnd_2480140 : Nat := 4983230072969 + 3 ^ 40 * 2480140 * 2
def baseEnd_2480140 : Nat := 849002606961354449696033

theorem tailTrace_2480140 : CollatzResearch.WordTrace tailWord_2480140 prefixEnd_2480140 849002606961354449696033 := by
  unfold tailWord_2480140
  simp only [CollatzResearch.WordTrace]
  refine ⟨45229068617441914517322937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60305424823255886023097249 45229068617441914517322937)
  ·
    refine ⟨33921801463081435887992203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45229068617441914517322937 33921801463081435887992203)
    ·
      refine ⟨50882702194622153831988305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33921801463081435887992203 50882702194622153831988305)
      ·
        refine ⟨38162026645966615373991229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50882702194622153831988305 38162026645966615373991229)
        ·
          refine ⟨14310759992237480765246711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38162026645966615373991229 14310759992237480765246711)
          ·
            refine ⟨21466139988356221147870067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14310759992237480765246711 21466139988356221147870067)
            ·
              refine ⟨32199209982534331721805101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21466139988356221147870067 32199209982534331721805101)
              ·
                refine ⟨12074703743450374395676913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32199209982534331721805101 12074703743450374395676913)
                ·
                  refine ⟨9056027807587780796757685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12074703743450374395676913 9056027807587780796757685)
                  ·
                    refine ⟨849002606961354449696033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9056027807587780796757685 849002606961354449696033)
                    ·
                      rfl

theorem cell22_2480140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 3, 2, 5].length) (baseStart_2480140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2480140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2480140 prefixEnd_2480140 := by exact prefixLift 2480140
  have htrace : WordTrace (prefixWord ++ tailWord_2480140) baseStart_2480140 baseEnd_2480140 := by
    simpa [prefixWord, tailWord_2480140, baseEnd_2480140] using wordTrace_append hprefix tailTrace_2480140
  have hstable : (prefixWord ++ tailWord_2480140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2480140).length < 2 ^ (prefixWord ++ tailWord_2480140).sum := by decide
  have hdescent : baseEnd_2480140 < baseStart_2480140 := by decide
  rcases family_descends (prefixWord ++ tailWord_2480140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2480148 : List Nat := [2, 4, 3, 2, 2, 1, 2, 6]
def baseStart_2480148 : Nat := 118140960795 + 2480148 * 2 ^ 59
def prefixEnd_2480148 : Nat := 4983230072969 + 3 ^ 40 * 2480148 * 2
def baseEnd_2480148 : Nat := 94333927280538343944001

theorem tailTrace_2480148 : CollatzResearch.WordTrace tailWord_2480148 prefixEnd_2480148 94333927280538343944001 := by
  unfold tailWord_2480148
  simp only [CollatzResearch.WordTrace]
  refine ⟨45229214509427423200468549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60305619345903230933958065 45229214509427423200468549)
  ·
    refine ⟨8480477720517641850087853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45229214509427423200468549 8480477720517641850087853)
    ·
      refine ⟨3180179145194115693782945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8480477720517641850087853 3180179145194115693782945)
      ·
        refine ⟨2385134358895586770337209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3180179145194115693782945 2385134358895586770337209)
        ·
          refine ⟨1788850769171690077752907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2385134358895586770337209 1788850769171690077752907)
          ·
            refine ⟨2683276153757535116629361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1788850769171690077752907 2683276153757535116629361)
            ·
              refine ⟨2012457115318151337472021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2683276153757535116629361 2012457115318151337472021)
              ·
                refine ⟨94333927280538343944001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2012457115318151337472021 94333927280538343944001)
                ·
                  rfl

theorem cell22_2480148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 2, 6].length) (baseStart_2480148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2480148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2480148 prefixEnd_2480148 := by exact prefixLift 2480148
  have htrace : WordTrace (prefixWord ++ tailWord_2480148) baseStart_2480148 baseEnd_2480148 := by
    simpa [prefixWord, tailWord_2480148, baseEnd_2480148] using wordTrace_append hprefix tailTrace_2480148
  have hstable : (prefixWord ++ tailWord_2480148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2480148).length < 2 ^ (prefixWord ++ tailWord_2480148).sum := by decide
  have hdescent : baseEnd_2480148 < baseStart_2480148 := by decide
  rcases family_descends (prefixWord ++ tailWord_2480148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2480180 : List Nat := [2, 5, 1, 2, 2, 1, 3, 2, 1, 3]
def baseStart_2480180 : Nat := 118140960795 + 2480180 * 2 ^ 59
def prefixEnd_2480180 : Nat := 4983230072969 + 3 ^ 40 * 2480180 * 2
def baseEnd_2480180 : Nat := 849016299778807678695911

theorem tailTrace_2480180 : CollatzResearch.WordTrace tailWord_2480180 prefixEnd_2480180 849016299778807678695911 := by
  unfold tailWord_2480180
  simp only [CollatzResearch.WordTrace]
  refine ⟨45229798077369457933050997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60306397436492610577401329 45229798077369457933050997)
  ·
    refine ⟨4240293569753386681223531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 45229798077369457933050997 4240293569753386681223531)
    ·
      refine ⟨6360440354630080021835297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4240293569753386681223531 6360440354630080021835297)
      ·
        refine ⟨4770330265972560016376473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6360440354630080021835297 4770330265972560016376473)
        ·
          refine ⟨3577747699479420012282355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4770330265972560016376473 3577747699479420012282355)
          ·
            refine ⟨5366621549219130018423533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3577747699479420012282355 5366621549219130018423533)
            ·
              refine ⟨2012483080957173756908825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5366621549219130018423533 2012483080957173756908825)
              ·
                refine ⟨1509362310717880317681619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2012483080957173756908825 1509362310717880317681619)
                ·
                  refine ⟨2264043466076820476522429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1509362310717880317681619 2264043466076820476522429)
                  ·
                    refine ⟨849016299778807678695911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2264043466076820476522429 849016299778807678695911)
                    ·
                      rfl

theorem cell22_2480180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 3, 2, 1, 3].length) (baseStart_2480180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2480180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2480180 prefixEnd_2480180 := by exact prefixLift 2480180
  have htrace : WordTrace (prefixWord ++ tailWord_2480180) baseStart_2480180 baseEnd_2480180 := by
    simpa [prefixWord, tailWord_2480180, baseEnd_2480180] using wordTrace_append hprefix tailTrace_2480180
  have hstable : (prefixWord ++ tailWord_2480180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2480180).length < 2 ^ (prefixWord ++ tailWord_2480180).sum := by decide
  have hdescent : baseEnd_2480180 < baseStart_2480180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2480180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2480200 : List Nat := [2, 1, 3, 1, 1, 1, 2, 4, 1, 6]
def baseStart_2480200 : Nat := 118140960795 + 2480200 * 2 ^ 59
def prefixEnd_2480200 : Nat := 4983230072969 + 3 ^ 40 * 2480200 * 2
def baseEnd_2480200 : Nat := 849023146187534293195849

theorem tailTrace_2480200 : CollatzResearch.WordTrace tailWord_2480200 prefixEnd_2480200 849023146187534293195849 := by
  unfold tailWord_2480200
  simp only [CollatzResearch.WordTrace]
  refine ⟨45230162807333229640915027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60306883743110972854553369 45230162807333229640915027)
  ·
    refine ⟨67845244210999844461372541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45230162807333229640915027 67845244210999844461372541)
    ·
      refine ⟨25441966579124941673014703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67845244210999844461372541 25441966579124941673014703)
      ·
        refine ⟨38162949868687412509522055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25441966579124941673014703 38162949868687412509522055)
        ·
          refine ⟨57244424803031118764283083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38162949868687412509522055 57244424803031118764283083)
          ·
            refine ⟨85866637204546678146424625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57244424803031118764283083 85866637204546678146424625)
            ·
              refine ⟨64399977903410008609818469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85866637204546678146424625 64399977903410008609818469)
              ·
                refine ⟨12074995856889376614340963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64399977903410008609818469 12074995856889376614340963)
                ·
                  refine ⟨18112493785334064921511445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12074995856889376614340963 18112493785334064921511445)
                  ·
                    refine ⟨849023146187534293195849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18112493785334064921511445 849023146187534293195849)
                    ·
                      rfl

theorem cell22_2480200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 4, 1, 6].length) (baseStart_2480200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2480200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2480200 prefixEnd_2480200 := by exact prefixLift 2480200
  have htrace : WordTrace (prefixWord ++ tailWord_2480200) baseStart_2480200 baseEnd_2480200 := by
    simpa [prefixWord, tailWord_2480200, baseEnd_2480200] using wordTrace_append hprefix tailTrace_2480200
  have hstable : (prefixWord ++ tailWord_2480200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2480200).length < 2 ^ (prefixWord ++ tailWord_2480200).sum := by decide
  have hdescent : baseEnd_2480200 < baseStart_2480200 := by decide
  rcases family_descends (prefixWord ++ tailWord_2480200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2480215 : List Nat := [1, 1, 3, 2, 2, 1, 4, 8]
def baseStart_2480215 : Nat := 118140960795 + 2480215 * 2 ^ 59
def prefixEnd_2480215 : Nat := 4983230072969 + 3 ^ 40 * 2480215 * 2
def baseEnd_2480215 : Nat := 94336475666008806007867

theorem tailTrace_2480215 : CollatzResearch.WordTrace tailWord_2480215 prefixEnd_2480215 94336475666008806007867 := by
  unfold tailWord_2480215
  simp only [CollatzResearch.WordTrace]
  refine ⟨90460872709612116843626099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60307248473074744562417399 90460872709612116843626099)
  ·
    refine ⟨135691309064418175265439149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90460872709612116843626099 135691309064418175265439149)
    ·
      refine ⟨50884240899156815724539681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135691309064418175265439149 50884240899156815724539681)
      ·
        refine ⟨38163180674367611793404761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50884240899156815724539681 38163180674367611793404761)
        ·
          refine ⟨28622385505775708845053571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38163180674367611793404761 28622385505775708845053571)
          ·
            refine ⟨42933578258663563267580357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28622385505775708845053571 42933578258663563267580357)
            ·
              refine ⟨8050045923499418112671317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42933578258663563267580357 8050045923499418112671317)
              ·
                refine ⟨94336475666008806007867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8050045923499418112671317 94336475666008806007867)
                ·
                  rfl

theorem cell22_2480215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 8].length) (baseStart_2480215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2480215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2480215 prefixEnd_2480215 := by exact prefixLift 2480215
  have htrace : WordTrace (prefixWord ++ tailWord_2480215) baseStart_2480215 baseEnd_2480215 := by
    simpa [prefixWord, tailWord_2480215, baseEnd_2480215] using wordTrace_append hprefix tailTrace_2480215
  have hstable : (prefixWord ++ tailWord_2480215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2480215).length < 2 ^ (prefixWord ++ tailWord_2480215).sum := by decide
  have hdescent : baseEnd_2480215 < baseStart_2480215 := by decide
  rcases family_descends (prefixWord ++ tailWord_2480215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2480217 : List Nat := [1, 2, 1, 2, 2, 1, 6, 1, 2, 4]
def baseStart_2480217 : Nat := 118140960795 + 2480217 * 2 ^ 59
def prefixEnd_2480217 : Nat := 4983230072969 + 3 ^ 40 * 2480217 * 2
def baseEnd_2480217 : Nat := 849028965634951915520797

theorem tailTrace_2480217 : CollatzResearch.WordTrace tailWord_2480217 prefixEnd_2480217 849028965634951915520797 := by
  unfold tailWord_2480217
  simp only [CollatzResearch.WordTrace]
  refine ⟨90460945655604871185198905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60307297103736580790132603 90460945655604871185198905)
  ·
    refine ⟨67845709241703653388899179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90460945655604871185198905 67845709241703653388899179)
    ·
      refine ⟨101768563862555480083348769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67845709241703653388899179 101768563862555480083348769)
      ·
        refine ⟨76326422896916610062511577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101768563862555480083348769 76326422896916610062511577)
        ·
          refine ⟨57244817172687457546883683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76326422896916610062511577 57244817172687457546883683)
          ·
            refine ⟨85867225759031186320325525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57244817172687457546883683 85867225759031186320325525)
            ·
              refine ⟨4025026207454586858765259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 85867225759031186320325525 4025026207454586858765259)
              ·
                refine ⟨6037539311181880288147889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4025026207454586858765259 6037539311181880288147889)
                ·
                  refine ⟨4528154483386410216110917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6037539311181880288147889 4528154483386410216110917)
                  ·
                    refine ⟨849028965634951915520797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4528154483386410216110917 849028965634951915520797)
                    ·
                      rfl

theorem cell22_2480217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 1, 2, 4].length) (baseStart_2480217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2480217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2480217 prefixEnd_2480217 := by exact prefixLift 2480217
  have htrace : WordTrace (prefixWord ++ tailWord_2480217) baseStart_2480217 baseEnd_2480217 := by
    simpa [prefixWord, tailWord_2480217, baseEnd_2480217] using wordTrace_append hprefix tailTrace_2480217
  have hstable : (prefixWord ++ tailWord_2480217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2480217).length < 2 ^ (prefixWord ++ tailWord_2480217).sum := by decide
  have hdescent : baseEnd_2480217 < baseStart_2480217 := by decide
  rcases family_descends (prefixWord ++ tailWord_2480217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2480264 : List Nat := [2, 1, 3, 4, 1, 1, 1, 1, 5, 3]
def baseStart_2480264 : Nat := 118140960795 + 2480264 * 2 ^ 59
def prefixEnd_2480264 : Nat := 4983230072969 + 3 ^ 40 * 2480264 * 2
def baseEnd_2480264 : Nat := 849045054695459459595653

theorem tailTrace_2480264 : CollatzResearch.WordTrace tailWord_2480264 prefixEnd_2480264 849045054695459459595653 := by
  unfold tailWord_2480264
  simp only [CollatzResearch.WordTrace]
  refine ⟨45231329943217299106079923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60308439924289732141439897 45231329943217299106079923)
  ·
    refine ⟨67846994914825948659119885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45231329943217299106079923 67846994914825948659119885)
    ·
      refine ⟨25442623093059730747169957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67846994914825948659119885 25442623093059730747169957)
      ·
        refine ⟨4770491829948699515094367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25442623093059730747169957 4770491829948699515094367)
        ·
          refine ⟨7155737744923049272641551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4770491829948699515094367 7155737744923049272641551)
          ·
            refine ⟨10733606617384573908962327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7155737744923049272641551 10733606617384573908962327)
            ·
              refine ⟨16100409926076860863443491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10733606617384573908962327 16100409926076860863443491)
              ·
                refine ⟨24150614889115291295165237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16100409926076860863443491 24150614889115291295165237)
                ·
                  refine ⟨2264120145854558558921741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24150614889115291295165237 2264120145854558558921741)
                  ·
                    refine ⟨849045054695459459595653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2264120145854558558921741 849045054695459459595653)
                    ·
                      rfl

theorem cell22_2480264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 1, 5, 3].length) (baseStart_2480264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2480264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2480264 prefixEnd_2480264 := by exact prefixLift 2480264
  have htrace : WordTrace (prefixWord ++ tailWord_2480264) baseStart_2480264 baseEnd_2480264 := by
    simpa [prefixWord, tailWord_2480264, baseEnd_2480264] using wordTrace_append hprefix tailTrace_2480264
  have hstable : (prefixWord ++ tailWord_2480264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2480264).length < 2 ^ (prefixWord ++ tailWord_2480264).sum := by decide
  have hdescent : baseEnd_2480264 < baseStart_2480264 := by decide
  rcases family_descends (prefixWord ++ tailWord_2480264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2480275 : List Nat := [1, 1, 1, 2, 1, 2, 3, 1, 3, 7]
def baseStart_2480275 : Nat := 118140960795 + 2480275 * 2 ^ 59
def prefixEnd_2480275 : Nat := 4983230072969 + 3 ^ 40 * 2480275 * 2
def baseEnd_2480275 : Nat := 849048820220259097570619

theorem tailTrace_2480275 : CollatzResearch.WordTrace tailWord_2480275 prefixEnd_2480275 849048820220259097570619 := by
  unfold tailWord_2480275
  simp only [CollatzResearch.WordTrace]
  refine ⟨90463061089394747090810279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60308707392929831393873519 90463061089394747090810279)
  ·
    refine ⟨135694591634092120636215419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90463061089394747090810279 135694591634092120636215419)
    ·
      refine ⟨203541887451138180954323129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135694591634092120636215419 203541887451138180954323129)
      ·
        refine ⟨152656415588353635715742347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 203541887451138180954323129 152656415588353635715742347)
        ·
          refine ⟨228984623382530453573613521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152656415588353635715742347 228984623382530453573613521)
          ·
            refine ⟨171738467536897840180210141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 228984623382530453573613521 171738467536897840180210141)
            ·
              refine ⟨64401925326336690067578803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 171738467536897840180210141 64401925326336690067578803)
              ·
                refine ⟨96602887989505035101368205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64401925326336690067578803 96602887989505035101368205)
                ·
                  refine ⟨36226082996064388163013077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 96602887989505035101368205 36226082996064388163013077)
                  ·
                    refine ⟨849048820220259097570619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36226082996064388163013077 849048820220259097570619)
                    ·
                      rfl

theorem cell22_2480275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 3, 7].length) (baseStart_2480275 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2480275 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2480275 prefixEnd_2480275 := by exact prefixLift 2480275
  have htrace : WordTrace (prefixWord ++ tailWord_2480275) baseStart_2480275 baseEnd_2480275 := by
    simpa [prefixWord, tailWord_2480275, baseEnd_2480275] using wordTrace_append hprefix tailTrace_2480275
  have hstable : (prefixWord ++ tailWord_2480275).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2480275).length < 2 ^ (prefixWord ++ tailWord_2480275).sum := by decide
  have hdescent : baseEnd_2480275 < baseStart_2480275 := by decide
  rcases family_descends (prefixWord ++ tailWord_2480275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2480298 : List Nat := [3, 1, 5, 1, 2, 1, 2, 1, 3, 3]
def baseStart_2480298 : Nat := 118140960795 + 2480298 * 2 ^ 59
def prefixEnd_2480298 : Nat := 4983230072969 + 3 ^ 40 * 2480298 * 2
def baseEnd_2480298 : Nat := 849056693590294704245549

theorem tailTrace_2480298 : CollatzResearch.WordTrace tailWord_2480298 prefixEnd_2480298 849056693590294704245549 := by
  unfold tailWord_2480298
  simp only [CollatzResearch.WordTrace]
  refine ⟨22615974992077855504724387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60309266645540948012598365 22615974992077855504724387)
  ·
    refine ⟨33923962488116783257086581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22615974992077855504724387 33923962488116783257086581)
    ·
      refine ⟨3180371483260948430351867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33923962488116783257086581 3180371483260948430351867)
      ·
        refine ⟨4770557224891422645527801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3180371483260948430351867 4770557224891422645527801)
        ·
          refine ⟨3577917918668566984145851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4770557224891422645527801 3577917918668566984145851)
          ·
            refine ⟨5366876878002850476218777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3577917918668566984145851 5366876878002850476218777)
            ·
              refine ⟨4025157658502137857164083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5366876878002850476218777 4025157658502137857164083)
              ·
                refine ⟨6037736487753206785746125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4025157658502137857164083 6037736487753206785746125)
                ·
                  refine ⟨2264151182907452544654797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6037736487753206785746125 2264151182907452544654797)
                  ·
                    refine ⟨849056693590294704245549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2264151182907452544654797 849056693590294704245549)
                    ·
                      rfl

theorem cell22_2480298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_2480298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2480298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2480298 prefixEnd_2480298 := by exact prefixLift 2480298
  have htrace : WordTrace (prefixWord ++ tailWord_2480298) baseStart_2480298 baseEnd_2480298 := by
    simpa [prefixWord, tailWord_2480298, baseEnd_2480298] using wordTrace_append hprefix tailTrace_2480298
  have hstable : (prefixWord ++ tailWord_2480298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2480298).length < 2 ^ (prefixWord ++ tailWord_2480298).sum := by decide
  have hdescent : baseEnd_2480298 < baseStart_2480298 := by decide
  rcases family_descends (prefixWord ++ tailWord_2480298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2480332 : List Nat := [2, 2, 1, 6, 2, 1, 1, 3, 1, 3]
def baseStart_2480332 : Nat := 118140960795 + 2480332 * 2 ^ 59
def prefixEnd_2480332 : Nat := 4983230072969 + 3 ^ 40 * 2480332 * 2
def baseEnd_2480332 : Nat := 849068332485129948895445

theorem tailTrace_2480332 : CollatzResearch.WordTrace tailWord_2480332 prefixEnd_2480332 849068332485129948895445 := by
  unfold tailWord_2480332
  simp only [CollatzResearch.WordTrace]
  refine ⟨45232570025094122912817625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60310093366792163883756833 45232570025094122912817625)
  ·
    refine ⟨33924427518820592184613219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45232570025094122912817625 33924427518820592184613219)
    ·
      refine ⟨50886641278230888276919829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33924427518820592184613219 50886641278230888276919829)
      ·
        refine ⟨2385311309917072887980617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 50886641278230888276919829 2385311309917072887980617)
        ·
          refine ⟨1788983482437804665985463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2385311309917072887980617 1788983482437804665985463)
          ·
            refine ⟨2683475223656706998978195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1788983482437804665985463 2683475223656706998978195)
            ·
              refine ⟨4025212835485060498467293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2683475223656706998978195 4025212835485060498467293)
              ·
                refine ⟨1509454813306897686925235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4025212835485060498467293 1509454813306897686925235)
                ·
                  refine ⟨2264182219960346530387853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1509454813306897686925235 2264182219960346530387853)
                  ·
                    refine ⟨849068332485129948895445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2264182219960346530387853 849068332485129948895445)
                    ·
                      rfl

theorem cell22_2480332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 3, 1, 3].length) (baseStart_2480332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2480332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2480332 prefixEnd_2480332 := by exact prefixLift 2480332
  have htrace : WordTrace (prefixWord ++ tailWord_2480332) baseStart_2480332 baseEnd_2480332 := by
    simpa [prefixWord, tailWord_2480332, baseEnd_2480332] using wordTrace_append hprefix tailTrace_2480332
  have hstable : (prefixWord ++ tailWord_2480332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2480332).length < 2 ^ (prefixWord ++ tailWord_2480332).sum := by decide
  have hdescent : baseEnd_2480332 < baseStart_2480332 := by decide
  rcases family_descends (prefixWord ++ tailWord_2480332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2480337 : List Nat := [1, 2, 2, 1, 2, 2, 2, 4, 1, 5]
def baseStart_2480337 : Nat := 118140960795 + 2480337 * 2 ^ 59
def prefixEnd_2480337 : Nat := 4983230072969 + 3 ^ 40 * 2480337 * 2
def baseEnd_2480337 : Nat := 849070044087311602520429

theorem tailTrace_2480337 : CollatzResearch.WordTrace tailWord_2480337 prefixEnd_2480337 849070044087311602520429 := by
  unfold tailWord_2480337
  simp only [CollatzResearch.WordTrace]
  refine ⟨90465322415170131679567265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60310214943446754453044843 90465322415170131679567265)
  ·
    refine ⟨67848991811377598759675449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90465322415170131679567265 67848991811377598759675449)
    ·
      refine ⟨50886743858533199069756587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67848991811377598759675449 50886743858533199069756587)
      ·
        refine ⟨76330115787799798604634881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50886743858533199069756587 76330115787799798604634881)
        ·
          refine ⟨57247586840849848953476161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76330115787799798604634881 57247586840849848953476161)
          ·
            refine ⟨42935690130637386715107121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57247586840849848953476161 42935690130637386715107121)
            ·
              refine ⟨32201767597978040036330341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42935690130637386715107121 32201767597978040036330341)
              ·
                refine ⟨6037831424620882506811939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32201767597978040036330341 6037831424620882506811939)
                ·
                  refine ⟨9056747136931323760217909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6037831424620882506811939 9056747136931323760217909)
                  ·
                    refine ⟨849070044087311602520429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9056747136931323760217909 849070044087311602520429)
                    ·
                      rfl

theorem cell22_2480337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 4, 1, 5].length) (baseStart_2480337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2480337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2480337 prefixEnd_2480337 := by exact prefixLift 2480337
  have htrace : WordTrace (prefixWord ++ tailWord_2480337) baseStart_2480337 baseEnd_2480337 := by
    simpa [prefixWord, tailWord_2480337, baseEnd_2480337] using wordTrace_append hprefix tailTrace_2480337
  have hstable : (prefixWord ++ tailWord_2480337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2480337).length < 2 ^ (prefixWord ++ tailWord_2480337).sum := by decide
  have hdescent : baseEnd_2480337 < baseStart_2480337 := by decide
  rcases family_descends (prefixWord ++ tailWord_2480337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2480367 : List Nat := [1, 1, 2, 1, 6, 1, 1, 9]
def baseStart_2480367 : Nat := 118140960795 + 2480367 * 2 ^ 59
def prefixEnd_2480367 : Nat := 4983230072969 + 3 ^ 40 * 2480367 * 2
def baseEnd_2480367 : Nat := 94342257077822391585593

theorem tailTrace_2480367 : CollatzResearch.WordTrace tailWord_2480367 prefixEnd_2480367 94342257077822391585593 := by
  unfold tailWord_2480367
  simp only [CollatzResearch.WordTrace]
  refine ⟨90466416605061446803159355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60310944403374297868772903 90466416605061446803159355)
  ·
    refine ⟨135699624907592170204739033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90466416605061446803159355 135699624907592170204739033)
    ·
      refine ⟨101774718680694127653554275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135699624907592170204739033 101774718680694127653554275)
      ·
        refine ⟨152662078021041191480331413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101774718680694127653554275 152662078021041191480331413)
        ·
          refine ⟨7156034907236305850640535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 152662078021041191480331413 7156034907236305850640535)
          ·
            refine ⟨10734052360854458775960803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7156034907236305850640535 10734052360854458775960803)
            ·
              refine ⟨16101078541281688163941205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10734052360854458775960803 16101078541281688163941205)
              ·
                refine ⟨94342257077822391585593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16101078541281688163941205 94342257077822391585593)
                ·
                  rfl

theorem cell22_2480367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 9].length) (baseStart_2480367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2480367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2480367 prefixEnd_2480367 := by exact prefixLift 2480367
  have htrace : WordTrace (prefixWord ++ tailWord_2480367) baseStart_2480367 baseEnd_2480367 := by
    simpa [prefixWord, tailWord_2480367, baseEnd_2480367] using wordTrace_append hprefix tailTrace_2480367
  have hstable : (prefixWord ++ tailWord_2480367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2480367).length < 2 ^ (prefixWord ++ tailWord_2480367).sum := by decide
  have hdescent : baseEnd_2480367 < baseStart_2480367 := by decide
  rcases family_descends (prefixWord ++ tailWord_2480367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2480386 : List Nat := [3, 4, 1, 1, 2, 1, 1, 3, 2, 4]
def baseStart_2480386 : Nat := 118140960795 + 2480386 * 2 ^ 59
def prefixEnd_2480386 : Nat := 4983230072969 + 3 ^ 40 * 2480386 * 2
def baseEnd_2480386 : Nat := 849086817788691808045279

theorem tailTrace_2480386 : CollatzResearch.WordTrace tailWord_2480386 prefixEnd_2480386 849086817788691808045279 := by
  unfold tailWord_2480386
  simp only [CollatzResearch.WordTrace]
  refine ⟨22616777397998153262025253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60311406394661742032067341 22616777397998153262025253)
  ·
    refine ⟨4240645762124653736629735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22616777397998153262025253 4240645762124653736629735)
    ·
      refine ⟨6360968643186980604944603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4240645762124653736629735 6360968643186980604944603)
      ·
        refine ⟨9541452964780470907416905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6360968643186980604944603 9541452964780470907416905)
        ·
          refine ⟨7156089723585353180562679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9541452964780470907416905 7156089723585353180562679)
          ·
            refine ⟨10734134585378029770844019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7156089723585353180562679 10734134585378029770844019)
            ·
              refine ⟨16101201878067044656266029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10734134585378029770844019 16101201878067044656266029)
              ·
                refine ⟨6037950704275141746099761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16101201878067044656266029 6037950704275141746099761)
                ·
                  refine ⟨4528463028206356309574821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6037950704275141746099761 4528463028206356309574821)
                  ·
                    refine ⟨849086817788691808045279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4528463028206356309574821 849086817788691808045279)
                    ·
                      rfl

theorem cell22_2480386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_2480386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2480386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2480386 prefixEnd_2480386 := by exact prefixLift 2480386
  have htrace : WordTrace (prefixWord ++ tailWord_2480386) baseStart_2480386 baseEnd_2480386 := by
    simpa [prefixWord, tailWord_2480386, baseEnd_2480386] using wordTrace_append hprefix tailTrace_2480386
  have hstable : (prefixWord ++ tailWord_2480386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2480386).length < 2 ^ (prefixWord ++ tailWord_2480386).sum := by decide
  have hdescent : baseEnd_2480386 < baseStart_2480386 := by decide
  rcases family_descends (prefixWord ++ tailWord_2480386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2480457 : List Nat := [1, 2, 1, 1, 2, 3, 1, 1, 10]
def baseStart_2480457 : Nat := 118140960795 + 2480457 * 2 ^ 59
def prefixEnd_2480457 : Nat := 4983230072969 + 3 ^ 40 * 2480457 * 2
def baseEnd_2480457 : Nat := 283037040846557096506687

theorem tailTrace_2480457 : CollatzResearch.WordTrace tailWord_2480457 prefixEnd_2480457 283037040846557096506687 := by
  unfold tailWord_2480457
  simp only [CollatzResearch.WordTrace]
  refine ⟨90469699174735392173935625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60313132783156928115957083 90469699174735392173935625)
  ·
    refine ⟨67852274381051544130451719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90469699174735392173935625 67852274381051544130451719)
    ·
      refine ⟨101778411571577316195677579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67852274381051544130451719 101778411571577316195677579)
      ·
        refine ⟨152667617357365974293516369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101778411571577316195677579 152667617357365974293516369)
        ·
          refine ⟨114500713018024480720137277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152667617357365974293516369 114500713018024480720137277)
          ·
            refine ⟨42937767381759180270051479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 114500713018024480720137277 42937767381759180270051479)
            ·
              refine ⟨64406651072638770405077219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42937767381759180270051479 64406651072638770405077219)
              ·
                refine ⟨96609976608958155607615829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64406651072638770405077219 96609976608958155607615829)
                ·
                  refine ⟨283037040846557096506687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 96609976608958155607615829 283037040846557096506687)
                  ·
                    rfl

theorem cell22_2480457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 10].length) (baseStart_2480457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2480457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2480457 prefixEnd_2480457 := by exact prefixLift 2480457
  have htrace : WordTrace (prefixWord ++ tailWord_2480457) baseStart_2480457 baseEnd_2480457 := by
    simpa [prefixWord, tailWord_2480457, baseEnd_2480457] using wordTrace_append hprefix tailTrace_2480457
  have hstable : (prefixWord ++ tailWord_2480457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2480457).length < 2 ^ (prefixWord ++ tailWord_2480457).sum := by decide
  have hdescent : baseEnd_2480457 < baseStart_2480457 := by decide
  rcases family_descends (prefixWord ++ tailWord_2480457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2480521 : List Nat := [1, 2, 1, 1, 6, 2, 1, 2, 2, 4]
def baseStart_2480521 : Nat := 118140960795 + 2480521 * 2 ^ 59
def prefixEnd_2480521 : Nat := 4983230072969 + 3 ^ 40 * 2480521 * 2
def baseEnd_2480521 : Nat := 849133031047596455919865

theorem tailTrace_2480521 : CollatzResearch.WordTrace tailWord_2480521 prefixEnd_2480521 849133031047596455919865 := by
  unfold tailWord_2480521
  simp only [CollatzResearch.WordTrace]
  refine ⟨90472033446503531104265417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60314688964335687402843611 90472033446503531104265417)
  ·
    refine ⟨67854025084877648328199063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90472033446503531104265417 67854025084877648328199063)
    ·
      refine ⟨101781037627316472492298595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67854025084877648328199063 101781037627316472492298595)
      ·
        refine ⟨152671556440974708738447893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101781037627316472492298595 152671556440974708738447893)
        ·
          refine ⟨7156479208170689472114745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 152671556440974708738447893 7156479208170689472114745)
          ·
            refine ⟨5367359406128017104086059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7156479208170689472114745 5367359406128017104086059)
            ·
              refine ⟨8051039109192025656129089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5367359406128017104086059 8051039109192025656129089)
              ·
                refine ⟨6038279331894019242096817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8051039109192025656129089 6038279331894019242096817)
                ·
                  refine ⟨4528709498920514431572613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6038279331894019242096817 4528709498920514431572613)
                  ·
                    refine ⟨849133031047596455919865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4528709498920514431572613 849133031047596455919865)
                    ·
                      rfl

theorem cell22_2480521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 2, 2, 4].length) (baseStart_2480521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2480521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2480521 prefixEnd_2480521 := by exact prefixLift 2480521
  have htrace : WordTrace (prefixWord ++ tailWord_2480521) baseStart_2480521 baseEnd_2480521 := by
    simpa [prefixWord, tailWord_2480521, baseEnd_2480521] using wordTrace_append hprefix tailTrace_2480521
  have hstable : (prefixWord ++ tailWord_2480521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2480521).length < 2 ^ (prefixWord ++ tailWord_2480521).sum := by decide
  have hdescent : baseEnd_2480521 < baseStart_2480521 := by decide
  rcases family_descends (prefixWord ++ tailWord_2480521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2480536 : List Nat := [2, 1, 2, 5, 1, 2, 2, 7]
def baseStart_2480536 : Nat := 118140960795 + 2480536 * 2 ^ 59
def prefixEnd_2480536 : Nat := 4983230072969 + 3 ^ 40 * 2480536 * 2
def baseEnd_2480536 : Nat := 94348685094904601866091

theorem tailTrace_2480536 : CollatzResearch.WordTrace tailWord_2480536 prefixEnd_2480536 94348685094904601866091 := by
  unfold tailWord_2480536
  simp only [CollatzResearch.WordTrace]
  refine ⟨45236290270724594333030731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60315053694299459110707641 45236290270724594333030731)
  ·
    refine ⟨67854435406086891499546097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45236290270724594333030731 67854435406086891499546097)
    ·
      refine ⟨50890826554565168624659573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67854435406086891499546097 50890826554565168624659573)
      ·
        refine ⟨4771014989490484558561835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 50890826554565168624659573 4771014989490484558561835)
        ·
          refine ⟨7156522484235726837842753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4771014989490484558561835 7156522484235726837842753)
          ·
            refine ⟨5367391863176795128382065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7156522484235726837842753 5367391863176795128382065)
            ·
              refine ⟨4025543897382596346286549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5367391863176795128382065 4025543897382596346286549)
              ·
                refine ⟨94348685094904601866091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4025543897382596346286549 94348685094904601866091)
                ·
                  rfl

theorem cell22_2480536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 7].length) (baseStart_2480536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2480536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2480536 prefixEnd_2480536 := by exact prefixLift 2480536
  have htrace : WordTrace (prefixWord ++ tailWord_2480536) baseStart_2480536 baseEnd_2480536 := by
    simpa [prefixWord, tailWord_2480536, baseEnd_2480536] using wordTrace_append hprefix tailTrace_2480536
  have hstable : (prefixWord ++ tailWord_2480536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2480536).length < 2 ^ (prefixWord ++ tailWord_2480536).sum := by decide
  have hdescent : baseEnd_2480536 < baseStart_2480536 := by decide
  rcases family_descends (prefixWord ++ tailWord_2480536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2480568 : List Nat := [2, 1, 2, 1, 2, 2, 1, 7, 1, 3]
def baseStart_2480568 : Nat := 118140960795 + 2480568 * 2 ^ 59
def prefixEnd_2480568 : Nat := 4983230072969 + 3 ^ 40 * 2480568 * 2
def baseEnd_2480568 : Nat := 849149120108103999994721

theorem tailTrace_2480568 : CollatzResearch.WordTrace tailWord_2480568 prefixEnd_2480568 849149120108103999994721 := by
  unfold tailWord_2480568
  simp only [CollatzResearch.WordTrace]
  refine ⟨45236873838666629065613179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60315831784888838754150905 45236873838666629065613179)
  ·
    refine ⟨67855310757999943598419769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45236873838666629065613179 67855310757999943598419769)
    ·
      refine ⟨50891483068499957698814827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67855310757999943598419769 50891483068499957698814827)
      ·
        refine ⟨76337224602749936548222241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50891483068499957698814827 76337224602749936548222241)
        ·
          refine ⟨57252918452062452411166681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76337224602749936548222241 57252918452062452411166681)
          ·
            refine ⟨42939688839046839308375011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57252918452062452411166681 42939688839046839308375011)
            ·
              refine ⟨64409533258570258962562517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42939688839046839308375011 64409533258570258962562517)
              ·
                refine ⟨1509598435747740444435059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 64409533258570258962562517 1509598435747740444435059)
                ·
                  refine ⟨2264397653621610666652589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1509598435747740444435059 2264397653621610666652589)
                  ·
                    refine ⟨849149120108103999994721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2264397653621610666652589 849149120108103999994721)
                    ·
                      rfl

theorem cell22_2480568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 7, 1, 3].length) (baseStart_2480568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2480568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2480568 prefixEnd_2480568 := by exact prefixLift 2480568
  have htrace : WordTrace (prefixWord ++ tailWord_2480568) baseStart_2480568 baseEnd_2480568 := by
    simpa [prefixWord, tailWord_2480568, baseEnd_2480568] using wordTrace_append hprefix tailTrace_2480568
  have hstable : (prefixWord ++ tailWord_2480568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2480568).length < 2 ^ (prefixWord ++ tailWord_2480568).sum := by decide
  have hdescent : baseEnd_2480568 < baseStart_2480568 := by decide
  rcases family_descends (prefixWord ++ tailWord_2480568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2480579 : List Nat := [1, 1, 1, 3, 1, 1, 3, 4, 2, 5]
def baseStart_2480579 : Nat := 118140960795 + 2480579 * 2 ^ 59
def prefixEnd_2480579 : Nat := 4983230072969 + 3 ^ 40 * 2480579 * 2
def baseEnd_2480579 : Nat := 849152885632903637969687

theorem tailTrace_2480579 : CollatzResearch.WordTrace tailWord_2480579 prefixEnd_2480579 849152885632903637969687 := by
  unfold tailWord_2480579
  simp only [CollatzResearch.WordTrace]
  refine ⟨90474148880293407009876791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60316099253528938006584527 90474148880293407009876791)
  ·
    refine ⟨135711223320440110514815187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90474148880293407009876791 135711223320440110514815187)
    ·
      refine ⟨203566834980660165772222781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135711223320440110514815187 203566834980660165772222781)
      ·
        refine ⟨76337563117747562164583543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 203566834980660165772222781 76337563117747562164583543)
        ·
          refine ⟨114506344676621343246875315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76337563117747562164583543 114506344676621343246875315)
          ·
            refine ⟨171759517014932014870312973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114506344676621343246875315 171759517014932014870312973)
            ·
              refine ⟨64409818880599505576367365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 171759517014932014870312973 64409818880599505576367365)
              ·
                refine ⟨12076841040112407295568881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64409818880599505576367365 12076841040112407295568881)
                ·
                  refine ⟨9057630780084305471676661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12076841040112407295568881 9057630780084305471676661)
                  ·
                    refine ⟨849152885632903637969687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9057630780084305471676661 849152885632903637969687)
                    ·
                      rfl

theorem cell22_2480579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 4, 2, 5].length) (baseStart_2480579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2480579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2480579 prefixEnd_2480579 := by exact prefixLift 2480579
  have htrace : WordTrace (prefixWord ++ tailWord_2480579) baseStart_2480579 baseEnd_2480579 := by
    simpa [prefixWord, tailWord_2480579, baseEnd_2480579] using wordTrace_append hprefix tailTrace_2480579
  have hstable : (prefixWord ++ tailWord_2480579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2480579).length < 2 ^ (prefixWord ++ tailWord_2480579).sum := by decide
  have hdescent : baseEnd_2480579 < baseStart_2480579 := by decide
  rcases family_descends (prefixWord ++ tailWord_2480579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2480585 : List Nat := [1, 2, 1, 1, 2, 1, 8, 2, 1, 3]
def baseStart_2480585 : Nat := 118140960795 + 2480585 * 2 ^ 59
def prefixEnd_2480585 : Nat := 4983230072969 + 3 ^ 40 * 2480585 * 2
def baseEnd_2480585 : Nat := 849154939555521622319669

theorem tailTrace_2480585 : CollatzResearch.WordTrace tailWord_2480585 prefixEnd_2480585 849154939555521622319669 := by
  unfold tailWord_2480585
  simp only [CollatzResearch.WordTrace]
  refine ⟨90474367718271670034595209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60316245145514446689730139 90474367718271670034595209)
  ·
    refine ⟨67855775788703752525946407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90474367718271670034595209 67855775788703752525946407)
    ·
      refine ⟨101783663683055628788919611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67855775788703752525946407 101783663683055628788919611)
      ·
        refine ⟨152675495524583443183379417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101783663683055628788919611 152675495524583443183379417)
        ·
          refine ⟨114506621643437582387534563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152675495524583443183379417 114506621643437582387534563)
          ·
            refine ⟨171759932465156373581301845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114506621643437582387534563 171759932465156373581301845)
            ·
              refine ⟨2012811708576051252905881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 171759932465156373581301845 2012811708576051252905881)
              ·
                refine ⟨1509608781432038439679411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2012811708576051252905881 1509608781432038439679411)
                ·
                  refine ⟨2264413172148057659519117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1509608781432038439679411 2264413172148057659519117)
                  ·
                    refine ⟨849154939555521622319669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2264413172148057659519117 849154939555521622319669)
                    ·
                      rfl

theorem cell22_2480585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 8, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 8, 2, 1, 3].length) (baseStart_2480585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2480585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2480585 prefixEnd_2480585 := by exact prefixLift 2480585
  have htrace : WordTrace (prefixWord ++ tailWord_2480585) baseStart_2480585 baseEnd_2480585 := by
    simpa [prefixWord, tailWord_2480585, baseEnd_2480585] using wordTrace_append hprefix tailTrace_2480585
  have hstable : (prefixWord ++ tailWord_2480585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2480585).length < 2 ^ (prefixWord ++ tailWord_2480585).sum := by decide
  have hdescent : baseEnd_2480585 < baseStart_2480585 := by decide
  rcases family_descends (prefixWord ++ tailWord_2480585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2480596 : List Nat := [2, 4, 1, 2, 2, 1, 1, 1, 1, 7]
def baseStart_2480596 : Nat := 118140960795 + 2480596 * 2 ^ 59
def prefixEnd_2480596 : Nat := 4983230072969 + 3 ^ 40 * 2480596 * 2
def baseEnd_2480596 : Nat := 849158705080321260294635

theorem tailTrace_2480596 : CollatzResearch.WordTrace tailWord_2480596 prefixEnd_2480596 849158705080321260294635 := by
  unfold tailWord_2480596
  simp only [CollatzResearch.WordTrace]
  refine ⟨45237384460615909456622821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60316512614154545942163761 45237384460615909456622821)
  ·
    refine ⟨8482009586365483023116779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45237384460615909456622821 8482009586365483023116779)
    ·
      refine ⟨12723014379548224534675169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8482009586365483023116779 12723014379548224534675169)
      ·
        refine ⟨9542260784661168401006377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12723014379548224534675169 9542260784661168401006377)
        ·
          refine ⟨7156695588495876300754783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9542260784661168401006377 7156695588495876300754783)
          ·
            refine ⟨10735043382743814451132175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7156695588495876300754783 10735043382743814451132175)
            ·
              refine ⟨16102565074115721676698263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10735043382743814451132175 16102565074115721676698263)
              ·
                refine ⟨24153847611173582515047395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16102565074115721676698263 24153847611173582515047395)
                ·
                  refine ⟨36230771416760373772571093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24153847611173582515047395 36230771416760373772571093)
                  ·
                    refine ⟨849158705080321260294635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36230771416760373772571093 849158705080321260294635)
                    ·
                      rfl

theorem cell22_2480596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 1, 1, 7].length) (baseStart_2480596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2480596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2480596 prefixEnd_2480596 := by exact prefixLift 2480596
  have htrace : WordTrace (prefixWord ++ tailWord_2480596) baseStart_2480596 baseEnd_2480596 := by
    simpa [prefixWord, tailWord_2480596, baseEnd_2480596] using wordTrace_append hprefix tailTrace_2480596
  have hstable : (prefixWord ++ tailWord_2480596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2480596).length < 2 ^ (prefixWord ++ tailWord_2480596).sum := by decide
  have hdescent : baseEnd_2480596 < baseStart_2480596 := by decide
  rcases family_descends (prefixWord ++ tailWord_2480596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2480598 : List Nat := [5, 2, 1, 1, 1, 1, 1, 5, 5]
def baseStart_2480598 : Nat := 118140960795 + 2480598 * 2 ^ 59
def prefixEnd_2480598 : Nat := 4983230072969 + 3 ^ 40 * 2480598 * 2
def baseEnd_2480598 : Nat := 283053129907064640581543

theorem tailTrace_2480598 : CollatzResearch.WordTrace tailWord_2480598 prefixEnd_2480598 283053129907064640581543 := by
  unfold tailWord_2480598
  simp only [CollatzResearch.WordTrace]
  refine ⟨5654677616701535828426153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 60316561244816382169878965 5654677616701535828426153)
  ·
    refine ⟨4241008212526151871319615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5654677616701535828426153 4241008212526151871319615)
    ·
      refine ⟨6361512318789227806979423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4241008212526151871319615 6361512318789227806979423)
      ·
        refine ⟨9542268478183841710469135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6361512318789227806979423 9542268478183841710469135)
        ·
          refine ⟨14313402717275762565703703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9542268478183841710469135 14313402717275762565703703)
          ·
            refine ⟨21470104075913643848555555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14313402717275762565703703 21470104075913643848555555)
            ·
              refine ⟨32205156113870465772833333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21470104075913643848555555 32205156113870465772833333)
              ·
                refine ⟨3019233385675356166203125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32205156113870465772833333 3019233385675356166203125)
                ·
                  refine ⟨283053129907064640581543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3019233385675356166203125 283053129907064640581543)
                  ·
                    rfl

theorem cell22_2480598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_2480598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2480598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2480598 prefixEnd_2480598 := by exact prefixLift 2480598
  have htrace : WordTrace (prefixWord ++ tailWord_2480598) baseStart_2480598 baseEnd_2480598 := by
    simpa [prefixWord, tailWord_2480598, baseEnd_2480598] using wordTrace_append hprefix tailTrace_2480598
  have hstable : (prefixWord ++ tailWord_2480598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2480598).length < 2 ^ (prefixWord ++ tailWord_2480598).sum := by decide
  have hdescent : baseEnd_2480598 < baseStart_2480598 := by decide
  rcases family_descends (prefixWord ++ tailWord_2480598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2480750 : List Nat := [4, 1, 2, 2, 2, 2, 2, 2, 5]
def baseStart_2480750 : Nat := 118140960795 + 2480750 * 2 ^ 59
def prefixEnd_2480750 : Nat := 4983230072969 + 3 ^ 40 * 2480750 * 2
def baseEnd_2480750 : Nat := 283070474142505397314721

theorem tailTrace_2480750 : CollatzResearch.WordTrace tailWord_2480750 prefixEnd_2480750 283070474142505397314721 := by
  unfold tailWord_2480750
  simp only [CollatzResearch.WordTrace]
  refine ⟨11310048220334237901793963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60320257175115935476234469 11310048220334237901793963)
  ·
    refine ⟨16965072330501356852690945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11310048220334237901793963 16965072330501356852690945)
    ·
      refine ⟨12723804247876017639518209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16965072330501356852690945 12723804247876017639518209)
      ·
        refine ⟨9542853185907013229638657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12723804247876017639518209 9542853185907013229638657)
        ·
          refine ⟨7157139889430259922228993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9542853185907013229638657 7157139889430259922228993)
          ·
            refine ⟨5367854917072694941671745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7157139889430259922228993 5367854917072694941671745)
            ·
              refine ⟨4025891187804521206253809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5367854917072694941671745 4025891187804521206253809)
              ·
                refine ⟨3019418390853390904690357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4025891187804521206253809 3019418390853390904690357)
                ·
                  refine ⟨283070474142505397314721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3019418390853390904690357 283070474142505397314721)
                  ·
                    rfl

theorem cell22_2480750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 2, 5].length) (baseStart_2480750 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2480750 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2480750 prefixEnd_2480750 := by exact prefixLift 2480750
  have htrace : WordTrace (prefixWord ++ tailWord_2480750) baseStart_2480750 baseEnd_2480750 := by
    simpa [prefixWord, tailWord_2480750, baseEnd_2480750] using wordTrace_append hprefix tailTrace_2480750
  have hstable : (prefixWord ++ tailWord_2480750).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2480750).length < 2 ^ (prefixWord ++ tailWord_2480750).sum := by decide
  have hdescent : baseEnd_2480750 < baseStart_2480750 := by decide
  rcases family_descends (prefixWord ++ tailWord_2480750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2480793 : List Nat := [1, 2, 1, 2, 1, 2, 4, 2, 4, 3]
def baseStart_2480793 : Nat := 118140960795 + 2480793 * 2 ^ 59
def prefixEnd_2480793 : Nat := 4983230072969 + 3 ^ 40 * 2480793 * 2
def baseEnd_2480793 : Nat := 849226142206278413119031

theorem tailTrace_2480793 : CollatzResearch.WordTrace tailWord_2480793 prefixEnd_2480793 849226142206278413119031 := by
  unfold tailWord_2480793
  simp only [CollatzResearch.WordTrace]
  refine ⟨90481954101518121558167033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60321302734345414372111355 90481954101518121558167033)
  ·
    refine ⟨67861465576138591168625275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90481954101518121558167033 67861465576138591168625275)
    ·
      refine ⟨101792198364207886752937913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67861465576138591168625275 101792198364207886752937913)
      ·
        refine ⟨76344148773155915064703435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101792198364207886752937913 76344148773155915064703435)
        ·
          refine ⟨114516223159733872597055153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76344148773155915064703435 114516223159733872597055153)
          ·
            refine ⟨85887167369800404447791365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114516223159733872597055153 85887167369800404447791365)
            ·
              refine ⟨16103843881837575833960881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 85887167369800404447791365 16103843881837575833960881)
              ·
                refine ⟨12077882911378181875470661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16103843881837575833960881 12077882911378181875470661)
                ·
                  refine ⟨2264603045883409101650749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12077882911378181875470661 2264603045883409101650749)
                  ·
                    refine ⟨849226142206278413119031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2264603045883409101650749 849226142206278413119031)
                    ·
                      rfl

theorem cell22_2480793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 2, 4, 3].length) (baseStart_2480793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2480793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2480793 prefixEnd_2480793 := by exact prefixLift 2480793
  have htrace : WordTrace (prefixWord ++ tailWord_2480793) baseStart_2480793 baseEnd_2480793 := by
    simpa [prefixWord, tailWord_2480793, baseEnd_2480793] using wordTrace_append hprefix tailTrace_2480793
  have hstable : (prefixWord ++ tailWord_2480793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2480793).length < 2 ^ (prefixWord ++ tailWord_2480793).sum := by decide
  have hdescent : baseEnd_2480793 < baseStart_2480793 := by decide
  rcases family_descends (prefixWord ++ tailWord_2480793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2480840 : List Nat := [2, 1, 3, 1, 2, 5, 2, 6]
def baseStart_2480840 : Nat := 118140960795 + 2480840 * 2 ^ 59
def prefixEnd_2480840 : Nat := 4983230072969 + 3 ^ 40 * 2480840 * 2
def baseEnd_2480840 : Nat := 94360247918531773021543

theorem tailTrace_2480840 : CollatzResearch.WordTrace tailWord_2480840 prefixEnd_2480840 94360247918531773021543 := by
  unfold tailWord_2480840
  simp only [CollatzResearch.WordTrace]
  refine ⟨45241834166173924292563987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60322445554898565723418649 45241834166173924292563987)
  ·
    refine ⟨67862751249260886438845981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45241834166173924292563987 67862751249260886438845981)
    ·
      refine ⟨25448531718472832414567243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67862751249260886438845981 25448531718472832414567243)
      ·
        refine ⟨38172797577709248621850865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25448531718472832414567243 38172797577709248621850865)
        ·
          refine ⟨28629598183281936466388149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38172797577709248621850865 28629598183281936466388149)
          ·
            refine ⟨2684024829682681543723889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28629598183281936466388149 2684024829682681543723889)
            ·
              refine ⟨2013018622262011157792917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2684024829682681543723889 2013018622262011157792917)
              ·
                refine ⟨94360247918531773021543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2013018622262011157792917 94360247918531773021543)
                ·
                  rfl

theorem cell22_2480840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 2, 6].length) (baseStart_2480840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2480840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2480840 prefixEnd_2480840 := by exact prefixLift 2480840
  have htrace : WordTrace (prefixWord ++ tailWord_2480840) baseStart_2480840 baseEnd_2480840 := by
    simpa [prefixWord, tailWord_2480840, baseEnd_2480840] using wordTrace_append hprefix tailTrace_2480840
  have hstable : (prefixWord ++ tailWord_2480840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2480840).length < 2 ^ (prefixWord ++ tailWord_2480840).sum := by decide
  have hdescent : baseEnd_2480840 < baseStart_2480840 := by decide
  rcases family_descends (prefixWord ++ tailWord_2480840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2480868 : List Nat := [2, 3, 1, 1, 1, 4, 2, 1, 7]
def baseStart_2480868 : Nat := 118140960795 + 2480868 * 2 ^ 59
def prefixEnd_2480868 : Nat := 4983230072969 + 3 ^ 40 * 2480868 * 2
def baseEnd_2480868 : Nat := 283083938746334405831267

theorem tailTrace_2480868 : CollatzResearch.WordTrace tailWord_2480868 prefixEnd_2480868 283083938746334405831267 := by
  unfold tailWord_2480868
  simp only [CollatzResearch.WordTrace]
  refine ⟨45242344788123204683573629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60323126384164272911431505 45242344788123204683573629)
  ·
    refine ⟨16965879295546201756340111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45242344788123204683573629 16965879295546201756340111)
    ·
      refine ⟨25448818943319302634510167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16965879295546201756340111 25448818943319302634510167)
      ·
        refine ⟨38173228414978953951765251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25448818943319302634510167 38173228414978953951765251)
        ·
          refine ⟨57259842622468430927647877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38173228414978953951765251 57259842622468430927647877)
          ·
            refine ⟨10736220491712830798933977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57259842622468430927647877 10736220491712830798933977)
            ·
              refine ⟨8052165368784623099200483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10736220491712830798933977 8052165368784623099200483)
              ·
                refine ⟨12078248053176934648800725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8052165368784623099200483 12078248053176934648800725)
                ·
                  refine ⟨283083938746334405831267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12078248053176934648800725 283083938746334405831267)
                  ·
                    rfl

theorem cell22_2480868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 1, 7].length) (baseStart_2480868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2480868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2480868 prefixEnd_2480868 := by exact prefixLift 2480868
  have htrace : WordTrace (prefixWord ++ tailWord_2480868) baseStart_2480868 baseEnd_2480868 := by
    simpa [prefixWord, tailWord_2480868, baseEnd_2480868] using wordTrace_append hprefix tailTrace_2480868
  have hstable : (prefixWord ++ tailWord_2480868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2480868).length < 2 ^ (prefixWord ++ tailWord_2480868).sum := by decide
  have hdescent : baseEnd_2480868 < baseStart_2480868 := by decide
  rcases family_descends (prefixWord ++ tailWord_2480868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2480945 : List Nat := [1, 2, 2, 3, 2, 1, 4, 1, 1, 5]
def baseStart_2480945 : Nat := 118140960795 + 2480945 * 2 ^ 59
def prefixEnd_2480945 : Nat := 4983230072969 + 3 ^ 40 * 2480945 * 2
def baseEnd_2480945 : Nat := 849278174912600683318565

theorem tailTrace_2480945 : CollatzResearch.WordTrace tailWord_2480945 prefixEnd_2480945 849278174912600683318565 := by
  unfold tailWord_2480945
  simp only [CollatzResearch.WordTrace]
  refine ⟨90487497996967451517700289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60324998664644967678466859 90487497996967451517700289)
  ·
    refine ⟨67865623497725588638275217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90487497996967451517700289 67865623497725588638275217)
    ·
      refine ⟨50899217623294191478706413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67865623497725588638275217 50899217623294191478706413)
      ·
        refine ⟨19087206608735321804514905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50899217623294191478706413 19087206608735321804514905)
        ·
          refine ⟨14315404956551491353386179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19087206608735321804514905 14315404956551491353386179)
          ·
            refine ⟨21473107434827237030079269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14315404956551491353386179 21473107434827237030079269)
            ·
              refine ⟨4026207644030106943139863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21473107434827237030079269 4026207644030106943139863)
              ·
                refine ⟨6039311466045160414709795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4026207644030106943139863 6039311466045160414709795)
                ·
                  refine ⟨9058967199067740622064693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6039311466045160414709795 9058967199067740622064693)
                  ·
                    refine ⟨849278174912600683318565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9058967199067740622064693 849278174912600683318565)
                    ·
                      rfl

theorem cell22_2480945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 1, 1, 5].length) (baseStart_2480945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2480945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2480945 prefixEnd_2480945 := by exact prefixLift 2480945
  have htrace : WordTrace (prefixWord ++ tailWord_2480945) baseStart_2480945 baseEnd_2480945 := by
    simpa [prefixWord, tailWord_2480945, baseEnd_2480945] using wordTrace_append hprefix tailTrace_2480945
  have hstable : (prefixWord ++ tailWord_2480945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2480945).length < 2 ^ (prefixWord ++ tailWord_2480945).sum := by decide
  have hdescent : baseEnd_2480945 < baseStart_2480945 := by decide
  rcases family_descends (prefixWord ++ tailWord_2480945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2480966 : List Nat := [6, 1, 1, 2, 2, 1, 1, 3, 1, 4]
def baseStart_2480966 : Nat := 118140960795 + 2480966 * 2 ^ 59
def prefixEnd_2480966 : Nat := 4983230072969 + 3 ^ 40 * 2480966 * 2
def baseEnd_2480966 : Nat := 849285363641763628543501

theorem tailTrace_2480966 : CollatzResearch.WordTrace tailWord_2480966 prefixEnd_2480966 849285363641763628543501 := by
  unfold tailWord_2480966
  simp only [CollatzResearch.WordTrace]
  refine ⟨2827758247809105378256711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 60325509286594248069476501 2827758247809105378256711)
  ·
    refine ⟨4241637371713658067385067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2827758247809105378256711 4241637371713658067385067)
    ·
      refine ⟨6362456057570487101077601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4241637371713658067385067 6362456057570487101077601)
      ·
        refine ⟨4771842043177865325808201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6362456057570487101077601 4771842043177865325808201)
        ·
          refine ⟨3578881532383398994356151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4771842043177865325808201 3578881532383398994356151)
          ·
            refine ⟨5368322298575098491534227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3578881532383398994356151 5368322298575098491534227)
            ·
              refine ⟨8052483447862647737301341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5368322298575098491534227 8052483447862647737301341)
              ·
                refine ⟨3019681292948492901488003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8052483447862647737301341 3019681292948492901488003)
                ·
                  refine ⟨4529521939422739352232005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3019681292948492901488003 4529521939422739352232005)
                  ·
                    refine ⟨849285363641763628543501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4529521939422739352232005 849285363641763628543501)
                    ·
                      rfl

theorem cell22_2480966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_2480966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2480966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2480966 prefixEnd_2480966 := by exact prefixLift 2480966
  have htrace : WordTrace (prefixWord ++ tailWord_2480966) baseStart_2480966 baseEnd_2480966 := by
    simpa [prefixWord, tailWord_2480966, baseEnd_2480966] using wordTrace_append hprefix tailTrace_2480966
  have hstable : (prefixWord ++ tailWord_2480966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2480966).length < 2 ^ (prefixWord ++ tailWord_2480966).sum := by decide
  have hdescent : baseEnd_2480966 < baseStart_2480966 := by decide
  rcases family_descends (prefixWord ++ tailWord_2480966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2481026 : List Nat := [3, 4, 2, 2, 2, 1, 8]
def baseStart_2481026 : Nat := 118140960795 + 2481026 * 2 ^ 59
def prefixEnd_2481026 : Nat := 4983230072969 + 3 ^ 40 * 2481026 * 2
def baseEnd_2481026 : Nat := 31455774180294202668271

theorem tailTrace_2481026 : CollatzResearch.WordTrace tailWord_2481026 prefixEnd_2481026 31455774180294202668271 := by
  unfold tailWord_2481026
  simp only [CollatzResearch.WordTrace]
  refine ⟨22622613077418500587849733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60326968206449334900932621 22622613077418500587849733)
  ·
    refine ⟨4241739952015968860221825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22622613077418500587849733 4241739952015968860221825)
    ·
      refine ⟨3181304964011976645166369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4241739952015968860221825 3181304964011976645166369)
      ·
        refine ⟨2385978723008982483874777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3181304964011976645166369 2385978723008982483874777)
        ·
          refine ⟨1789484042256736862906083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2385978723008982483874777 1789484042256736862906083)
          ·
            refine ⟨2684226063385105294359125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1789484042256736862906083 2684226063385105294359125)
            ·
              refine ⟨31455774180294202668271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2684226063385105294359125 31455774180294202668271)
              ·
                rfl

theorem cell22_2481026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 8].length) (baseStart_2481026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2481026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2481026 prefixEnd_2481026 := by exact prefixLift 2481026
  have htrace : WordTrace (prefixWord ++ tailWord_2481026) baseStart_2481026 baseEnd_2481026 := by
    simpa [prefixWord, tailWord_2481026, baseEnd_2481026] using wordTrace_append hprefix tailTrace_2481026
  have hstable : (prefixWord ++ tailWord_2481026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2481026).length < 2 ^ (prefixWord ++ tailWord_2481026).sum := by decide
  have hdescent : baseEnd_2481026 < baseStart_2481026 := by decide
  rcases family_descends (prefixWord ++ tailWord_2481026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2481080 : List Nat := [2, 1, 2, 1, 2, 4, 1, 1, 3, 5]
def baseStart_2481080 : Nat := 118140960795 + 2481080 * 2 ^ 59
def prefixEnd_2481080 : Nat := 4983230072969 + 3 ^ 40 * 2481080 * 2
def baseEnd_2481080 : Nat := 849324388171505331193151

theorem tailTrace_2481080 : CollatzResearch.WordTrace tailWord_2481080 prefixEnd_2481080 849324388171505331193151 := by
  unfold tailWord_2481080
  simp only [CollatzResearch.WordTrace]
  refine ⟨45246210925739184786932347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60328281234318913049243129 45246210925739184786932347)
  ·
    refine ⟨67869316388608777180398521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45246210925739184786932347 67869316388608777180398521)
    ·
      refine ⟨50901987291456582885298891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67869316388608777180398521 50901987291456582885298891)
      ·
        refine ⟨76352980937184874327948337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50901987291456582885298891 76352980937184874327948337)
        ·
          refine ⟨57264735702888655745961253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76352980937184874327948337 57264735702888655745961253)
          ·
            refine ⟨10737137944291622952367735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57264735702888655745961253 10737137944291622952367735)
            ·
              refine ⟨16105706916437434428551603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10737137944291622952367735 16105706916437434428551603)
              ·
                refine ⟨24158560374656151642827405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16105706916437434428551603 24158560374656151642827405)
                ·
                  refine ⟨9059460140496056866060277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24158560374656151642827405 9059460140496056866060277)
                  ·
                    refine ⟨849324388171505331193151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9059460140496056866060277 849324388171505331193151)
                    ·
                      rfl

theorem cell22_2481080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 1, 3, 5].length) (baseStart_2481080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2481080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2481080 prefixEnd_2481080 := by exact prefixLift 2481080
  have htrace : WordTrace (prefixWord ++ tailWord_2481080) baseStart_2481080 baseEnd_2481080 := by
    simpa [prefixWord, tailWord_2481080, baseEnd_2481080] using wordTrace_append hprefix tailTrace_2481080
  have hstable : (prefixWord ++ tailWord_2481080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2481080).length < 2 ^ (prefixWord ++ tailWord_2481080).sum := by decide
  have hdescent : baseEnd_2481080 < baseStart_2481080 := by decide
  rcases family_descends (prefixWord ++ tailWord_2481080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2481082 : List Nat := [3, 1, 1, 1, 2, 1, 4, 5, 4]
def baseStart_2481082 : Nat := 118140960795 + 2481082 * 2 ^ 59
def prefixEnd_2481082 : Nat := 4983230072969 + 3 ^ 40 * 2481082 * 2
def baseEnd_2481082 : Nat := 283108357604125997547715

theorem tailTrace_2481082 : CollatzResearch.WordTrace tailWord_2481082 prefixEnd_2481082 283108357604125997547715 := by
  unfold tailWord_2481082
  simp only [CollatzResearch.WordTrace]
  refine ⟨22623123699367780978859375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60328329864980749276958333 22623123699367780978859375)
  ·
    refine ⟨33934685549051671468289063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22623123699367780978859375 33934685549051671468289063)
    ·
      refine ⟨50902028323577507202433595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33934685549051671468289063 50902028323577507202433595)
      ·
        refine ⟨76353042485366260803650393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50902028323577507202433595 76353042485366260803650393)
        ·
          refine ⟨57264781864024695602737795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76353042485366260803650393 57264781864024695602737795)
          ·
            refine ⟨85897172796037043404106693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57264781864024695602737795 85897172796037043404106693)
            ·
              refine ⟨16105719899256945638270005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 85897172796037043404106693 16105719899256945638270005)
              ·
                refine ⟨1509911240555338653587813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16105719899256945638270005 1509911240555338653587813)
                ·
                  refine ⟨283108357604125997547715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1509911240555338653587813 283108357604125997547715)
                  ·
                    rfl

theorem cell22_2481082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 5, 4].length) (baseStart_2481082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2481082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2481082 prefixEnd_2481082 := by exact prefixLift 2481082
  have htrace : WordTrace (prefixWord ++ tailWord_2481082) baseStart_2481082 baseEnd_2481082 := by
    simpa [prefixWord, tailWord_2481082, baseEnd_2481082] using wordTrace_append hprefix tailTrace_2481082
  have hstable : (prefixWord ++ tailWord_2481082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2481082).length < 2 ^ (prefixWord ++ tailWord_2481082).sum := by decide
  have hdescent : baseEnd_2481082 < baseStart_2481082 := by decide
  rcases family_descends (prefixWord ++ tailWord_2481082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2481092 : List Nat := [2, 3, 3, 3, 2, 1, 2, 2, 1, 3]
def baseStart_2481092 : Nat := 118140960795 + 2481092 * 2 ^ 59
def prefixEnd_2481092 : Nat := 4983230072969 + 3 ^ 40 * 2481092 * 2
def baseEnd_2481092 : Nat := 849328496016741299893115

theorem tailTrace_2481092 : CollatzResearch.WordTrace tailWord_2481092 prefixEnd_2481092 849328496016741299893115 := by
  unfold tailWord_2481092
  simp only [CollatzResearch.WordTrace]
  refine ⟨45246429763717447811650765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60328573018289930415534353 45246429763717447811650765)
  ·
    refine ⟨16967411161394042929369037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45246429763717447811650765 16967411161394042929369037)
    ·
      refine ⟨6362779185522766098513389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16967411161394042929369037 6362779185522766098513389)
      ·
        refine ⟨2386042194571037286942521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6362779185522766098513389 2386042194571037286942521)
        ·
          refine ⟨1789531645928277965206891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2386042194571037286942521 1789531645928277965206891)
          ·
            refine ⟨2684297468892416947810337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1789531645928277965206891 2684297468892416947810337)
            ·
              refine ⟨2013223101669312710857753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2684297468892416947810337 2013223101669312710857753)
              ·
                refine ⟨1509917326251984533143315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2013223101669312710857753 1509917326251984533143315)
                ·
                  refine ⟨2264875989377976799714973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1509917326251984533143315 2264875989377976799714973)
                  ·
                    refine ⟨849328496016741299893115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2264875989377976799714973 849328496016741299893115)
                    ·
                      rfl

theorem cell22_2481092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 2, 2, 1, 3].length) (baseStart_2481092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2481092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2481092 prefixEnd_2481092 := by exact prefixLift 2481092
  have htrace : WordTrace (prefixWord ++ tailWord_2481092) baseStart_2481092 baseEnd_2481092 := by
    simpa [prefixWord, tailWord_2481092, baseEnd_2481092] using wordTrace_append hprefix tailTrace_2481092
  have hstable : (prefixWord ++ tailWord_2481092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2481092).length < 2 ^ (prefixWord ++ tailWord_2481092).sum := by decide
  have hdescent : baseEnd_2481092 < baseStart_2481092 := by decide
  rcases family_descends (prefixWord ++ tailWord_2481092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2481099 : List Nat := [1, 1, 1, 1, 3, 5, 4, 2, 4]
def baseStart_2481099 : Nat := 118140960795 + 2481099 * 2 ^ 59
def prefixEnd_2481099 : Nat := 4983230072969 + 3 ^ 40 * 2481099 * 2
def baseEnd_2481099 : Nat := 283110297419931871656031

theorem tailTrace_2481099 : CollatzResearch.WordTrace tailWord_2481099 prefixEnd_2481099 283110297419931871656031 := by
  unfold tailWord_2481099
  simp only [CollatzResearch.WordTrace]
  refine ⟨90493114838409535818806351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60328743225606357212537567 90493114838409535818806351)
  ·
    refine ⟨135739672257614303728209527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90493114838409535818806351 135739672257614303728209527)
    ·
      refine ⟨203609508386421455592314291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135739672257614303728209527 203609508386421455592314291)
      ·
        refine ⟨305414262579632183388471437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203609508386421455592314291 305414262579632183388471437)
        ·
          refine ⟨114530348467362068770676789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 305414262579632183388471437 114530348467362068770676789)
          ·
            refine ⟨10737220168815193947250949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 114530348467362068770676789 10737220168815193947250949)
            ·
              refine ⟨2013228781652848865109553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10737220168815193947250949 2013228781652848865109553)
              ·
                refine ⟨1509921586239636648832165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2013228781652848865109553 1509921586239636648832165)
                ·
                  refine ⟨283110297419931871656031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1509921586239636648832165 283110297419931871656031)
                  ·
                    rfl

theorem cell22_2481099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 4, 2, 4].length) (baseStart_2481099 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2481099 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2481099 prefixEnd_2481099 := by exact prefixLift 2481099
  have htrace : WordTrace (prefixWord ++ tailWord_2481099) baseStart_2481099 baseEnd_2481099 := by
    simpa [prefixWord, tailWord_2481099, baseEnd_2481099] using wordTrace_append hprefix tailTrace_2481099
  have hstable : (prefixWord ++ tailWord_2481099).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2481099).length < 2 ^ (prefixWord ++ tailWord_2481099).sum := by decide
  have hdescent : baseEnd_2481099 < baseStart_2481099 := by decide
  rcases family_descends (prefixWord ++ tailWord_2481099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2481114 : List Nat := [3, 1, 1, 2, 4, 1, 2, 3, 2, 3]
def baseStart_2481114 : Nat := 118140960795 + 2481114 * 2 ^ 59
def prefixEnd_2481114 : Nat := 4983230072969 + 3 ^ 40 * 2481114 * 2
def baseEnd_2481114 : Nat := 849336027066340575843047

theorem tailTrace_2481114 : CollatzResearch.WordTrace tailWord_2481114 prefixEnd_2481114 849336027066340575843047 := by
  unfold tailWord_2481114
  simp only [CollatzResearch.WordTrace]
  refine ⟨22623415483338798345150599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60329107955570128920401597 22623415483338798345150599)
  ·
    refine ⟨33935123225008197517725899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22623415483338798345150599 33935123225008197517725899)
    ·
      refine ⟨50902684837512296276588849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33935123225008197517725899 50902684837512296276588849)
      ·
        refine ⟨38177013628134222207441637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50902684837512296276588849 38177013628134222207441637)
        ·
          refine ⟨7158190055275166663895307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38177013628134222207441637 7158190055275166663895307)
          ·
            refine ⟨10737285082912749995842961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7158190055275166663895307 10737285082912749995842961)
            ·
              refine ⟨8052963812184562496882221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10737285082912749995842961 8052963812184562496882221)
              ·
                refine ⟨3019861429569210936330833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8052963812184562496882221 3019861429569210936330833)
                ·
                  refine ⟨2264896072176908202248125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3019861429569210936330833 2264896072176908202248125)
                  ·
                    refine ⟨849336027066340575843047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2264896072176908202248125 849336027066340575843047)
                    ·
                      rfl

theorem cell22_2481114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 3, 2, 3].length) (baseStart_2481114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2481114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2481114 prefixEnd_2481114 := by exact prefixLift 2481114
  have htrace : WordTrace (prefixWord ++ tailWord_2481114) baseStart_2481114 baseEnd_2481114 := by
    simpa [prefixWord, tailWord_2481114, baseEnd_2481114] using wordTrace_append hprefix tailTrace_2481114
  have hstable : (prefixWord ++ tailWord_2481114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2481114).length < 2 ^ (prefixWord ++ tailWord_2481114).sum := by decide
  have hdescent : baseEnd_2481114 < baseStart_2481114 := by decide
  rcases family_descends (prefixWord ++ tailWord_2481114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2481159 : List Nat := [1, 1, 4, 3, 1, 1, 4, 1, 3, 3]
def baseStart_2481159 : Nat := 118140960795 + 2481159 * 2 ^ 59
def prefixEnd_2481159 : Nat := 4983230072969 + 3 ^ 40 * 2481159 * 2
def baseEnd_2481159 : Nat := 849351431485975458467909

theorem tailTrace_2481159 : CollatzResearch.WordTrace tailWord_2481159 prefixEnd_2481159 849351431485975458467909 := by
  unfold tailWord_2481159
  simp only [CollatzResearch.WordTrace]
  refine ⟨90495303218192166065990531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60330202145461444043993687 90495303218192166065990531)
  ·
    refine ⟨135742954827288249098985797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90495303218192166065990531 135742954827288249098985797)
    ·
      refine ⟨25451804030116546706059837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 135742954827288249098985797 25451804030116546706059837)
      ·
        refine ⟨9544426511293705014772439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25451804030116546706059837 9544426511293705014772439)
        ·
          refine ⟨14316639766940557522158659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9544426511293705014772439 14316639766940557522158659)
          ·
            refine ⟨21474959650410836283237989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14316639766940557522158659 21474959650410836283237989)
            ·
              refine ⟨4026554934452031803107123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21474959650410836283237989 4026554934452031803107123)
              ·
                refine ⟨6039832401678047704660685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4026554934452031803107123 6039832401678047704660685)
                ·
                  refine ⟨2264937150629267889247757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6039832401678047704660685 2264937150629267889247757)
                  ·
                    refine ⟨849351431485975458467909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2264937150629267889247757 849351431485975458467909)
                    ·
                      rfl

theorem cell22_2481159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 1, 3, 3].length) (baseStart_2481159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2481159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2481159 prefixEnd_2481159 := by exact prefixLift 2481159
  have htrace : WordTrace (prefixWord ++ tailWord_2481159) baseStart_2481159 baseEnd_2481159 := by
    simpa [prefixWord, tailWord_2481159, baseEnd_2481159] using wordTrace_append hprefix tailTrace_2481159
  have hstable : (prefixWord ++ tailWord_2481159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2481159).length < 2 ^ (prefixWord ++ tailWord_2481159).sum := by decide
  have hdescent : baseEnd_2481159 < baseStart_2481159 := by decide
  rcases family_descends (prefixWord ++ tailWord_2481159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2481262 : List Nat := [4, 1, 2, 2, 1, 12]
def baseStart_2481262 : Nat := 118140960795 + 2481262 * 2 ^ 59
def prefixEnd_2481262 : Nat := 4983230072969 + 3 ^ 40 * 2481262 * 2
def baseEnd_2481262 : Nat := 10486255438159475594353

theorem tailTrace_2481262 : CollatzResearch.WordTrace tailWord_2481262 prefixEnd_2481262 10486255438159475594353 := by
  unfold tailWord_2481262
  simp only [CollatzResearch.WordTrace]
  refine ⟨11312382492102376832123755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60332706624546009771326693 11312382492102376832123755)
  ·
    refine ⟨16968573738153565248185633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11312382492102376832123755 16968573738153565248185633)
    ·
      refine ⟨12726430303615173936139225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16968573738153565248185633 12726430303615173936139225)
      ·
        refine ⟨9544822727711380452104419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12726430303615173936139225 9544822727711380452104419)
        ·
          refine ⟨14317234091567070678156629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9544822727711380452104419 14317234091567070678156629)
          ·
            refine ⟨10486255438159475594353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 14317234091567070678156629 10486255438159475594353)
            ·
              rfl

theorem cell22_2481262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 12].length) (baseStart_2481262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2481262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2481262 prefixEnd_2481262 := by exact prefixLift 2481262
  have htrace : WordTrace (prefixWord ++ tailWord_2481262) baseStart_2481262 baseEnd_2481262 := by
    simpa [prefixWord, tailWord_2481262, baseEnd_2481262] using wordTrace_append hprefix tailTrace_2481262
  have hstable : (prefixWord ++ tailWord_2481262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2481262).length < 2 ^ (prefixWord ++ tailWord_2481262).sum := by decide
  have hdescent : baseEnd_2481262 < baseStart_2481262 := by decide
  rcases family_descends (prefixWord ++ tailWord_2481262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2481266 : List Nat := [3, 2, 1, 2, 2, 1, 4, 2, 2, 3]
def baseStart_2481266 : Nat := 118140960795 + 2481266 * 2 ^ 59
def prefixEnd_2481266 : Nat := 4983230072969 + 3 ^ 40 * 2481266 * 2
def baseEnd_2481266 : Nat := 849388059772662846042581

theorem tailTrace_2481266 : CollatzResearch.WordTrace tailWord_2481266 prefixEnd_2481266 849388059772662846042581 := by
  unfold tailWord_2481266
  simp only [CollatzResearch.WordTrace]
  refine ⟨22624801457201130835033913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60332803885869682226757101 22624801457201130835033913)
  ·
    refine ⟨16968601092900848126275435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22624801457201130835033913 16968601092900848126275435)
    ·
      refine ⟨25452901639351272189413153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16968601092900848126275435 25452901639351272189413153)
      ·
        refine ⟨19089676229513454142059865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25452901639351272189413153 19089676229513454142059865)
        ·
          refine ⟨14317257172135090606544899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19089676229513454142059865 14317257172135090606544899)
          ·
            refine ⟨21475885758202635909817349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14317257172135090606544899 21475885758202635909817349)
            ·
              refine ⟨4026728579662994233090753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21475885758202635909817349 4026728579662994233090753)
              ·
                refine ⟨3020046434747245674818065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4026728579662994233090753 3020046434747245674818065)
                ·
                  refine ⟨2265034826060434256113549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3020046434747245674818065 2265034826060434256113549)
                  ·
                    refine ⟨849388059772662846042581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2265034826060434256113549 849388059772662846042581)
                    ·
                      rfl

theorem cell22_2481266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 2, 2, 3].length) (baseStart_2481266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2481266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2481266 prefixEnd_2481266 := by exact prefixLift 2481266
  have htrace : WordTrace (prefixWord ++ tailWord_2481266) baseStart_2481266 baseEnd_2481266 := by
    simpa [prefixWord, tailWord_2481266, baseEnd_2481266] using wordTrace_append hprefix tailTrace_2481266
  have hstable : (prefixWord ++ tailWord_2481266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2481266).length < 2 ^ (prefixWord ++ tailWord_2481266).sum := by decide
  have hdescent : baseEnd_2481266 < baseStart_2481266 := by decide
  rcases family_descends (prefixWord ++ tailWord_2481266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2481386 : List Nat := [3, 1, 3, 1, 1, 5, 1, 1, 6]
def baseStart_2481386 : Nat := 118140960795 + 2481386 * 2 ^ 59
def prefixEnd_2481386 : Nat := 4983230072969 + 3 ^ 40 * 2481386 * 2
def baseEnd_2481386 : Nat := 283143046075007511014071

theorem tailTrace_2481386 : CollatzResearch.WordTrace tailWord_2481386 prefixEnd_2481386 283143046075007511014071 := by
  unfold tailWord_2481386
  simp only [CollatzResearch.WordTrace]
  refine ⟨22625895647092445958626003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60335721725579855889669341 22625895647092445958626003)
  ·
    refine ⟨33938843470638668937939005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22625895647092445958626003 33938843470638668937939005)
    ·
      refine ⟨12727066301489500851727127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33938843470638668937939005 12727066301489500851727127)
      ·
        refine ⟨19090599452234251277590691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12727066301489500851727127 19090599452234251277590691)
        ·
          refine ⟨28635899178351376916386037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19090599452234251277590691 28635899178351376916386037)
          ·
            refine ⟨2684615547970441585911191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28635899178351376916386037 2684615547970441585911191)
            ·
              refine ⟨4026923321955662378866787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2684615547970441585911191 4026923321955662378866787)
              ·
                refine ⟨6040384982933493568300181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4026923321955662378866787 6040384982933493568300181)
                ·
                  refine ⟨283143046075007511014071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6040384982933493568300181 283143046075007511014071)
                  ·
                    rfl

theorem cell22_2481386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 1, 6].length) (baseStart_2481386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2481386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2481386 prefixEnd_2481386 := by exact prefixLift 2481386
  have htrace : WordTrace (prefixWord ++ tailWord_2481386) baseStart_2481386 baseEnd_2481386 := by
    simpa [prefixWord, tailWord_2481386, baseEnd_2481386] using wordTrace_append hprefix tailTrace_2481386
  have hstable : (prefixWord ++ tailWord_2481386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2481386).length < 2 ^ (prefixWord ++ tailWord_2481386).sum := by decide
  have hdescent : baseEnd_2481386 < baseStart_2481386 := by decide
  rcases family_descends (prefixWord ++ tailWord_2481386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2481401 : List Nat := [1, 2, 1, 3, 1, 1, 5, 3, 2, 3]
def baseStart_2481401 : Nat := 118140960795 + 2481401 * 2 ^ 59
def prefixEnd_2481401 : Nat := 4983230072969 + 3 ^ 40 * 2481401 * 2
def baseEnd_2481401 : Nat := 849434273031567493917167

theorem tailTrace_2481401 : CollatzResearch.WordTrace tailWord_2481401 prefixEnd_2481401 849434273031567493917167 := by
  unfold tailWord_2481401
  simp only [CollatzResearch.WordTrace]
  refine ⟨90504129683315441396300057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60336086455543627597533371 90504129683315441396300057)
  ·
    refine ⟨67878097262486581047225043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90504129683315441396300057 67878097262486581047225043)
    ·
      refine ⟨101817145893729871570837565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67878097262486581047225043 101817145893729871570837565)
      ·
        refine ⟨38181429710148701839064087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101817145893729871570837565 38181429710148701839064087)
        ·
          refine ⟨57272144565223052758596131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38181429710148701839064087 57272144565223052758596131)
          ·
            refine ⟨85908216847834579137894197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57272144565223052758596131 85908216847834579137894197)
            ·
              refine ⟨8053895329484491794177581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 85908216847834579137894197 8053895329484491794177581)
              ·
                refine ⟨3020210748556684422816593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8053895329484491794177581 3020210748556684422816593)
                ·
                  refine ⟨2265158061417513317112445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3020210748556684422816593 2265158061417513317112445)
                  ·
                    refine ⟨849434273031567493917167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2265158061417513317112445 849434273031567493917167)
                    ·
                      rfl

theorem cell22_2481401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 3, 2, 3].length) (baseStart_2481401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2481401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2481401 prefixEnd_2481401 := by exact prefixLift 2481401
  have htrace : WordTrace (prefixWord ++ tailWord_2481401) baseStart_2481401 baseEnd_2481401 := by
    simpa [prefixWord, tailWord_2481401, baseEnd_2481401] using wordTrace_append hprefix tailTrace_2481401
  have hstable : (prefixWord ++ tailWord_2481401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2481401).length < 2 ^ (prefixWord ++ tailWord_2481401).sum := by decide
  have hdescent : baseEnd_2481401 < baseStart_2481401 := by decide
  rcases family_descends (prefixWord ++ tailWord_2481401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2481444 : List Nat := [2, 3, 1, 3, 1, 1, 1, 1, 1, 8]
def baseStart_2481444 : Nat := 118140960795 + 2481444 * 2 ^ 59
def prefixEnd_2481444 : Nat := 4983230072969 + 3 ^ 40 * 2481444 * 2
def baseEnd_2481444 : Nat := 849448992810329715092035

theorem tailTrace_2481444 : CollatzResearch.WordTrace tailWord_2481444 prefixEnd_2481444 849448992810329715092035 := by
  unfold tailWord_2481444
  simp only [CollatzResearch.WordTrace]
  refine ⟨45252849011079829870057693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60337132014773106493410257 45252849011079829870057693)
  ·
    refine ⟨16969818379154936201271635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45252849011079829870057693 16969818379154936201271635)
    ·
      refine ⟨25454727568732404301907453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16969818379154936201271635 25454727568732404301907453)
      ·
        refine ⟨9545522838274651613215295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25454727568732404301907453 9545522838274651613215295)
        ·
          refine ⟨14318284257411977419822943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9545522838274651613215295 14318284257411977419822943)
          ·
            refine ⟨21477426386117966129734415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14318284257411977419822943 21477426386117966129734415)
            ·
              refine ⟨32216139579176949194601623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21477426386117966129734415 32216139579176949194601623)
              ·
                refine ⟨48324209368765423791902435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32216139579176949194601623 48324209368765423791902435)
                ·
                  refine ⟨72486314053148135687853653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48324209368765423791902435 72486314053148135687853653)
                  ·
                    refine ⟨849448992810329715092035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 72486314053148135687853653 849448992810329715092035)
                    ·
                      rfl

theorem cell22_2481444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 1, 8].length) (baseStart_2481444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2481444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2481444 prefixEnd_2481444 := by exact prefixLift 2481444
  have htrace : WordTrace (prefixWord ++ tailWord_2481444) baseStart_2481444 baseEnd_2481444 := by
    simpa [prefixWord, tailWord_2481444, baseEnd_2481444] using wordTrace_append hprefix tailTrace_2481444
  have hstable : (prefixWord ++ tailWord_2481444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2481444).length < 2 ^ (prefixWord ++ tailWord_2481444).sum := by decide
  have hdescent : baseEnd_2481444 < baseStart_2481444 := by decide
  rcases family_descends (prefixWord ++ tailWord_2481444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2481493 : List Nat := [1, 3, 2, 2, 3, 3, 1, 2, 5]
def baseStart_2481493 : Nat := 118140960795 + 2481493 * 2 ^ 59
def prefixEnd_2481493 : Nat := 4983230072969 + 3 ^ 40 * 2481493 * 2
def baseEnd_2481493 : Nat := 283155255503903306872295

theorem tailTrace_2481493 : CollatzResearch.WordTrace tailWord_2481493 prefixEnd_2481493 283155255503903306872295 := by
  unfold tailWord_2481493
  simp only [CollatzResearch.WordTrace]
  refine ⟨90507485198982141108649133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60338323465988094072432755 90507485198982141108649133)
  ·
    refine ⟨33940306949618302915743425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90507485198982141108649133 33940306949618302915743425)
    ·
      refine ⟨25455230212213727186807569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33940306949618302915743425 25455230212213727186807569)
      ·
        refine ⟨19091422659160295390105677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25455230212213727186807569 19091422659160295390105677)
        ·
          refine ⟨7159283497185110771289629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19091422659160295390105677 7159283497185110771289629)
          ·
            refine ⟨2684731311444416539233611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7159283497185110771289629 2684731311444416539233611)
            ·
              refine ⟨4027096967166624808850417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2684731311444416539233611 4027096967166624808850417)
              ·
                refine ⟨3020322725374968606637813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4027096967166624808850417 3020322725374968606637813)
                ·
                  refine ⟨283155255503903306872295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3020322725374968606637813 283155255503903306872295)
                  ·
                    rfl

theorem cell22_2481493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 2, 5].length) (baseStart_2481493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2481493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2481493 prefixEnd_2481493 := by exact prefixLift 2481493
  have htrace : WordTrace (prefixWord ++ tailWord_2481493) baseStart_2481493 baseEnd_2481493 := by
    simpa [prefixWord, tailWord_2481493, baseEnd_2481493] using wordTrace_append hprefix tailTrace_2481493
  have hstable : (prefixWord ++ tailWord_2481493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2481493).length < 2 ^ (prefixWord ++ tailWord_2481493).sum := by decide
  have hdescent : baseEnd_2481493 < baseStart_2481493 := by decide
  rcases family_descends (prefixWord ++ tailWord_2481493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2481570 : List Nat := [3, 3, 1, 2, 1, 3, 1, 3, 2, 3]
def baseStart_2481570 : Nat := 118140960795 + 2481570 * 2 ^ 59
def prefixEnd_2481570 : Nat := 4983230072969 + 3 ^ 40 * 2481570 * 2
def baseEnd_2481570 : Nat := 849492125185307386441649

theorem tailTrace_2481570 : CollatzResearch.WordTrace tailWord_2481570 prefixEnd_2481570 849492125185307386441649 := by
  unfold tailWord_2481570
  simp only [CollatzResearch.WordTrace]
  refine ⟨22627573404925795814800541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60340195746468788839468109 22627573404925795814800541)
  ·
    refine ⟨8485340026847173430550203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22627573404925795814800541 8485340026847173430550203)
    ·
      refine ⟨12728010040270760145825305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8485340026847173430550203 12728010040270760145825305)
      ·
        refine ⟨9546007530203070109368979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12728010040270760145825305 9546007530203070109368979)
        ·
          refine ⟨14319011295304605164053469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9546007530203070109368979 14319011295304605164053469)
          ·
            refine ⟨5369629235739226936520051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14319011295304605164053469 5369629235739226936520051)
            ·
              refine ⟨8054443853608840404780077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5369629235739226936520051 8054443853608840404780077)
              ·
                refine ⟨3020416445103315151792529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8054443853608840404780077 3020416445103315151792529)
                ·
                  refine ⟨2265312333827486363844397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3020416445103315151792529 2265312333827486363844397)
                  ·
                    refine ⟨849492125185307386441649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2265312333827486363844397 849492125185307386441649)
                    ·
                      rfl

theorem cell22_2481570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 3, 2, 3].length) (baseStart_2481570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2481570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2481570 prefixEnd_2481570 := by exact prefixLift 2481570
  have htrace : WordTrace (prefixWord ++ tailWord_2481570) baseStart_2481570 baseEnd_2481570 := by
    simpa [prefixWord, tailWord_2481570, baseEnd_2481570] using wordTrace_append hprefix tailTrace_2481570
  have hstable : (prefixWord ++ tailWord_2481570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2481570).length < 2 ^ (prefixWord ++ tailWord_2481570).sum := by decide
  have hdescent : baseEnd_2481570 < baseStart_2481570 := by decide
  rcases family_descends (prefixWord ++ tailWord_2481570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2481611 : List Nat := [1, 1, 1, 1, 3, 3, 3, 4, 5]
def baseStart_2481611 : Nat := 118140960795 + 2481611 * 2 ^ 59
def prefixEnd_2481611 : Nat := 4983230072969 + 3 ^ 40 * 2481611 * 2
def baseEnd_2481611 : Nat := 283168720107732315388841

theorem tailTrace_2481611 : CollatzResearch.WordTrace tailWord_2481611 prefixEnd_2481611 283168720107732315388841 := by
  unfold tailWord_2481611
  simp only [CollatzResearch.WordTrace]
  refine ⟨90511789012554647261444687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60341192675036431507629791 90511789012554647261444687)
  ·
    refine ⟨135767683518831970892167031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90511789012554647261444687 135767683518831970892167031)
    ·
      refine ⟨203651525278247956338250547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135767683518831970892167031 203651525278247956338250547)
      ·
        refine ⟨305477287917371934507375821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203651525278247956338250547 305477287917371934507375821)
        ·
          refine ⟨114553982969014475440265933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 305477287917371934507375821 114553982969014475440265933)
          ·
            refine ⟨42957743613380428290099725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 114553982969014475440265933 42957743613380428290099725)
            ·
              refine ⟨16109153855017660608787397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42957743613380428290099725 16109153855017660608787397)
              ·
                refine ⟨3020466347815811364147637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16109153855017660608787397 3020466347815811364147637)
                ·
                  refine ⟨283168720107732315388841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3020466347815811364147637 283168720107732315388841)
                  ·
                    rfl

theorem cell22_2481611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 4, 5].length) (baseStart_2481611 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2481611 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2481611 prefixEnd_2481611 := by exact prefixLift 2481611
  have htrace : WordTrace (prefixWord ++ tailWord_2481611) baseStart_2481611 baseEnd_2481611 := by
    simpa [prefixWord, tailWord_2481611, baseEnd_2481611] using wordTrace_append hprefix tailTrace_2481611
  have hstable : (prefixWord ++ tailWord_2481611).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2481611).length < 2 ^ (prefixWord ++ tailWord_2481611).sum := by decide
  have hdescent : baseEnd_2481611 < baseStart_2481611 := by decide
  rcases family_descends (prefixWord ++ tailWord_2481611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2481626 : List Nat := [3, 1, 1, 2, 3, 2, 1, 1, 1, 7]
def baseStart_2481626 : Nat := 118140960795 + 2481626 * 2 ^ 59
def prefixEnd_2481626 : Nat := 4983230072969 + 3 ^ 40 * 2481626 * 2
def baseEnd_2481626 : Nat := 849511295129741907041477

theorem tailTrace_2481626 : CollatzResearch.WordTrace tailWord_2481626 prefixEnd_2481626 849511295129741907041477 := by
  unfold tailWord_2481626
  simp only [CollatzResearch.WordTrace]
  refine ⟨22628084026875076205810183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60341557405000203215493821 22628084026875076205810183)
  ·
    refine ⟨33942126040312614308715275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22628084026875076205810183 33942126040312614308715275)
    ·
      refine ⟨50913189060468921463072913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33942126040312614308715275 50913189060468921463072913)
      ·
        refine ⟨38184891795351691097304685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50913189060468921463072913 38184891795351691097304685)
        ·
          refine ⟨14319334423256884161489257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38184891795351691097304685 14319334423256884161489257)
          ·
            refine ⟨10739500817442663121116943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14319334423256884161489257 10739500817442663121116943)
            ·
              refine ⟨16109251226163994681675415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10739500817442663121116943 16109251226163994681675415)
              ·
                refine ⟨24163876839245992022513123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16109251226163994681675415 24163876839245992022513123)
                ·
                  refine ⟨36245815258868988033769685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24163876839245992022513123 36245815258868988033769685)
                  ·
                    refine ⟨849511295129741907041477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36245815258868988033769685 849511295129741907041477)
                    ·
                      rfl

theorem cell22_2481626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 1, 1, 7].length) (baseStart_2481626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2481626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2481626 prefixEnd_2481626 := by exact prefixLift 2481626
  have htrace : WordTrace (prefixWord ++ tailWord_2481626) baseStart_2481626 baseEnd_2481626 := by
    simpa [prefixWord, tailWord_2481626, baseEnd_2481626] using wordTrace_append hprefix tailTrace_2481626
  have hstable : (prefixWord ++ tailWord_2481626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2481626).length < 2 ^ (prefixWord ++ tailWord_2481626).sum := by decide
  have hdescent : baseEnd_2481626 < baseStart_2481626 := by decide
  rcases family_descends (prefixWord ++ tailWord_2481626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2481658 : List Nat := [3, 1, 1, 1, 1, 2, 5, 3, 1, 4]
def baseStart_2481658 : Nat := 118140960795 + 2481658 * 2 ^ 59
def prefixEnd_2481658 : Nat := 4983230072969 + 3 ^ 40 * 2481658 * 2
def baseEnd_2481658 : Nat := 849522249383704490241379

theorem tailTrace_2481658 : CollatzResearch.WordTrace tailWord_2481658 prefixEnd_2481658 849522249383704490241379 := by
  unfold tailWord_2481658
  simp only [CollatzResearch.WordTrace]
  refine ⟨22628375810846093572101407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60342335495589582858937085 22628375810846093572101407)
  ·
    refine ⟨33942563716269140358152111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22628375810846093572101407 33942563716269140358152111)
    ·
      refine ⟨50913845574403710537228167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33942563716269140358152111 50913845574403710537228167)
      ·
        refine ⟨76370768361605565805842251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50913845574403710537228167 76370768361605565805842251)
        ·
          refine ⟨114556152542408348708763377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76370768361605565805842251 114556152542408348708763377)
          ·
            refine ⟨85917114406806261531572533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114556152542408348708763377 85917114406806261531572533)
            ·
              refine ⟨8054729475638087018584925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 85917114406806261531572533 8054729475638087018584925)
              ·
                refine ⟨3020523553364282631969347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8054729475638087018584925 3020523553364282631969347)
                ·
                  refine ⟨4530785330046423947954021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3020523553364282631969347 4530785330046423947954021)
                  ·
                    refine ⟨849522249383704490241379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4530785330046423947954021 849522249383704490241379)
                    ·
                      rfl

theorem cell22_2481658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 3, 1, 4].length) (baseStart_2481658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2481658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2481658 prefixEnd_2481658 := by exact prefixLift 2481658
  have htrace : WordTrace (prefixWord ++ tailWord_2481658) baseStart_2481658 baseEnd_2481658 := by
    simpa [prefixWord, tailWord_2481658, baseEnd_2481658] using wordTrace_append hprefix tailTrace_2481658
  have hstable : (prefixWord ++ tailWord_2481658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2481658).length < 2 ^ (prefixWord ++ tailWord_2481658).sum := by decide
  have hdescent : baseEnd_2481658 < baseStart_2481658 := by decide
  rcases family_descends (prefixWord ++ tailWord_2481658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2481673 : List Nat := [1, 2, 1, 1, 3, 1, 3, 6, 4]
def baseStart_2481673 : Nat := 118140960795 + 2481673 * 2 ^ 59
def prefixEnd_2481673 : Nat := 4983230072969 + 3 ^ 40 * 2481673 * 2
def baseEnd_2481673 : Nat := 283175794730083150372111

theorem tailTrace_2481673 : CollatzResearch.WordTrace tailWord_2481673 prefixEnd_2481673 283175794730083150372111 := by
  unfold tailWord_2481673
  simp only [CollatzResearch.WordTrace]
  refine ⟨90514050338330031850201673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60342700225553354566801115 90514050338330031850201673)
  ·
    refine ⟨67885537753747523887651255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90514050338330031850201673 67885537753747523887651255)
    ·
      refine ⟨101828306630621285831476883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67885537753747523887651255 101828306630621285831476883)
      ·
        refine ⟨152742459945931928747215325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101828306630621285831476883 152742459945931928747215325)
        ·
          refine ⟨57278422479724473280205747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 152742459945931928747215325 57278422479724473280205747)
          ·
            refine ⟨85917633719586709920308621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57278422479724473280205747 85917633719586709920308621)
            ·
              refine ⟨32219112644845016220115733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85917633719586709920308621 32219112644845016220115733)
              ·
                refine ⟨1510270905227110135317925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 32219112644845016220115733 1510270905227110135317925)
                ·
                  refine ⟨283175794730083150372111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1510270905227110135317925 283175794730083150372111)
                  ·
                    rfl

theorem cell22_2481673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 6, 4].length) (baseStart_2481673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2481673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2481673 prefixEnd_2481673 := by exact prefixLift 2481673
  have htrace : WordTrace (prefixWord ++ tailWord_2481673) baseStart_2481673 baseEnd_2481673 := by
    simpa [prefixWord, tailWord_2481673, baseEnd_2481673] using wordTrace_append hprefix tailTrace_2481673
  have hstable : (prefixWord ++ tailWord_2481673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2481673).length < 2 ^ (prefixWord ++ tailWord_2481673).sum := by decide
  have hdescent : baseEnd_2481673 < baseStart_2481673 := by decide
  rcases family_descends (prefixWord ++ tailWord_2481673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2481853 : List Nat := [1, 4, 1, 2, 1, 2, 2, 9]
def baseStart_2481853 : Nat := 118140960795 + 2481853 * 2 ^ 59
def prefixEnd_2481853 : Nat := 4983230072969 + 3 ^ 40 * 2481853 * 2
def baseEnd_2481853 : Nat := 94398777985420997957309

theorem tailTrace_2481853 : CollatzResearch.WordTrace tailWord_2481853 prefixEnd_2481853 94398777985420997957309 := by
  unfold tailWord_2481853
  simp only [CollatzResearch.WordTrace]
  refine ⟨90520615477677922591754213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60347076985118615061169475 90520615477677922591754213)
  ·
    refine ⟨16972615402064610485953915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90520615477677922591754213 16972615402064610485953915)
    ·
      refine ⟨25458923103096915728930873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16972615402064610485953915 25458923103096915728930873)
      ·
        refine ⟨19094192327322686796698155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25458923103096915728930873 19094192327322686796698155)
        ·
          refine ⟨28641288490984030195047233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19094192327322686796698155 28641288490984030195047233)
          ·
            refine ⟨21480966368238022646285425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28641288490984030195047233 21480966368238022646285425)
            ·
              refine ⟨16110724776178516984714069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21480966368238022646285425 16110724776178516984714069)
              ·
                refine ⟨94398777985420997957309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16110724776178516984714069 94398777985420997957309)
                ·
                  rfl

theorem cell22_2481853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 9].length) (baseStart_2481853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2481853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2481853 prefixEnd_2481853 := by exact prefixLift 2481853
  have htrace : WordTrace (prefixWord ++ tailWord_2481853) baseStart_2481853 baseEnd_2481853 := by
    simpa [prefixWord, tailWord_2481853, baseEnd_2481853] using wordTrace_append hprefix tailTrace_2481853
  have hstable : (prefixWord ++ tailWord_2481853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2481853).length < 2 ^ (prefixWord ++ tailWord_2481853).sum := by decide
  have hdescent : baseEnd_2481853 < baseStart_2481853 := by decide
  rcases family_descends (prefixWord ++ tailWord_2481853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2481908 : List Nat := [2, 6, 1, 1, 1, 1, 4, 1, 2, 3]
def baseStart_2481908 : Nat := 118140960795 + 2481908 * 2 ^ 59
def prefixEnd_2481908 : Nat := 4983230072969 + 3 ^ 40 * 2481908 * 2
def baseEnd_2481908 : Nat := 849607829492787171490613

theorem tailTrace_2481908 : CollatzResearch.WordTrace tailWord_2481908 prefixEnd_2481908 849607829492787171490613 := by
  unfold tailWord_2481908
  simp only [CollatzResearch.WordTrace]
  refine ⟨45261310746239333492503189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60348414328319111323337585 45261310746239333492503189)
  ·
    refine ⟨2121623941229968757461087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 45261310746239333492503189 2121623941229968757461087)
    ·
      refine ⟨3182435911844953136191631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2121623941229968757461087 3182435911844953136191631)
      ·
        refine ⟨4773653867767429704287447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3182435911844953136191631 4773653867767429704287447)
        ·
          refine ⟨7160480801651144556431171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4773653867767429704287447 7160480801651144556431171)
          ·
            refine ⟨10740721202476716834646757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7160480801651144556431171 10740721202476716834646757)
            ·
              refine ⟨2013885225464384406496267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10740721202476716834646757 2013885225464384406496267)
              ·
                refine ⟨3020827838196576609744401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2013885225464384406496267 3020827838196576609744401)
                ·
                  refine ⟨2265620878647432457308301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3020827838196576609744401 2265620878647432457308301)
                  ·
                    refine ⟨849607829492787171490613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2265620878647432457308301 849607829492787171490613)
                    ·
                      rfl

theorem cell22_2481908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_2481908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2481908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2481908 prefixEnd_2481908 := by exact prefixLift 2481908
  have htrace : WordTrace (prefixWord ++ tailWord_2481908) baseStart_2481908 baseEnd_2481908 := by
    simpa [prefixWord, tailWord_2481908, baseEnd_2481908] using wordTrace_append hprefix tailTrace_2481908
  have hstable : (prefixWord ++ tailWord_2481908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2481908).length < 2 ^ (prefixWord ++ tailWord_2481908).sum := by decide
  have hdescent : baseEnd_2481908 < baseStart_2481908 := by decide
  rcases family_descends (prefixWord ++ tailWord_2481908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2481996 : List Nat := [2, 2, 1, 3, 4, 2, 2, 1, 1, 4]
def baseStart_2481996 : Nat := 118140960795 + 2481996 * 2 ^ 59
def prefixEnd_2481996 : Nat := 4983230072969 + 3 ^ 40 * 2481996 * 2
def baseEnd_2481996 : Nat := 849637953691184275290343

theorem tailTrace_2481996 : CollatzResearch.WordTrace tailWord_2481996 prefixEnd_2481996 849637953691184275290343 := by
  unfold tailWord_2481996
  simp only [CollatzResearch.WordTrace]
  refine ⟨45262915558079929007104921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60350554077439905342806561 45262915558079929007104921)
  ·
    refine ⟨33947186668559946755328691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45262915558079929007104921 33947186668559946755328691)
    ·
      refine ⟨50920780002839920132993037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33947186668559946755328691 50920780002839920132993037)
      ·
        refine ⟨19095292501064970049872389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50920780002839920132993037 19095292501064970049872389)
        ·
          refine ⟨3580367343949681884351073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19095292501064970049872389 3580367343949681884351073)
          ·
            refine ⟨2685275507962261413263305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3580367343949681884351073 2685275507962261413263305)
            ·
              refine ⟨2013956630971696059947479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2685275507962261413263305 2013956630971696059947479)
              ·
                refine ⟨3020934946457544089921219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2013956630971696059947479 3020934946457544089921219)
                ·
                  refine ⟨4531402419686316134881829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3020934946457544089921219 4531402419686316134881829)
                  ·
                    refine ⟨849637953691184275290343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4531402419686316134881829 849637953691184275290343)
                    ·
                      rfl

theorem cell22_2481996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 2, 1, 1, 4].length) (baseStart_2481996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2481996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2481996 prefixEnd_2481996 := by exact prefixLift 2481996
  have htrace : WordTrace (prefixWord ++ tailWord_2481996) baseStart_2481996 baseEnd_2481996 := by
    simpa [prefixWord, tailWord_2481996, baseEnd_2481996] using wordTrace_append hprefix tailTrace_2481996
  have hstable : (prefixWord ++ tailWord_2481996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2481996).length < 2 ^ (prefixWord ++ tailWord_2481996).sum := by decide
  have hdescent : baseEnd_2481996 < baseStart_2481996 := by decide
  rcases family_descends (prefixWord ++ tailWord_2481996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2482005 : List Nat := [1, 3, 2, 2, 2, 3, 9]
def baseStart_2482005 : Nat := 118140960795 + 2482005 * 2 ^ 59
def prefixEnd_2482005 : Nat := 4983230072969 + 3 ^ 40 * 2482005 * 2
def baseEnd_2482005 : Nat := 31468186465744861178345

theorem tailTrace_2482005 : CollatzResearch.WordTrace tailWord_2482005 prefixEnd_2482005 31468186465744861178345 := by
  unfold tailWord_2482005
  simp only [CollatzResearch.WordTrace]
  refine ⟨90526159373127252551287469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60350772915418168367524979 90526159373127252551287469)
  ·
    refine ⟨33947309764922719706732801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90526159373127252551287469 33947309764922719706732801)
    ·
      refine ⟨25460482323692039780049601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33947309764922719706732801 25460482323692039780049601)
      ·
        refine ⟨19095361742769029835037201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25460482323692039780049601 19095361742769029835037201)
        ·
          refine ⟨14321521307076772376277901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19095361742769029835037201 14321521307076772376277901)
          ·
            refine ⟨5370570490153789641104213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14321521307076772376277901 5370570490153789641104213)
            ·
              refine ⟨31468186465744861178345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5370570490153789641104213 31468186465744861178345)
              ·
                rfl

theorem cell22_2482005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 9].length) (baseStart_2482005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2482005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2482005 prefixEnd_2482005 := by exact prefixLift 2482005
  have htrace : WordTrace (prefixWord ++ tailWord_2482005) baseStart_2482005 baseEnd_2482005 := by
    simpa [prefixWord, tailWord_2482005, baseEnd_2482005] using wordTrace_append hprefix tailTrace_2482005
  have hstable : (prefixWord ++ tailWord_2482005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2482005).length < 2 ^ (prefixWord ++ tailWord_2482005).sum := by decide
  have hdescent : baseEnd_2482005 < baseStart_2482005 := by decide
  rcases family_descends (prefixWord ++ tailWord_2482005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2482026 : List Nat := [3, 1, 3, 4, 1, 2, 1, 1, 1, 5]
def baseStart_2482026 : Nat := 118140960795 + 2482026 * 2 ^ 59
def prefixEnd_2482026 : Nat := 4983230072969 + 3 ^ 40 * 2482026 * 2
def baseEnd_2482026 : Nat := 849648223304274197040251

theorem tailTrace_2482026 : CollatzResearch.WordTrace tailWord_2482026 prefixEnd_2482026 849648223304274197040251 := by
  unfold tailWord_2482026
  simp only [CollatzResearch.WordTrace]
  refine ⟨22631731326512793284450483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60351283537367448758534621 22631731326512793284450483)
  ·
    refine ⟨33947596989769189926675725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22631731326512793284450483 33947596989769189926675725)
    ·
      refine ⟨12730348871163446222503397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33947596989769189926675725 12730348871163446222503397)
      ·
        refine ⟨2386940413343146166719387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12730348871163446222503397 2386940413343146166719387)
        ·
          refine ⟨3580410620014719250079081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2386940413343146166719387 3580410620014719250079081)
          ·
            refine ⟨2685307965011039437559311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3580410620014719250079081 2685307965011039437559311)
            ·
              refine ⟨4027961947516559156338967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2685307965011039437559311 4027961947516559156338967)
              ·
                refine ⟨6041942921274838734508451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4027961947516559156338967 6041942921274838734508451)
                ·
                  refine ⟨9062914381912258101762677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6041942921274838734508451 9062914381912258101762677)
                  ·
                    refine ⟨849648223304274197040251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9062914381912258101762677 849648223304274197040251)
                    ·
                      rfl

theorem cell22_2482026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 1, 1, 5].length) (baseStart_2482026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2482026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2482026 prefixEnd_2482026 := by exact prefixLift 2482026
  have htrace : WordTrace (prefixWord ++ tailWord_2482026) baseStart_2482026 baseEnd_2482026 := by
    simpa [prefixWord, tailWord_2482026, baseEnd_2482026] using wordTrace_append hprefix tailTrace_2482026
  have hstable : (prefixWord ++ tailWord_2482026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2482026).length < 2 ^ (prefixWord ++ tailWord_2482026).sum := by decide
  have hdescent : baseEnd_2482026 < baseStart_2482026 := by decide
  rcases family_descends (prefixWord ++ tailWord_2482026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2482065 : List Nat := [1, 2, 2, 1, 1, 1, 4, 1, 4, 5]
def baseStart_2482065 : Nat := 118140960795 + 2482065 * 2 ^ 59
def prefixEnd_2482065 : Nat := 4983230072969 + 3 ^ 40 * 2482065 * 2
def baseEnd_2482065 : Nat := 849661573801291095315131

theorem tailTrace_2482065 : CollatzResearch.WordTrace tailWord_2482065 prefixEnd_2482065 849661573801291095315131 := by
  unfold tailWord_2482065
  simp only [CollatzResearch.WordTrace]
  refine ⟨90528347752909882798471649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60352231835273255198981099 90528347752909882798471649)
  ·
    refine ⟨67896260814682412098853737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90528347752909882798471649 67896260814682412098853737)
    ·
      refine ⟨50922195611011809074140303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67896260814682412098853737 50922195611011809074140303)
      ·
        refine ⟨76383293416517713611210455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50922195611011809074140303 76383293416517713611210455)
        ·
          refine ⟨114574940124776570416815683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76383293416517713611210455 114574940124776570416815683)
          ·
            refine ⟨171862410187164855625223525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114574940124776570416815683 171862410187164855625223525)
            ·
              refine ⟨32224201910093410429729411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 171862410187164855625223525 32224201910093410429729411)
              ·
                refine ⟨48336302865140115644594117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32224201910093410429729411 48336302865140115644594117)
                ·
                  refine ⟨9063056787213771683361397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48336302865140115644594117 9063056787213771683361397)
                  ·
                    refine ⟨849661573801291095315131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9063056787213771683361397 849661573801291095315131)
                    ·
                      rfl

theorem cell22_2482065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 5].length) (baseStart_2482065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2482065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2482065 prefixEnd_2482065 := by exact prefixLift 2482065
  have htrace : WordTrace (prefixWord ++ tailWord_2482065) baseStart_2482065 baseEnd_2482065 := by
    simpa [prefixWord, tailWord_2482065, baseEnd_2482065] using wordTrace_append hprefix tailTrace_2482065
  have hstable : (prefixWord ++ tailWord_2482065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2482065).length < 2 ^ (prefixWord ++ tailWord_2482065).sum := by decide
  have hdescent : baseEnd_2482065 < baseStart_2482065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2482065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2482080 : List Nat := [2, 1, 1, 4, 1, 1, 1, 1, 2, 8]
def baseStart_2482080 : Nat := 118140960795 + 2482080 * 2 ^ 59
def prefixEnd_2482080 : Nat := 4983230072969 + 3 ^ 40 * 2482080 * 2
def baseEnd_2482080 : Nat := 849666708607836056190085

theorem tailTrace_2482080 : CollatzResearch.WordTrace tailWord_2482080 prefixEnd_2482080 849666708607836056190085 := by
  unfold tailWord_2482080
  simp only [CollatzResearch.WordTrace]
  refine ⟨45264447423927770180133847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60352596565237026906845129 45264447423927770180133847)
  ·
    refine ⟨67896671135891655270200771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45264447423927770180133847 67896671135891655270200771)
    ·
      refine ⟨101845006703837482905301157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67896671135891655270200771 101845006703837482905301157)
      ·
        refine ⟨19095938756969528044743967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 101845006703837482905301157 19095938756969528044743967)
        ·
          refine ⟨28643908135454292067115951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19095938756969528044743967 28643908135454292067115951)
          ·
            refine ⟨42965862203181438100673927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28643908135454292067115951 42965862203181438100673927)
            ·
              refine ⟨64448793304772157151010891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42965862203181438100673927 64448793304772157151010891)
              ·
                refine ⟨96673189957158235726516337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64448793304772157151010891 96673189957158235726516337)
                ·
                  refine ⟨72504892467868676794887253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 96673189957158235726516337 72504892467868676794887253)
                  ·
                    refine ⟨849666708607836056190085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 72504892467868676794887253 849666708607836056190085)
                    ·
                      rfl

theorem cell22_2482080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 2, 8].length) (baseStart_2482080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2482080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2482080 prefixEnd_2482080 := by exact prefixLift 2482080
  have htrace : WordTrace (prefixWord ++ tailWord_2482080) baseStart_2482080 baseEnd_2482080 := by
    simpa [prefixWord, tailWord_2482080, baseEnd_2482080] using wordTrace_append hprefix tailTrace_2482080
  have hstable : (prefixWord ++ tailWord_2482080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2482080).length < 2 ^ (prefixWord ++ tailWord_2482080).sum := by decide
  have hdescent : baseEnd_2482080 < baseStart_2482080 := by decide
  rcases family_descends (prefixWord ++ tailWord_2482080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2482084 : List Nat := [2, 3, 1, 2, 1, 3, 4, 1, 5]
def baseStart_2482084 : Nat := 118140960795 + 2482084 * 2 ^ 59
def prefixEnd_2482084 : Nat := 4983230072969 + 3 ^ 40 * 2482084 * 2
def baseEnd_2482084 : Nat := 283222692629860459696691

theorem tailTrace_2482084 : CollatzResearch.WordTrace tailWord_2482084 prefixEnd_2482084 283222692629860459696691 := by
  unfold tailWord_2482084
  simp only [CollatzResearch.WordTrace]
  refine ⟨45264520369920524521706653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60352693826560699362275537 45264520369920524521706653)
  ·
    refine ⟨16974195138720196695639995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45264520369920524521706653 16974195138720196695639995)
    ·
      refine ⟨25461292708080295043459993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16974195138720196695639995 25461292708080295043459993)
      ·
        refine ⟨19095969531060221282594995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25461292708080295043459993 19095969531060221282594995)
        ·
          refine ⟨28643954296590331923892493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19095969531060221282594995 28643954296590331923892493)
          ·
            refine ⟨10741482861221374471459685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28643954296590331923892493 10741482861221374471459685)
            ·
              refine ⟨2014028036479007713398691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10741482861221374471459685 2014028036479007713398691)
              ·
                refine ⟨3021042054718511570098037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2014028036479007713398691 3021042054718511570098037)
                ·
                  refine ⟨283222692629860459696691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3021042054718511570098037 283222692629860459696691)
                  ·
                    rfl

theorem cell22_2482084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 4, 1, 5].length) (baseStart_2482084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2482084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2482084 prefixEnd_2482084 := by exact prefixLift 2482084
  have htrace : WordTrace (prefixWord ++ tailWord_2482084) baseStart_2482084 baseEnd_2482084 := by
    simpa [prefixWord, tailWord_2482084, baseEnd_2482084] using wordTrace_append hprefix tailTrace_2482084
  have hstable : (prefixWord ++ tailWord_2482084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2482084).length < 2 ^ (prefixWord ++ tailWord_2482084).sum := by decide
  have hdescent : baseEnd_2482084 < baseStart_2482084 := by decide
  rcases family_descends (prefixWord ++ tailWord_2482084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2482095 : List Nat := [1, 1, 2, 1, 2, 2, 4, 1, 8]
def baseStart_2482095 : Nat := 118140960795 + 2482095 * 2 ^ 59
def prefixEnd_2482095 : Nat := 4983230072969 + 3 ^ 40 * 2482095 * 2
def baseEnd_2482095 : Nat := 283223947804793672355013

theorem tailTrace_2482095 : CollatzResearch.WordTrace tailWord_2482095 prefixEnd_2482095 283223947804793672355013 := by
  unfold tailWord_2482095
  simp only [CollatzResearch.WordTrace]
  refine ⟨90529441942801197922063739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60352961295200798614709159 90529441942801197922063739)
  ·
    refine ⟨135794162914201796883095609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90529441942801197922063739 135794162914201796883095609)
    ·
      refine ⟨101845622185651347662321707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135794162914201796883095609 101845622185651347662321707)
      ·
        refine ⟨152768433278477021493482561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101845622185651347662321707 152768433278477021493482561)
        ·
          refine ⟨114576324958857766120111921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152768433278477021493482561 114576324958857766120111921)
          ·
            refine ⟨85932243719143324590083941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114576324958857766120111921 85932243719143324590083941)
            ·
              refine ⟨16112295697339373360640739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 85932243719143324590083941 16112295697339373360640739)
              ·
                refine ⟨24168443546009060040961109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16112295697339373360640739 24168443546009060040961109)
                ·
                  refine ⟨283223947804793672355013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24168443546009060040961109 283223947804793672355013)
                  ·
                    rfl

theorem cell22_2482095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 1, 8].length) (baseStart_2482095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2482095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2482095 prefixEnd_2482095 := by exact prefixLift 2482095
  have htrace : WordTrace (prefixWord ++ tailWord_2482095) baseStart_2482095 baseEnd_2482095 := by
    simpa [prefixWord, tailWord_2482095, baseEnd_2482095] using wordTrace_append hprefix tailTrace_2482095
  have hstable : (prefixWord ++ tailWord_2482095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2482095).length < 2 ^ (prefixWord ++ tailWord_2482095).sum := by decide
  have hdescent : baseEnd_2482095 < baseStart_2482095 := by decide
  rcases family_descends (prefixWord ++ tailWord_2482095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2482146 : List Nat := [3, 3, 3, 1, 2, 1, 1, 2, 6]
def baseStart_2482146 : Nat := 118140960795 + 2482146 * 2 ^ 59
def prefixEnd_2482146 : Nat := 4983230072969 + 3 ^ 40 * 2482146 * 2
def baseEnd_2482146 : Nat := 283229767252211294679961

theorem tailTrace_2482146 : CollatzResearch.WordTrace tailWord_2482146 prefixEnd_2482146 283229767252211294679961 := by
  unfold tailWord_2482146
  simp only [CollatzResearch.WordTrace]
  refine ⟨22632825516404108408042573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60354201377077622421446861 22632825516404108408042573)
  ·
    refine ⟨8487309568651540653015965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22632825516404108408042573 8487309568651540653015965)
    ·
      refine ⟨3182741088244327744880987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8487309568651540653015965 3182741088244327744880987)
      ·
        refine ⟨4774111632366491617321481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3182741088244327744880987 4774111632366491617321481)
        ·
          refine ⟨3580583724274868712991111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4774111632366491617321481 3580583724274868712991111)
          ·
            refine ⟨5370875586412303069486667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3580583724274868712991111 5370875586412303069486667)
            ·
              refine ⟨8056313379618454604230001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5370875586412303069486667 8056313379618454604230001)
              ·
                refine ⟨6042235034713840953172501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8056313379618454604230001 6042235034713840953172501)
                ·
                  refine ⟨283229767252211294679961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6042235034713840953172501 283229767252211294679961)
                  ·
                    rfl

theorem cell22_2482146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 2, 6].length) (baseStart_2482146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2482146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2482146 prefixEnd_2482146 := by exact prefixLift 2482146
  have htrace : WordTrace (prefixWord ++ tailWord_2482146) baseStart_2482146 baseEnd_2482146 := by
    simpa [prefixWord, tailWord_2482146, baseEnd_2482146] using wordTrace_append hprefix tailTrace_2482146
  have hstable : (prefixWord ++ tailWord_2482146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2482146).length < 2 ^ (prefixWord ++ tailWord_2482146).sum := by decide
  have hdescent : baseEnd_2482146 < baseStart_2482146 := by decide
  rcases family_descends (prefixWord ++ tailWord_2482146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2482174 : List Nat := [4, 2, 2, 2, 1, 2, 9]
def baseStart_2482174 : Nat := 118140960795 + 2482174 * 2 ^ 59
def prefixEnd_2482174 : Nat := 4983230072969 + 3 ^ 40 * 2482174 * 2
def baseEnd_2482174 : Nat := 31470329138105597938511

theorem tailTrace_2482174 : CollatzResearch.WordTrace tailWord_2482174 prefixEnd_2482174 31470329138105597938511 := by
  unfold tailWord_2482174
  simp only [CollatzResearch.WordTrace]
  refine ⟨11316540413689374301773697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60354882206343329609459717 11316540413689374301773697)
  ·
    refine ⟨8487405310267030726330273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11316540413689374301773697 8487405310267030726330273)
    ·
      refine ⟨6365553982700273044747705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8487405310267030726330273 6365553982700273044747705)
      ·
        refine ⟨4774165487025204783560779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6365553982700273044747705 4774165487025204783560779)
        ·
          refine ⟨7161248230537807175341169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4774165487025204783560779 7161248230537807175341169)
          ·
            refine ⟨5370936172903355381505877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7161248230537807175341169 5370936172903355381505877)
            ·
              refine ⟨31470329138105597938511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5370936172903355381505877 31470329138105597938511)
              ·
                rfl

theorem cell22_2482174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 9].length) (baseStart_2482174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2482174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2482174 prefixEnd_2482174 := by exact prefixLift 2482174
  have htrace : WordTrace (prefixWord ++ tailWord_2482174) baseStart_2482174 baseEnd_2482174 := by
    simpa [prefixWord, tailWord_2482174, baseEnd_2482174] using wordTrace_append hprefix tailTrace_2482174
  have hstable : (prefixWord ++ tailWord_2482174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2482174).length < 2 ^ (prefixWord ++ tailWord_2482174).sum := by decide
  have hdescent : baseEnd_2482174 < baseStart_2482174 := by decide
  rcases family_descends (prefixWord ++ tailWord_2482174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2482279 : List Nat := [1, 1, 5, 1, 1, 2, 3, 2, 1, 5]
def baseStart_2482279 : Nat := 118140960795 + 2482279 * 2 ^ 59
def prefixEnd_2482279 : Nat := 4983230072969 + 3 ^ 40 * 2482279 * 2
def baseEnd_2482279 : Nat := 849734830374665870464475

theorem tailTrace_2482279 : CollatzResearch.WordTrace tailWord_2482279 prefixEnd_2482279 849734830374665870464475 := by
  unfold tailWord_2482279
  simp only [CollatzResearch.WordTrace]
  refine ⟨90536152974134597346761891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60357435316089731564507927 90536152974134597346761891)
  ·
    refine ⟨135804229461201896020142837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90536152974134597346761891 135804229461201896020142837)
    ·
      refine ⟨12731646511987677751888391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 135804229461201896020142837 12731646511987677751888391)
      ·
        refine ⟨19097469767981516627832587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12731646511987677751888391 19097469767981516627832587)
        ·
          refine ⟨28646204651972274941748881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19097469767981516627832587 28646204651972274941748881)
          ·
            refine ⟨21484653488979206206311661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28646204651972274941748881 21484653488979206206311661)
            ·
              refine ⟨8056745058367202327366873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21484653488979206206311661 8056745058367202327366873)
              ·
                refine ⟨6042558793775401745525155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8056745058367202327366873 6042558793775401745525155)
                ·
                  refine ⟨9063838190663102618287733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6042558793775401745525155 9063838190663102618287733)
                  ·
                    refine ⟨849734830374665870464475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9063838190663102618287733 849734830374665870464475)
                    ·
                      rfl

theorem cell22_2482279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 2, 1, 5].length) (baseStart_2482279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2482279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2482279 prefixEnd_2482279 := by exact prefixLift 2482279
  have htrace : WordTrace (prefixWord ++ tailWord_2482279) baseStart_2482279 baseEnd_2482279 := by
    simpa [prefixWord, tailWord_2482279, baseEnd_2482279] using wordTrace_append hprefix tailTrace_2482279
  have hstable : (prefixWord ++ tailWord_2482279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2482279).length < 2 ^ (prefixWord ++ tailWord_2482279).sum := by decide
  have hdescent : baseEnd_2482279 < baseStart_2482279 := by decide
  rcases family_descends (prefixWord ++ tailWord_2482279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2482309 : List Nat := [1, 3, 1, 1, 5, 1, 3, 7]
def baseStart_2482309 : Nat := 118140960795 + 2482309 * 2 ^ 59
def prefixEnd_2482309 : Nat := 4983230072969 + 3 ^ 40 * 2482309 * 2
def baseEnd_2482309 : Nat := 94416122220861754690487

theorem tailTrace_2482309 : CollatzResearch.WordTrace tailWord_2482309 prefixEnd_2482309 94416122220861754690487 := by
  unfold tailWord_2482309
  simp only [CollatzResearch.WordTrace]
  refine ⟨90537247164025912470353981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60358164776017274980235987 90537247164025912470353981)
  ·
    refine ⟨33951467686509717176382743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90537247164025912470353981 33951467686509717176382743)
    ·
      refine ⟨50927201529764575764574115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33951467686509717176382743 50927201529764575764574115)
      ·
        refine ⟨76390802294646863646861173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50927201529764575764574115 76390802294646863646861173)
        ·
          refine ⟨7161637715123143466893235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 76390802294646863646861173 7161637715123143466893235)
          ·
            refine ⟨10742456572684715200339853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7161637715123143466893235 10742456572684715200339853)
            ·
              refine ⟨4028421214756768200127445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10742456572684715200339853 4028421214756768200127445)
              ·
                refine ⟨94416122220861754690487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4028421214756768200127445 94416122220861754690487)
                ·
                  rfl

theorem cell22_2482309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 7].length) (baseStart_2482309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2482309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2482309 prefixEnd_2482309 := by exact prefixLift 2482309
  have htrace : WordTrace (prefixWord ++ tailWord_2482309) baseStart_2482309 baseEnd_2482309 := by
    simpa [prefixWord, tailWord_2482309, baseEnd_2482309] using wordTrace_append hprefix tailTrace_2482309
  have hstable : (prefixWord ++ tailWord_2482309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2482309).length < 2 ^ (prefixWord ++ tailWord_2482309).sum := by decide
  have hdescent : baseEnd_2482309 < baseStart_2482309 := by decide
  rcases family_descends (prefixWord ++ tailWord_2482309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2482328 : List Nat := [2, 1, 2, 4, 3, 2, 1, 1, 2, 4]
def baseStart_2482328 : Nat := 118140960795 + 2482328 * 2 ^ 59
def prefixEnd_2482328 : Nat := 4983230072969 + 3 ^ 40 * 2482328 * 2
def baseEnd_2482328 : Nat := 849751604076046075989325

theorem tailTrace_2482328 : CollatzResearch.WordTrace tailWord_2482328 prefixEnd_2482328 849751604076046075989325 := by
  unfold tailWord_2482328
  simp only [CollatzResearch.WordTrace]
  refine ⟨45268970075478539357647819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60358626767304719143530425 45268970075478539357647819)
  ·
    refine ⟨67903455113217809036471729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45268970075478539357647819 67903455113217809036471729)
    ·
      refine ⟨50927591334913356777353797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67903455113217809036471729 50927591334913356777353797)
      ·
        refine ⟨9548923375296254395753837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50927591334913356777353797 9548923375296254395753837)
        ·
          refine ⟨3580846265736095398407689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9548923375296254395753837 3580846265736095398407689)
          ·
            refine ⟨2685634699302071548805767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3580846265736095398407689 2685634699302071548805767)
            ·
              refine ⟨4028452048953107323208651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2685634699302071548805767 4028452048953107323208651)
              ·
                refine ⟨6042678073429660984812977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4028452048953107323208651 6042678073429660984812977)
                ·
                  refine ⟨4532008555072245738609733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6042678073429660984812977 4532008555072245738609733)
                  ·
                    refine ⟨849751604076046075989325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4532008555072245738609733 849751604076046075989325)
                    ·
                      rfl

theorem cell22_2482328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 1, 2, 4].length) (baseStart_2482328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2482328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2482328 prefixEnd_2482328 := by exact prefixLift 2482328
  have htrace : WordTrace (prefixWord ++ tailWord_2482328) baseStart_2482328 baseEnd_2482328 := by
    simpa [prefixWord, tailWord_2482328, baseEnd_2482328] using wordTrace_append hprefix tailTrace_2482328
  have hstable : (prefixWord ++ tailWord_2482328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2482328).length < 2 ^ (prefixWord ++ tailWord_2482328).sum := by decide
  have hdescent : baseEnd_2482328 < baseStart_2482328 := by decide
  rcases family_descends (prefixWord ++ tailWord_2482328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2482354 : List Nat := [3, 2, 1, 1, 1, 3, 3, 1, 7]
def baseStart_2482354 : Nat := 118140960795 + 2482354 * 2 ^ 59
def prefixEnd_2482354 : Nat := 4983230072969 + 3 ^ 40 * 2482354 * 2
def baseEnd_2482354 : Nat := 283253501469130224946415

theorem tailTrace_2482354 : CollatzResearch.WordTrace tailWord_2482354 prefixEnd_2482354 283253501469130224946415 := by
  unfold tailWord_2482354
  simp only [CollatzResearch.WordTrace]
  refine ⟨22634722112215721288935529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60359258965908590103828077 22634722112215721288935529)
  ·
    refine ⟨16976041584161790966701647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22634722112215721288935529 16976041584161790966701647)
    ·
      refine ⟨25464062376242686450052471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16976041584161790966701647 25464062376242686450052471)
      ·
        refine ⟨38196093564364029675078707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25464062376242686450052471 38196093564364029675078707)
        ·
          refine ⟨57294140346546044512618061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38196093564364029675078707 57294140346546044512618061)
          ·
            refine ⟨21485302629954766692231773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57294140346546044512618061 21485302629954766692231773)
            ·
              refine ⟨8056988486233037509586915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21485302629954766692231773 8056988486233037509586915)
              ·
                refine ⟨12085482729349556264380373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8056988486233037509586915 12085482729349556264380373)
                ·
                  refine ⟨283253501469130224946415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12085482729349556264380373 283253501469130224946415)
                  ·
                    rfl

theorem cell22_2482354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 1, 7].length) (baseStart_2482354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2482354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2482354 prefixEnd_2482354 := by exact prefixLift 2482354
  have htrace : WordTrace (prefixWord ++ tailWord_2482354) baseStart_2482354 baseEnd_2482354 := by
    simpa [prefixWord, tailWord_2482354, baseEnd_2482354] using wordTrace_append hprefix tailTrace_2482354
  have hstable : (prefixWord ++ tailWord_2482354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2482354).length < 2 ^ (prefixWord ++ tailWord_2482354).sum := by decide
  have hdescent : baseEnd_2482354 < baseStart_2482354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2482354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2482401 : List Nat := [1, 2, 3, 1, 3, 1, 1, 5, 1, 4]
def baseStart_2482401 : Nat := 118140960795 + 2482401 * 2 ^ 59
def prefixEnd_2482401 : Nat := 4983230072969 + 3 ^ 40 * 2482401 * 2
def baseEnd_2482401 : Nat := 849776593467898218914101

theorem tailTrace_2482401 : CollatzResearch.WordTrace tailWord_2482401 prefixEnd_2482401 849776593467898218914101 := by
  unfold tailWord_2482401
  simp only [CollatzResearch.WordTrace]
  refine ⟨90540602679692612182703057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60360401786461741455135371 90540602679692612182703057)
  ·
    refine ⟨67905452009769459137027293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90540602679692612182703057 67905452009769459137027293)
    ·
      refine ⟨25464544503663547176385235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67905452009769459137027293 25464544503663547176385235)
      ·
        refine ⟨38196816755495320764577853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25464544503663547176385235 38196816755495320764577853)
        ·
          refine ⟨14323806283310745286716695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38196816755495320764577853 14323806283310745286716695)
          ·
            refine ⟨21485709424966117930075043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14323806283310745286716695 21485709424966117930075043)
            ·
              refine ⟨32228564137449176895112565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21485709424966117930075043 32228564137449176895112565)
              ·
                refine ⟨3021427887885860333916803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32228564137449176895112565 3021427887885860333916803)
                ·
                  refine ⟨4532141831828790500875205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3021427887885860333916803 4532141831828790500875205)
                  ·
                    refine ⟨849776593467898218914101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4532141831828790500875205 849776593467898218914101)
                    ·
                      rfl

theorem cell22_2482401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 5, 1, 4].length) (baseStart_2482401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2482401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2482401 prefixEnd_2482401 := by exact prefixLift 2482401
  have htrace : WordTrace (prefixWord ++ tailWord_2482401) baseStart_2482401 baseEnd_2482401 := by
    simpa [prefixWord, tailWord_2482401, baseEnd_2482401] using wordTrace_append hprefix tailTrace_2482401
  have hstable : (prefixWord ++ tailWord_2482401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2482401).length < 2 ^ (prefixWord ++ tailWord_2482401).sum := by decide
  have hdescent : baseEnd_2482401 < baseStart_2482401 := by decide
  rcases family_descends (prefixWord ++ tailWord_2482401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2482416 : List Nat := [2, 1, 1, 1, 3, 1, 1, 8, 4]
def baseStart_2482416 : Nat := 118140960795 + 2482416 * 2 ^ 59
def prefixEnd_2482416 : Nat := 4983230072969 + 3 ^ 40 * 2482416 * 2
def baseEnd_2482416 : Nat := 283260576091481059929685

theorem tailTrace_2482416 : CollatzResearch.WordTrace tailWord_2482416 prefixEnd_2482416 283260576091481059929685 := by
  unfold tailWord_2482416
  simp only [CollatzResearch.WordTrace]
  refine ⟨45270574887319134872249551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60360766516425513162999401 45270574887319134872249551)
  ·
    refine ⟨67905862330978702308374327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45270574887319134872249551 67905862330978702308374327)
    ·
      refine ⟨101858793496468053462561491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67905862330978702308374327 101858793496468053462561491)
      ·
        refine ⟨152788190244702080193842237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101858793496468053462561491 152788190244702080193842237)
        ·
          refine ⟨57295571341763280072690839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 152788190244702080193842237 57295571341763280072690839)
          ·
            refine ⟨85943357012644920109036259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57295571341763280072690839 85943357012644920109036259)
            ·
              refine ⟨128915035518967380163554389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85943357012644920109036259 128915035518967380163554389)
              ·
                refine ⟨1510723072487898986291653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 128915035518967380163554389 1510723072487898986291653)
                ·
                  refine ⟨283260576091481059929685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1510723072487898986291653 283260576091481059929685)
                  ·
                    rfl

theorem cell22_2482416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 8, 4].length) (baseStart_2482416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2482416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2482416 prefixEnd_2482416 := by exact prefixLift 2482416
  have htrace : WordTrace (prefixWord ++ tailWord_2482416) baseStart_2482416 baseEnd_2482416 := by
    simpa [prefixWord, tailWord_2482416, baseEnd_2482416] using wordTrace_append hprefix tailTrace_2482416
  have hstable : (prefixWord ++ tailWord_2482416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2482416).length < 2 ^ (prefixWord ++ tailWord_2482416).sum := by decide
  have hdescent : baseEnd_2482416 < baseStart_2482416 := by decide
  rcases family_descends (prefixWord ++ tailWord_2482416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2482429 : List Nat := [1, 4, 1, 1, 1, 1, 1, 3, 3, 6]
def baseStart_2482429 : Nat := 118140960795 + 2482429 * 2 ^ 59
def prefixEnd_2482429 : Nat := 4983230072969 + 3 ^ 40 * 2482429 * 2
def baseEnd_2482429 : Nat := 849786178440115479214015

theorem tailTrace_2482429 : CollatzResearch.WordTrace tailWord_2482429 prefixEnd_2482429 849786178440115479214015 := by
  unfold tailWord_2482429
  simp only [CollatzResearch.WordTrace]
  refine ⟨90541623923591172964722341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60361082615727448643148227 90541623923591172964722341)
  ·
    refine ⟨16976554485673344930885439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90541623923591172964722341 16976554485673344930885439)
    ·
      refine ⟨25464831728510017396328159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16976554485673344930885439 25464831728510017396328159)
      ·
        refine ⟨38197247592765026094492239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25464831728510017396328159 38197247592765026094492239)
        ·
          refine ⟨57295871389147539141738359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38197247592765026094492239 57295871389147539141738359)
          ·
            refine ⟨85943807083721308712607539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57295871389147539141738359 85943807083721308712607539)
            ·
              refine ⟨128915710625581963068911309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85943807083721308712607539 128915710625581963068911309)
              ·
                refine ⟨48343391484593236150841741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 128915710625581963068911309 48343391484593236150841741)
                ·
                  refine ⟨18128771806722463556565653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48343391484593236150841741 18128771806722463556565653)
                  ·
                    refine ⟨849786178440115479214015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18128771806722463556565653 849786178440115479214015)
                    ·
                      rfl

theorem cell22_2482429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 3, 6].length) (baseStart_2482429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2482429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2482429 prefixEnd_2482429 := by exact prefixLift 2482429
  have htrace : WordTrace (prefixWord ++ tailWord_2482429) baseStart_2482429 baseEnd_2482429 := by
    simpa [prefixWord, tailWord_2482429, baseEnd_2482429] using wordTrace_append hprefix tailTrace_2482429
  have hstable : (prefixWord ++ tailWord_2482429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2482429).length < 2 ^ (prefixWord ++ tailWord_2482429).sum := by decide
  have hdescent : baseEnd_2482429 < baseStart_2482429 := by decide
  rcases family_descends (prefixWord ++ tailWord_2482429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2482444 : List Nat := [2, 2, 1, 2, 2, 2, 1, 10]
def baseStart_2482444 : Nat := 118140960795 + 2482444 * 2 ^ 59
def prefixEnd_2482444 : Nat := 4983230072969 + 3 ^ 40 * 2482444 * 2
def baseEnd_2482444 : Nat := 94421257027406715565441

theorem tailTrace_2482444 : CollatzResearch.WordTrace tailWord_2482444 prefixEnd_2482444 94421257027406715565441 := by
  unfold tailWord_2482444
  simp only [CollatzResearch.WordTrace]
  refine ⟨45271085509268415263259193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60361447345691220351012257 45271085509268415263259193)
  ·
    refine ⟨33953314131951311447444395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45271085509268415263259193 33953314131951311447444395)
    ·
      refine ⟨50929971197926967171166593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33953314131951311447444395 50929971197926967171166593)
      ·
        refine ⟨38197478398445225378374945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50929971197926967171166593 38197478398445225378374945)
        ·
          refine ⟨28648108798833919033781209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38197478398445225378374945 28648108798833919033781209)
          ·
            refine ⟨21486081599125439275335907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28648108798833919033781209 21486081599125439275335907)
            ·
              refine ⟨32229122398688158913003861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21486081599125439275335907 32229122398688158913003861)
              ·
                refine ⟨94421257027406715565441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 32229122398688158913003861 94421257027406715565441)
                ·
                  rfl

theorem cell22_2482444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 10].length) (baseStart_2482444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2482444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2482444 prefixEnd_2482444 := by exact prefixLift 2482444
  have htrace : WordTrace (prefixWord ++ tailWord_2482444) baseStart_2482444 baseEnd_2482444 := by
    simpa [prefixWord, tailWord_2482444, baseEnd_2482444] using wordTrace_append hprefix tailTrace_2482444
  have hstable : (prefixWord ++ tailWord_2482444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2482444).length < 2 ^ (prefixWord ++ tailWord_2482444).sum := by decide
  have hdescent : baseEnd_2482444 < baseStart_2482444 := by decide
  rcases family_descends (prefixWord ++ tailWord_2482444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2482461 : List Nat := [1, 4, 2, 3, 2, 10]
def baseStart_2482461 : Nat := 118140960795 + 2482461 * 2 ^ 59
def prefixEnd_2482461 : Nat := 4983230072969 + 3 ^ 40 * 2482461 * 2
def baseEnd_2482461 : Nat := 10491322625852815585357

theorem tailTrace_2482461 : CollatzResearch.WordTrace tailWord_2482461 prefixEnd_2482461 10491322625852815585357 := by
  unfold tailWord_2482461
  simp only [CollatzResearch.WordTrace]
  refine ⟨90542791059475242429887237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60361860706316828286591491 90542791059475242429887237)
  ·
    refine ⟨16976773323651607955603857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90542791059475242429887237 16976773323651607955603857)
    ·
      refine ⟨12732579992738705966702893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16976773323651607955603857 12732579992738705966702893)
      ·
        refine ⟨4774717497277014737513585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12732579992738705966702893 4774717497277014737513585)
        ·
          refine ⟨3581038122957761053135189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4774717497277014737513585 3581038122957761053135189)
          ·
            refine ⟨10491322625852815585357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3581038122957761053135189 10491322625852815585357)
            ·
              rfl

theorem cell22_2482461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 10].length) (baseStart_2482461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2482461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2482461 prefixEnd_2482461 := by exact prefixLift 2482461
  have htrace : WordTrace (prefixWord ++ tailWord_2482461) baseStart_2482461 baseEnd_2482461 := by
    simpa [prefixWord, tailWord_2482461, baseEnd_2482461] using wordTrace_append hprefix tailTrace_2482461
  have hstable : (prefixWord ++ tailWord_2482461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2482461).length < 2 ^ (prefixWord ++ tailWord_2482461).sum := by decide
  have hdescent : baseEnd_2482461 < baseStart_2482461 := by decide
  rcases family_descends (prefixWord ++ tailWord_2482461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2482497 : List Nat := [1, 2, 5, 2, 3, 1, 1, 1, 2, 4]
def baseStart_2482497 : Nat := 118140960795 + 2482497 * 2 ^ 59
def prefixEnd_2482497 : Nat := 4983230072969 + 3 ^ 40 * 2482497 * 2
def baseEnd_2482497 : Nat := 849809456229785968513807

theorem tailTrace_2482497 : CollatzResearch.WordTrace tailWord_2482497 prefixEnd_2482497 849809456229785968513807 := by
  unfold tailWord_2482497
  simp only [CollatzResearch.WordTrace]
  refine ⟨90544104087344820578197745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60362736058229880385465163 90544104087344820578197745)
  ·
    refine ⟨67908078065508615433648309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90544104087344820578197745 67908078065508615433648309)
    ·
      refine ⟨6366382318641432696904529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 67908078065508615433648309 6366382318641432696904529)
      ·
        refine ⟨4774786738981074522678397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6366382318641432696904529 4774786738981074522678397)
        ·
          refine ⟨1790545027117902946004399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4774786738981074522678397 1790545027117902946004399)
          ·
            refine ⟨2685817540676854419006599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1790545027117902946004399 2685817540676854419006599)
            ·
              refine ⟨4028726311015281628509899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2685817540676854419006599 4028726311015281628509899)
              ·
                refine ⟨6043089466522922442764849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4028726311015281628509899 6043089466522922442764849)
                ·
                  refine ⟨4532317099892191832073637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6043089466522922442764849 4532317099892191832073637)
                  ·
                    refine ⟨849809456229785968513807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4532317099892191832073637 849809456229785968513807)
                    ·
                      rfl

theorem cell22_2482497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 1, 2, 4].length) (baseStart_2482497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2482497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2482497 prefixEnd_2482497 := by exact prefixLift 2482497
  have htrace : WordTrace (prefixWord ++ tailWord_2482497) baseStart_2482497 baseEnd_2482497 := by
    simpa [prefixWord, tailWord_2482497, baseEnd_2482497] using wordTrace_append hprefix tailTrace_2482497
  have hstable : (prefixWord ++ tailWord_2482497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2482497).length < 2 ^ (prefixWord ++ tailWord_2482497).sum := by decide
  have hdescent : baseEnd_2482497 < baseStart_2482497 := by decide
  rcases family_descends (prefixWord ++ tailWord_2482497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2482538 : List Nat := [3, 1, 3, 3, 1, 1, 2, 1, 2, 5]
def baseStart_2482538 : Nat := 118140960795 + 2482538 * 2 ^ 59
def prefixEnd_2482538 : Nat := 4983230072969 + 3 ^ 40 * 2482538 * 2
def baseEnd_2482538 : Nat := 849823491367675528238681

theorem tailTrace_2482538 : CollatzResearch.WordTrace tailWord_2482538 prefixEnd_2482538 849823491367675528238681 := by
  unfold tailWord_2482538
  simp only [CollatzResearch.WordTrace]
  refine ⟨22636399870049071145110067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60363732986797523053626845 22636399870049071145110067)
  ·
    refine ⟨33954599805073606717665101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22636399870049071145110067 33954599805073606717665101)
    ·
      refine ⟨12732974926902602519124413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33954599805073606717665101 12732974926902602519124413)
      ·
        refine ⟨4774865597588475944671655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12732974926902602519124413 4774865597588475944671655)
        ·
          refine ⟨7162298396382713917007483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4774865597588475944671655 7162298396382713917007483)
          ·
            refine ⟨10743447594574070875511225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7162298396382713917007483 10743447594574070875511225)
            ·
              refine ⟨8057585695930553156633419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10743447594574070875511225 8057585695930553156633419)
              ·
                refine ⟨12086378543895829734950129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8057585695930553156633419 12086378543895829734950129)
                ·
                  refine ⟨9064783907921872301212597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12086378543895829734950129 9064783907921872301212597)
                  ·
                    refine ⟨849823491367675528238681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9064783907921872301212597 849823491367675528238681)
                    ·
                      rfl

theorem cell22_2482538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 1, 2, 5].length) (baseStart_2482538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2482538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2482538 prefixEnd_2482538 := by exact prefixLift 2482538
  have htrace : WordTrace (prefixWord ++ tailWord_2482538) baseStart_2482538 baseEnd_2482538 := by
    simpa [prefixWord, tailWord_2482538, baseEnd_2482538] using wordTrace_append hprefix tailTrace_2482538
  have hstable : (prefixWord ++ tailWord_2482538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2482538).length < 2 ^ (prefixWord ++ tailWord_2482538).sum := by decide
  have hdescent : baseEnd_2482538 < baseStart_2482538 := by decide
  rcases family_descends (prefixWord ++ tailWord_2482538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2482540 : List Nat := [2, 2, 1, 1, 6, 1, 3, 1, 5]
def baseStart_2482540 : Nat := 118140960795 + 2482540 * 2 ^ 59
def prefixEnd_2482540 : Nat := 4983230072969 + 3 ^ 40 * 2482540 * 2
def baseEnd_2482540 : Nat := 283274725336182729896225

theorem tailTrace_2482540 : CollatzResearch.WordTrace tailWord_2482540 prefixEnd_2482540 283274725336182729896225 := by
  unfold tailWord_2482540
  simp only [CollatzResearch.WordTrace]
  refine ⟨45272836213094519461006537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60363781617459359281342049 45272836213094519461006537)
  ·
    refine ⟨33954627159820889595754903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45272836213094519461006537 33954627159820889595754903)
    ·
      refine ⟨50931940739731334393632355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33954627159820889595754903 50931940739731334393632355)
      ·
        refine ⟨76397911109597001590448533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50931940739731334393632355 76397911109597001590448533)
        ·
          refine ⟨3581152083262359449552275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 76397911109597001590448533 3581152083262359449552275)
          ·
            refine ⟨5371728124893539174328413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3581152083262359449552275 5371728124893539174328413)
            ·
              refine ⟨2014398046835077190373155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5371728124893539174328413 2014398046835077190373155)
              ·
                refine ⟨3021597070252615785559733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2014398046835077190373155 3021597070252615785559733)
                ·
                  refine ⟨283274725336182729896225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3021597070252615785559733 283274725336182729896225)
                  ·
                    rfl

theorem cell22_2482540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 5].length) (baseStart_2482540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2482540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2482540 prefixEnd_2482540 := by exact prefixLift 2482540
  have htrace : WordTrace (prefixWord ++ tailWord_2482540) baseStart_2482540 baseEnd_2482540 := by
    simpa [prefixWord, tailWord_2482540, baseEnd_2482540] using wordTrace_append hprefix tailTrace_2482540
  have hstable : (prefixWord ++ tailWord_2482540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2482540).length < 2 ^ (prefixWord ++ tailWord_2482540).sum := by decide
  have hdescent : baseEnd_2482540 < baseStart_2482540 := by decide
  rcases family_descends (prefixWord ++ tailWord_2482540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2482583 : List Nat := [1, 1, 3, 3, 1, 1, 4, 1, 4, 3]
def baseStart_2482583 : Nat := 118140960795 + 2482583 * 2 ^ 59
def prefixEnd_2482583 : Nat := 4983230072969 + 3 ^ 40 * 2482583 * 2
def baseEnd_2482583 : Nat := 849838895787310410863543

theorem tailTrace_2482583 : CollatzResearch.WordTrace tailWord_2482583 prefixEnd_2482583 849838895787310410863543 := by
  unfold tailWord_2482583
  simp only [CollatzResearch.WordTrace]
  refine ⟨90547240765033257265828403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60364827176688838177218935 90547240765033257265828403)
  ·
    refine ⟨135820861147549885898742605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90547240765033257265828403 135820861147549885898742605)
    ·
      refine ⟨50932822930331207212028477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135820861147549885898742605 50932822930331207212028477)
      ·
        refine ⟨19099808598874202704510679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50932822930331207212028477 19099808598874202704510679)
        ·
          refine ⟨28649712898311304056766019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19099808598874202704510679 28649712898311304056766019)
          ·
            refine ⟨42974569347466956085149029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28649712898311304056766019 42974569347466956085149029)
            ·
              refine ⟨8057731752650054265965443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42974569347466956085149029 8057731752650054265965443)
              ·
                refine ⟨12086597628975081398948165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8057731752650054265965443 12086597628975081398948165)
                ·
                  refine ⟨2266237055432827762302781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12086597628975081398948165 2266237055432827762302781)
                  ·
                    refine ⟨849838895787310410863543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2266237055432827762302781 849838895787310410863543)
                    ·
                      rfl

theorem cell22_2482583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 1, 4, 3].length) (baseStart_2482583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2482583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2482583 prefixEnd_2482583 := by exact prefixLift 2482583
  have htrace : WordTrace (prefixWord ++ tailWord_2482583) baseStart_2482583 baseEnd_2482583 := by
    simpa [prefixWord, tailWord_2482583, baseEnd_2482583] using wordTrace_append hprefix tailTrace_2482583
  have hstable : (prefixWord ++ tailWord_2482583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2482583).length < 2 ^ (prefixWord ++ tailWord_2482583).sum := by decide
  have hdescent : baseEnd_2482583 < baseStart_2482583 := by decide
  rcases family_descends (prefixWord ++ tailWord_2482583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2482585 : List Nat := [1, 2, 1, 2, 1, 4, 5, 2, 4]
def baseStart_2482585 : Nat := 118140960795 + 2482585 * 2 ^ 59
def prefixEnd_2482585 : Nat := 4983230072969 + 3 ^ 40 * 2482585 * 2
def baseEnd_2482585 : Nat := 283279860142727690771179

theorem tailTrace_2482585 : CollatzResearch.WordTrace tailWord_2482585 prefixEnd_2482585 283279860142727690771179 := by
  unfold tailWord_2482585
  simp only [CollatzResearch.WordTrace]
  refine ⟨90547313711026011607401209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60364875807350674404934139 90547313711026011607401209)
  ·
    refine ⟨67910485283269508705550907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90547313711026011607401209 67910485283269508705550907)
    ·
      refine ⟨101865727924904263058326361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67910485283269508705550907 101865727924904263058326361)
      ·
        refine ⟨76399295943678197293744771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101865727924904263058326361 76399295943678197293744771)
        ·
          refine ⟨114598943915517295940617157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76399295943678197293744771 114598943915517295940617157)
          ·
            refine ⟨21487301984159492988865717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 114598943915517295940617157 21487301984159492988865717)
            ·
              refine ⟨2014434561014952467706161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21487301984159492988865717 2014434561014952467706161)
              ·
                refine ⟨1510825920761214350779621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2014434561014952467706161 1510825920761214350779621)
                ·
                  refine ⟨283279860142727690771179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1510825920761214350779621 283279860142727690771179)
                  ·
                    rfl

theorem cell22_2482585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 5, 2, 4].length) (baseStart_2482585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2482585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2482585 prefixEnd_2482585 := by exact prefixLift 2482585
  have htrace : WordTrace (prefixWord ++ tailWord_2482585) baseStart_2482585 baseEnd_2482585 := by
    simpa [prefixWord, tailWord_2482585, baseEnd_2482585] using wordTrace_append hprefix tailTrace_2482585
  have hstable : (prefixWord ++ tailWord_2482585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2482585).length < 2 ^ (prefixWord ++ tailWord_2482585).sum := by decide
  have hdescent : baseEnd_2482585 < baseStart_2482585 := by decide
  rcases family_descends (prefixWord ++ tailWord_2482585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2482596 : List Nat := [2, 3, 1, 2, 1, 1, 3, 9]
def baseStart_2482596 : Nat := 118140960795 + 2482596 * 2 ^ 59
def prefixEnd_2482596 : Nat := 4983230072969 + 3 ^ 40 * 2482596 * 2
def baseEnd_2482596 : Nat := 94427038439220301143167

theorem tailTrace_2482596 : CollatzResearch.WordTrace tailWord_2482596 prefixEnd_2482596 94427038439220301143167 := by
  unfold tailWord_2482596
  simp only [CollatzResearch.WordTrace]
  refine ⟨45273857456993080243025821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60365143275990773657367761 45273857456993080243025821)
  ·
    refine ⟨16977696546372405091134683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45273857456993080243025821 16977696546372405091134683)
    ·
      refine ⟨25466544819558607636702025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16977696546372405091134683 25466544819558607636702025)
      ·
        refine ⟨19099908614668955727526519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25466544819558607636702025 19099908614668955727526519)
        ·
          refine ⟨28649862922003433591289779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19099908614668955727526519 28649862922003433591289779)
          ·
            refine ⟨42974794383005150386934669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28649862922003433591289779 42974794383005150386934669)
            ·
              refine ⟨16115547893626931395100501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42974794383005150386934669 16115547893626931395100501)
              ·
                refine ⟨94427038439220301143167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16115547893626931395100501 94427038439220301143167)
                ·
                  rfl

theorem cell22_2482596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 9].length) (baseStart_2482596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2482596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2482596 prefixEnd_2482596 := by exact prefixLift 2482596
  have htrace : WordTrace (prefixWord ++ tailWord_2482596) baseStart_2482596 baseEnd_2482596 := by
    simpa [prefixWord, tailWord_2482596, baseEnd_2482596] using wordTrace_append hprefix tailTrace_2482596
  have hstable : (prefixWord ++ tailWord_2482596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2482596).length < 2 ^ (prefixWord ++ tailWord_2482596).sum := by decide
  have hdescent : baseEnd_2482596 < baseStart_2482596 := by decide
  rcases family_descends (prefixWord ++ tailWord_2482596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2482641 : List Nat := [1, 2, 2, 1, 2, 1, 1, 5, 7]
def baseStart_2482641 : Nat := 118140960795 + 2482641 * 2 ^ 59
def prefixEnd_2482641 : Nat := 4983230072969 + 3 ^ 40 * 2482641 * 2
def baseEnd_2482641 : Nat := 283286250124205864304455

theorem tailTrace_2482641 : CollatzResearch.WordTrace tailWord_2482641 prefixEnd_2482641 283286250124205864304455 := by
  unfold tailWord_2482641
  simp only [CollatzResearch.WordTrace]
  refine ⟨90549356198823133171439777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60366237465882088780959851 90549356198823133171439777)
  ·
    refine ⟨67912017149117349878579833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90549356198823133171439777 67912017149117349878579833)
    ·
      refine ⟨50934012861838012408934875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67912017149117349878579833 50934012861838012408934875)
      ·
        refine ⟨76401019292757018613402313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50934012861838012408934875 76401019292757018613402313)
        ·
          refine ⟨57300764469567763960051735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76401019292757018613402313 57300764469567763960051735)
          ·
            refine ⟨85951146704351645940077603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57300764469567763960051735 85951146704351645940077603)
            ·
              refine ⟨128926720056527468910116405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85951146704351645940077603 128926720056527468910116405)
              ·
                refine ⟨12086880005299450210323413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 128926720056527468910116405 12086880005299450210323413)
                ·
                  refine ⟨283286250124205864304455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12086880005299450210323413 283286250124205864304455)
                  ·
                    rfl

theorem cell22_2482641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 5, 7].length) (baseStart_2482641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2482641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2482641 prefixEnd_2482641 := by exact prefixLift 2482641
  have htrace : WordTrace (prefixWord ++ tailWord_2482641) baseStart_2482641 baseEnd_2482641 := by
    simpa [prefixWord, tailWord_2482641, baseEnd_2482641] using wordTrace_append hprefix tailTrace_2482641
  have hstable : (prefixWord ++ tailWord_2482641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2482641).length < 2 ^ (prefixWord ++ tailWord_2482641).sum := by decide
  have hdescent : baseEnd_2482641 < baseStart_2482641 := by decide
  rcases family_descends (prefixWord ++ tailWord_2482641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2482692 : List Nat := [2, 3, 2, 3, 1, 3, 1, 2, 5]
def baseStart_2482692 : Nat := 118140960795 + 2482692 * 2 ^ 59
def prefixEnd_2482692 : Nat := 4983230072969 + 3 ^ 40 * 2482692 * 2
def baseEnd_2482692 : Nat := 283292069571623486629403

theorem tailTrace_2482692 : CollatzResearch.WordTrace tailWord_2482692 prefixEnd_2482692 283292069571623486629403 := by
  unfold tailWord_2482692
  simp only [CollatzResearch.WordTrace]
  refine ⟨45275608160819184440773165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60367477547758912587697553 45275608160819184440773165)
  ·
    refine ⟨16978353060307194165289937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45275608160819184440773165 16978353060307194165289937)
    ·
      refine ⟨12733764795230395623967453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16978353060307194165289937 12733764795230395623967453)
      ·
        refine ⟨4775161798211398358987795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12733764795230395623967453 4775161798211398358987795)
        ·
          refine ⟨7162742697317097538481693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4775161798211398358987795 7162742697317097538481693)
          ·
            refine ⟨2686028511493911576930635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7162742697317097538481693 2686028511493911576930635)
            ·
              refine ⟨4029042767240867365395953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2686028511493911576930635 4029042767240867365395953)
              ·
                refine ⟨3021782075430650524046965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4029042767240867365395953 3021782075430650524046965)
                ·
                  refine ⟨283292069571623486629403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3021782075430650524046965 283292069571623486629403)
                  ·
                    rfl

theorem cell22_2482692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 2, 5].length) (baseStart_2482692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2482692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2482692 prefixEnd_2482692 := by exact prefixLift 2482692
  have htrace : WordTrace (prefixWord ++ tailWord_2482692) baseStart_2482692 baseEnd_2482692 := by
    simpa [prefixWord, tailWord_2482692, baseEnd_2482692] using wordTrace_append hprefix tailTrace_2482692
  have hstable : (prefixWord ++ tailWord_2482692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2482692).length < 2 ^ (prefixWord ++ tailWord_2482692).sum := by decide
  have hdescent : baseEnd_2482692 < baseStart_2482692 := by decide
  rcases family_descends (prefixWord ++ tailWord_2482692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2482748 : List Nat := [2, 2, 2, 2, 3, 1, 10]
def baseStart_2482748 : Nat := 118140960795 + 2482748 * 2 ^ 59
def prefixEnd_2482748 : Nat := 4983230072969 + 3 ^ 40 * 2482748 * 2
def baseEnd_2482748 : Nat := 31477606617011295573631

theorem tailTrace_2482748 : CollatzResearch.WordTrace tailWord_2482748 prefixEnd_2482748 31477606617011295573631 := by
  unfold tailWord_2482748
  simp only [CollatzResearch.WordTrace]
  refine ⟨45276629404717745222792449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60368839206290326963723265 45276629404717745222792449)
  ·
    refine ⟨33957472053538308917094337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45276629404717745222792449 33957472053538308917094337)
    ·
      refine ⟨25468104040153731687820753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33957472053538308917094337 25468104040153731687820753)
      ·
        refine ⟨19101078030115298765865565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25468104040153731687820753 19101078030115298765865565)
        ·
          refine ⟨7162904261293237037199587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19101078030115298765865565 7162904261293237037199587)
          ·
            refine ⟨10744356391939855555799381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7162904261293237037199587 10744356391939855555799381)
            ·
              refine ⟨31477606617011295573631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 10744356391939855555799381 31477606617011295573631)
              ·
                rfl

theorem cell22_2482748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 10].length) (baseStart_2482748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2482748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2482748 prefixEnd_2482748 := by exact prefixLift 2482748
  have htrace : WordTrace (prefixWord ++ tailWord_2482748) baseStart_2482748 baseEnd_2482748 := by
    simpa [prefixWord, tailWord_2482748, baseEnd_2482748] using wordTrace_append hprefix tailTrace_2482748
  have hstable : (prefixWord ++ tailWord_2482748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2482748).length < 2 ^ (prefixWord ++ tailWord_2482748).sum := by decide
  have hdescent : baseEnd_2482748 < baseStart_2482748 := by decide
  rcases family_descends (prefixWord ++ tailWord_2482748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2482765 : List Nat := [1, 6, 1, 1, 2, 1, 1, 9]
def baseStart_2482765 : Nat := 118140960795 + 2482765 * 2 ^ 59
def prefixEnd_2482765 : Nat := 4983230072969 + 3 ^ 40 * 2482765 * 2
def baseEnd_2482765 : Nat := 94433466456302511423665

theorem tailTrace_2482765 : CollatzResearch.WordTrace tailWord_2482765 prefixEnd_2482765 94433466456302511423665 := by
  unfold tailWord_2482765
  simp only [CollatzResearch.WordTrace]
  refine ⟨90553878850373902348953749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60369252566915934899302499 90553878850373902348953749)
  ·
    refine ⟨4244713071111276672607207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 90553878850373902348953749 4244713071111276672607207)
    ·
      refine ⟨6367069606666915008910811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4244713071111276672607207 6367069606666915008910811)
      ·
        refine ⟨9550604410000372513366217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6367069606666915008910811 9550604410000372513366217)
        ·
          refine ⟨7162953307500279385024663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9550604410000372513366217 7162953307500279385024663)
          ·
            refine ⟨10744429961250419077536995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7162953307500279385024663 10744429961250419077536995)
            ·
              refine ⟨16116644941875628616305493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10744429961250419077536995 16116644941875628616305493)
              ·
                refine ⟨94433466456302511423665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16116644941875628616305493 94433466456302511423665)
                ·
                  rfl

theorem cell22_2482765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 9].length) (baseStart_2482765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2482765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2482765 prefixEnd_2482765 := by exact prefixLift 2482765
  have htrace : WordTrace (prefixWord ++ tailWord_2482765) baseStart_2482765 baseEnd_2482765 := by
    simpa [prefixWord, tailWord_2482765, baseEnd_2482765] using wordTrace_append hprefix tailTrace_2482765
  have hstable : (prefixWord ++ tailWord_2482765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2482765).length < 2 ^ (prefixWord ++ tailWord_2482765).sum := by decide
  have hdescent : baseEnd_2482765 < baseStart_2482765 := by decide
  rcases family_descends (prefixWord ++ tailWord_2482765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2482769 : List Nat := [1, 2, 2, 1, 3, 5, 2, 1, 2, 3]
def baseStart_2482769 : Nat := 118140960795 + 2482769 * 2 ^ 59
def prefixEnd_2482769 : Nat := 4983230072969 + 3 ^ 40 * 2482769 * 2
def baseEnd_2482769 : Nat := 849902567388467925712973

theorem tailTrace_2482769 : CollatzResearch.WordTrace tailWord_2482769 prefixEnd_2482769 849902567388467925712973 := by
  unfold tailWord_2482769
  simp only [CollatzResearch.WordTrace]
  refine ⟨90554024742359411032099361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60369349828239607354732907 90554024742359411032099361)
  ·
    refine ⟨67915518556769558274074521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90554024742359411032099361 67915518556769558274074521)
    ·
      refine ⟨50936638917577168705555891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67915518556769558274074521 50936638917577168705555891)
      ·
        refine ⟨76404958376365753058333837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50936638917577168705555891 76404958376365753058333837)
        ·
          refine ⟨28651859391137157396875189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76404958376365753058333837 28651859391137157396875189)
          ·
            refine ⟨2686111817919108505957049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28651859391137157396875189 2686111817919108505957049)
            ·
              refine ⟨2014583863439331379467787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2686111817919108505957049 2014583863439331379467787)
              ·
                refine ⟨3021875795158997069201681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2014583863439331379467787 3021875795158997069201681)
                ·
                  refine ⟨2266406846369247801901261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3021875795158997069201681 2266406846369247801901261)
                  ·
                    refine ⟨849902567388467925712973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2266406846369247801901261 849902567388467925712973)
                    ·
                      rfl

theorem cell22_2482769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 2, 1, 2, 3].length) (baseStart_2482769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2482769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2482769 prefixEnd_2482769 := by exact prefixLift 2482769
  have htrace : WordTrace (prefixWord ++ tailWord_2482769) baseStart_2482769 baseEnd_2482769 := by
    simpa [prefixWord, tailWord_2482769, baseEnd_2482769] using wordTrace_append hprefix tailTrace_2482769
  have hstable : (prefixWord ++ tailWord_2482769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2482769).length < 2 ^ (prefixWord ++ tailWord_2482769).sum := by decide
  have hdescent : baseEnd_2482769 < baseStart_2482769 := by decide
  rcases family_descends (prefixWord ++ tailWord_2482769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2482808 : List Nat := [2, 1, 2, 1, 1, 1, 2, 3, 4, 5]
def baseStart_2482808 : Nat := 118140960795 + 2482808 * 2 ^ 59
def prefixEnd_2482808 : Nat := 4983230072969 + 3 ^ 40 * 2482808 * 2
def baseEnd_2482808 : Nat := 849915917885484823987853

theorem tailTrace_2482808 : CollatzResearch.WordTrace tailWord_2482808 prefixEnd_2482808 849915917885484823987853 := by
  unfold tailWord_2482808
  simp only [CollatzResearch.WordTrace]
  refine ⟨45277723594609060346384539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60370298126145413795179385 45277723594609060346384539)
  ·
    refine ⟨67916585391913590519576809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45277723594609060346384539 67916585391913590519576809)
    ·
      refine ⟨50937439043935192889682607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67916585391913590519576809 50937439043935192889682607)
      ·
        refine ⟨76406158565902789334523911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50937439043935192889682607 76406158565902789334523911)
        ·
          refine ⟨114609237848854184001785867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76406158565902789334523911 114609237848854184001785867)
          ·
            refine ⟨171913856773281276002678801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114609237848854184001785867 171913856773281276002678801)
            ·
              refine ⟨128935392579960957002009101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 171913856773281276002678801 128935392579960957002009101)
              ·
                refine ⟨48350772217485358875753413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 128935392579960957002009101 48350772217485358875753413)
                ·
                  refine ⟨9065769790778504789203765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48350772217485358875753413 9065769790778504789203765)
                  ·
                    refine ⟨849915917885484823987853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9065769790778504789203765 849915917885484823987853)
                    ·
                      rfl

theorem cell22_2482808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 4, 5].length) (baseStart_2482808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2482808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2482808 prefixEnd_2482808 := by exact prefixLift 2482808
  have htrace : WordTrace (prefixWord ++ tailWord_2482808) baseStart_2482808 baseEnd_2482808 := by
    simpa [prefixWord, tailWord_2482808, baseEnd_2482808] using wordTrace_append hprefix tailTrace_2482808
  have hstable : (prefixWord ++ tailWord_2482808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2482808).length < 2 ^ (prefixWord ++ tailWord_2482808).sum := by decide
  have hdescent : baseEnd_2482808 < baseStart_2482808 := by decide
  rcases family_descends (prefixWord ++ tailWord_2482808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2482840 : List Nat := [2, 1, 2, 4, 1, 1, 1, 3, 3, 4]
def baseStart_2482840 : Nat := 118140960795 + 2482840 * 2 ^ 59
def prefixEnd_2482840 : Nat := 4983230072969 + 3 ^ 40 * 2482840 * 2
def baseEnd_2482840 : Nat := 849926872139447407187755

theorem tailTrace_2482840 : CollatzResearch.WordTrace tailWord_2482840 prefixEnd_2482840 849926872139447407187755 := by
  unfold tailWord_2482840
  simp only [CollatzResearch.WordTrace]
  refine ⟨45278307162551095078966987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60371076216734793438622649 45278307162551095078966987)
  ·
    refine ⟨67917460743826642618450481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45278307162551095078966987 67917460743826642618450481)
    ·
      refine ⟨50938095557869981963837861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67917460743826642618450481 50938095557869981963837861)
      ·
        refine ⟨9550892917100621618219599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50938095557869981963837861 9550892917100621618219599)
        ·
          refine ⟨14326339375650932427329399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9550892917100621618219599 14326339375650932427329399)
          ·
            refine ⟨21489509063476398640994099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14326339375650932427329399 21489509063476398640994099)
            ·
              refine ⟨32234263595214597961491149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21489509063476398640994099 32234263595214597961491149)
              ·
                refine ⟨12087848848205474235559181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32234263595214597961491149 12087848848205474235559181)
                ·
                  refine ⟨4532943318077052838334693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12087848848205474235559181 4532943318077052838334693)
                  ·
                    refine ⟨849926872139447407187755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4532943318077052838334693 849926872139447407187755)
                    ·
                      rfl

theorem cell22_2482840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 3, 3, 4].length) (baseStart_2482840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2482840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2482840 prefixEnd_2482840 := by exact prefixLift 2482840
  have htrace : WordTrace (prefixWord ++ tailWord_2482840) baseStart_2482840 baseEnd_2482840 := by
    simpa [prefixWord, tailWord_2482840, baseEnd_2482840] using wordTrace_append hprefix tailTrace_2482840
  have hstable : (prefixWord ++ tailWord_2482840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2482840).length < 2 ^ (prefixWord ++ tailWord_2482840).sum := by decide
  have hdescent : baseEnd_2482840 < baseStart_2482840 := by decide
  rcases family_descends (prefixWord ++ tailWord_2482840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2483007 : List Nat := [1, 1, 2, 2, 5, 2, 1, 2, 6]
def baseStart_2483007 : Nat := 118140960795 + 2483007 * 2 ^ 59
def prefixEnd_2483007 : Nat := 4983230072969 + 3 ^ 40 * 2483007 * 2
def baseEnd_2483007 : Nat := 283328013217438212754081

theorem tailTrace_2483007 : CollatzResearch.WordTrace tailWord_2483007 prefixEnd_2483007 283328013217438212754081 := by
  unfold tailWord_2483007
  simp only [CollatzResearch.WordTrace]
  refine ⟨90562705315497177679263275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60375136876998118452842183 90562705315497177679263275)
  ·
    refine ⟨135844057973245766518894913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90562705315497177679263275 135844057973245766518894913)
    ·
      refine ⟨101883043479934324889171185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135844057973245766518894913 101883043479934324889171185)
      ·
        refine ⟨76412282609950743666878389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101883043479934324889171185 76412282609950743666878389)
        ·
          refine ⟨7163651494682882218769849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 76412282609950743666878389 7163651494682882218769849)
          ·
            refine ⟨5372738621012161664077387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7163651494682882218769849 5372738621012161664077387)
            ·
              refine ⟨8059107931518242496116081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5372738621012161664077387 8059107931518242496116081)
              ·
                refine ⟨6044330948638681872087061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8059107931518242496116081 6044330948638681872087061)
                ·
                  refine ⟨283328013217438212754081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6044330948638681872087061 283328013217438212754081)
                  ·
                    rfl

theorem cell22_2483007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 2, 6].length) (baseStart_2483007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2483007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2483007 prefixEnd_2483007 := by exact prefixLift 2483007
  have htrace : WordTrace (prefixWord ++ tailWord_2483007) baseStart_2483007 baseEnd_2483007 := by
    simpa [prefixWord, tailWord_2483007, baseEnd_2483007] using wordTrace_append hprefix tailTrace_2483007
  have hstable : (prefixWord ++ tailWord_2483007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2483007).length < 2 ^ (prefixWord ++ tailWord_2483007).sum := by decide
  have hdescent : baseEnd_2483007 < baseStart_2483007 := by decide
  rcases family_descends (prefixWord ++ tailWord_2483007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2483097 : List Nat := [1, 2, 1, 2, 1, 3, 1, 6, 5]
def baseStart_2483097 : Nat := 118140960795 + 2483097 * 2 ^ 59
def prefixEnd_2483097 : Nat := 4983230072969 + 3 ^ 40 * 2483097 * 2
def baseEnd_2483097 : Nat := 283338282830528134503989

theorem tailTrace_2483097 : CollatzResearch.WordTrace tailWord_2483097 prefixEnd_2483097 283338282830528134503989 := by
  unfold tailWord_2483097
  simp only [CollatzResearch.WordTrace]
  refine ⟨90565987885171123050039545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60377325256780748700026363 90565987885171123050039545)
  ·
    refine ⟨67924490913878342287529659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90565987885171123050039545 67924490913878342287529659)
    ·
      refine ⟨101886736370817513431294489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67924490913878342287529659 101886736370817513431294489)
      ·
        refine ⟨76415052278113135073470867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101886736370817513431294489 76415052278113135073470867)
        ·
          refine ⟨114622578417169702610206301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76415052278113135073470867 114622578417169702610206301)
          ·
            refine ⟨42983466906438638478827363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 114622578417169702610206301 42983466906438638478827363)
            ·
              refine ⟨64475200359657957718241045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42983466906438638478827363 64475200359657957718241045)
              ·
                refine ⟨3022275016858966768042549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 64475200359657957718241045 3022275016858966768042549)
                ·
                  refine ⟨283338282830528134503989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3022275016858966768042549 283338282830528134503989)
                  ·
                    rfl

theorem cell22_2483097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 6, 5].length) (baseStart_2483097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2483097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2483097 prefixEnd_2483097 := by exact prefixLift 2483097
  have htrace : WordTrace (prefixWord ++ tailWord_2483097) baseStart_2483097 baseEnd_2483097 := by
    simpa [prefixWord, tailWord_2483097, baseEnd_2483097] using wordTrace_append hprefix tailTrace_2483097
  have hstable : (prefixWord ++ tailWord_2483097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2483097).length < 2 ^ (prefixWord ++ tailWord_2483097).sum := by decide
  have hdescent : baseEnd_2483097 < baseStart_2483097 := by decide
  rcases family_descends (prefixWord ++ tailWord_2483097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2483208 : List Nat := [2, 1, 3, 2, 1, 5, 1, 2, 2, 3]
def baseStart_2483208 : Nat := 118140960795 + 2483208 * 2 ^ 59
def prefixEnd_2483208 : Nat := 4983230072969 + 3 ^ 40 * 2483208 * 2
def baseEnd_2483208 : Nat := 850052846060017113986627

theorem tailTrace_2483208 : CollatzResearch.WordTrace tailWord_2483208 prefixEnd_2483208 850052846060017113986627 := by
  unfold tailWord_2483208
  simp only [CollatzResearch.WordTrace]
  refine ⟨45285018193884494503665139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60380024258512659338220185 45285018193884494503665139)
  ·
    refine ⟨67927527290826741755497709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45285018193884494503665139 67927527290826741755497709)
    ·
      refine ⟨25472822734060028158311641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67927527290826741755497709 25472822734060028158311641)
      ·
        refine ⟨19104617050545021118733731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25472822734060028158311641 19104617050545021118733731)
        ·
          refine ⟨28656925575817531678100597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19104617050545021118733731 28656925575817531678100597)
          ·
            refine ⟨2686586772732893594821931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28656925575817531678100597 2686586772732893594821931)
            ·
              refine ⟨4029880159099340392232897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2686586772732893594821931 4029880159099340392232897)
              ·
                refine ⟨3022410119324505294174673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4029880159099340392232897 3022410119324505294174673)
                ·
                  refine ⟨2266807589493378970631005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3022410119324505294174673 2266807589493378970631005)
                  ·
                    refine ⟨850052846060017113986627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2266807589493378970631005 850052846060017113986627)
                    ·
                      rfl

theorem cell22_2483208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 2, 2, 3].length) (baseStart_2483208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2483208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2483208 prefixEnd_2483208 := by exact prefixLift 2483208
  have htrace : WordTrace (prefixWord ++ tailWord_2483208) baseStart_2483208 baseEnd_2483208 := by
    simpa [prefixWord, tailWord_2483208, baseEnd_2483208] using wordTrace_append hprefix tailTrace_2483208
  have hstable : (prefixWord ++ tailWord_2483208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2483208).length < 2 ^ (prefixWord ++ tailWord_2483208).sum := by decide
  have hdescent : baseEnd_2483208 < baseStart_2483208 := by decide
  rcases family_descends (prefixWord ++ tailWord_2483208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2483217 : List Nat := [1, 2, 2, 1, 1, 2, 1, 3, 1, 8]
def baseStart_2483217 : Nat := 118140960795 + 2483217 * 2 ^ 59
def prefixEnd_2483217 : Nat := 4983230072969 + 3 ^ 40 * 2483217 * 2
def baseEnd_2483217 : Nat := 850055926943944090511599

theorem tailTrace_2483217 : CollatzResearch.WordTrace tailWord_2483217 prefixEnd_2483217 850055926943944090511599 := by
  unfold tailWord_2483217
  simp only [CollatzResearch.WordTrace]
  refine ⟨90570364644736383544407905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60380243096490922362938603 90570364644736383544407905)
  ·
    refine ⟨67927773483552287658305929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90570364644736383544407905 67927773483552287658305929)
    ·
      refine ⟨50945830112664215743729447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67927773483552287658305929 50945830112664215743729447)
      ·
        refine ⟨76418745168996323615594171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50945830112664215743729447 76418745168996323615594171)
        ·
          refine ⟨114628117753494485423391257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76418745168996323615594171 114628117753494485423391257)
          ·
            refine ⟨85971088315120864067543443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114628117753494485423391257 85971088315120864067543443)
            ·
              refine ⟨128956632472681296101315165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85971088315120864067543443 128956632472681296101315165)
              ·
                refine ⟨48358737177255486037993187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 128956632472681296101315165 48358737177255486037993187)
                ·
                  refine ⟨72538105765883229056989781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48358737177255486037993187 72538105765883229056989781)
                  ·
                    refine ⟨850055926943944090511599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 72538105765883229056989781 850055926943944090511599)
                    ·
                      rfl

theorem cell22_2483217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 8].length) (baseStart_2483217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2483217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2483217 prefixEnd_2483217 := by exact prefixLift 2483217
  have htrace : WordTrace (prefixWord ++ tailWord_2483217) baseStart_2483217 baseEnd_2483217 := by
    simpa [prefixWord, tailWord_2483217, baseEnd_2483217] using wordTrace_append hprefix tailTrace_2483217
  have hstable : (prefixWord ++ tailWord_2483217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2483217).length < 2 ^ (prefixWord ++ tailWord_2483217).sum := by decide
  have hdescent : baseEnd_2483217 < baseStart_2483217 := by decide
  rcases family_descends (prefixWord ++ tailWord_2483217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2483270 : List Nat := [6, 1, 1, 1, 1, 2, 3, 1, 3, 3]
def baseStart_2483270 : Nat := 118140960795 + 2483270 * 2 ^ 59
def prefixEnd_2483270 : Nat := 4983230072969 + 3 ^ 40 * 2483270 * 2
def baseEnd_2483270 : Nat := 850074069927069618936437

theorem tailTrace_2483270 : CollatzResearch.WordTrace tailWord_2483270 prefixEnd_2483270 850074069927069618936437 := by
  unfold tailWord_2483270
  simp only [CollatzResearch.WordTrace]
  refine ⟨2830384303548261674877727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 60381531809029582397391509 2830384303548261674877727)
  ·
    refine ⟨4245576455322392512316591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2830384303548261674877727 4245576455322392512316591)
    ·
      refine ⟨6368364682983588768474887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4245576455322392512316591 6368364682983588768474887)
      ·
        refine ⟨9552547024475383152712331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6368364682983588768474887 9552547024475383152712331)
        ·
          refine ⟨14328820536713074729068497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9552547024475383152712331 14328820536713074729068497)
          ·
            refine ⟨10746615402534806046801373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14328820536713074729068497 10746615402534806046801373)
            ·
              refine ⟨4029980775950552267550515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10746615402534806046801373 4029980775950552267550515)
              ·
                refine ⟨6044971163925828401325773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4029980775950552267550515 6044971163925828401325773)
                ·
                  refine ⟨2266864186472185650497165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6044971163925828401325773 2266864186472185650497165)
                  ·
                    refine ⟨850074069927069618936437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2266864186472185650497165 850074069927069618936437)
                    ·
                      rfl

theorem cell22_2483270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 1, 3, 3].length) (baseStart_2483270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2483270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2483270 prefixEnd_2483270 := by exact prefixLift 2483270
  have htrace : WordTrace (prefixWord ++ tailWord_2483270) baseStart_2483270 baseEnd_2483270 := by
    simpa [prefixWord, tailWord_2483270, baseEnd_2483270] using wordTrace_append hprefix tailTrace_2483270
  have hstable : (prefixWord ++ tailWord_2483270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2483270).length < 2 ^ (prefixWord ++ tailWord_2483270).sum := by decide
  have hdescent : baseEnd_2483270 < baseStart_2483270 := by decide
  rcases family_descends (prefixWord ++ tailWord_2483270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2483311 : List Nat := [1, 1, 2, 1, 3, 3, 2, 5, 4]
def baseStart_2483311 : Nat := 118140960795 + 2483311 * 2 ^ 59
def prefixEnd_2483311 : Nat := 4983230072969 + 3 ^ 40 * 2483311 * 2
def baseEnd_2483311 : Nat := 283362701688319726220437

theorem tailTrace_2483311 : CollatzResearch.WordTrace tailWord_2483311 prefixEnd_2483311 283362701688319726220437 := by
  unfold tailWord_2483311
  simp only [CollatzResearch.WordTrace]
  refine ⟨90573793106395837598329787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60382528737597225065553191 90573793106395837598329787)
  ·
    refine ⟨135860689659593756397494681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90573793106395837598329787 135860689659593756397494681)
    ·
      refine ⟨101895517244695317298121011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135860689659593756397494681 101895517244695317298121011)
      ·
        refine ⟨152843275867042975947181517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101895517244695317298121011 152843275867042975947181517)
        ·
          refine ⟨57316228450141115980193069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 152843275867042975947181517 57316228450141115980193069)
          ·
            refine ⟨21493585668802918492572401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57316228450141115980193069 21493585668802918492572401)
            ·
              refine ⟨16120189251602188869429301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21493585668802918492572401 16120189251602188869429301)
              ·
                refine ⟨1511267742337705206508997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16120189251602188869429301 1511267742337705206508997)
                ·
                  refine ⟨283362701688319726220437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1511267742337705206508997 283362701688319726220437)
                  ·
                    rfl

theorem cell22_2483311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 5, 4].length) (baseStart_2483311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2483311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2483311 prefixEnd_2483311 := by exact prefixLift 2483311
  have htrace : WordTrace (prefixWord ++ tailWord_2483311) baseStart_2483311 baseEnd_2483311 := by
    simpa [prefixWord, tailWord_2483311, baseEnd_2483311] using wordTrace_append hprefix tailTrace_2483311
  have hstable : (prefixWord ++ tailWord_2483311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2483311).length < 2 ^ (prefixWord ++ tailWord_2483311).sum := by decide
  have hdescent : baseEnd_2483311 < baseStart_2483311 := by decide
  rcases family_descends (prefixWord ++ tailWord_2483311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2483328 : List Nat := [2, 1, 1, 2, 1, 3, 6, 2, 4]
def baseStart_2483328 : Nat := 118140960795 + 2483328 * 2 ^ 59
def prefixEnd_2483328 : Nat := 4983230072969 + 3 ^ 40 * 2483328 * 2
def baseEnd_2483328 : Nat := 283364641504125600328753

theorem tailTrace_2483328 : CollatzResearch.WordTrace tailWord_2483328 prefixEnd_2483328 283364641504125600328753 := by
  unfold tailWord_2483328
  simp only [CollatzResearch.WordTrace]
  refine ⟨45287206573667124750849319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60382942098222833001132425 45287206573667124750849319)
  ·
    refine ⟨67930809860500687126273979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45287206573667124750849319 67930809860500687126273979)
    ·
      refine ⟨101896214790751030689410969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67930809860500687126273979 101896214790751030689410969)
      ·
        refine ⟨76422161093063273017058227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101896214790751030689410969 76422161093063273017058227)
        ·
          refine ⟨114633241639594909525587341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76422161093063273017058227 114633241639594909525587341)
          ·
            refine ⟨42987465614848091072095253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 114633241639594909525587341 42987465614848091072095253)
            ·
              refine ⟨2015037450696004269004465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 42987465614848091072095253 2015037450696004269004465)
              ·
                refine ⟨1511278088022003201753349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2015037450696004269004465 1511278088022003201753349)
                ·
                  refine ⟨283364641504125600328753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1511278088022003201753349 283364641504125600328753)
                  ·
                    rfl

theorem cell22_2483328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 6, 2, 4].length) (baseStart_2483328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2483328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2483328 prefixEnd_2483328 := by exact prefixLift 2483328
  have htrace : WordTrace (prefixWord ++ tailWord_2483328) baseStart_2483328 baseEnd_2483328 := by
    simpa [prefixWord, tailWord_2483328, baseEnd_2483328] using wordTrace_append hprefix tailTrace_2483328
  have hstable : (prefixWord ++ tailWord_2483328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2483328).length < 2 ^ (prefixWord ++ tailWord_2483328).sum := by decide
  have hdescent : baseEnd_2483328 < baseStart_2483328 := by decide
  rcases family_descends (prefixWord ++ tailWord_2483328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2483358 : List Nat := [4, 3, 1, 1, 2, 2, 1, 1, 1, 6]
def baseStart_2483358 : Nat := 118140960795 + 2483358 * 2 ^ 59
def prefixEnd_2483358 : Nat := 4983230072969 + 3 ^ 40 * 2483358 * 2
def baseEnd_2483358 : Nat := 850104194125466722736167

theorem tailTrace_2483358 : CollatzResearch.WordTrace tailWord_2483358 prefixEnd_2483358 850104194125466722736167 := by
  unfold tailWord_2483358
  simp only [CollatzResearch.WordTrace]
  refine ⟨11321938417153195578161341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60383671558150376416860485 11321938417153195578161341)
  ·
    refine ⟨4245726906432448341810503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11321938417153195578161341 4245726906432448341810503)
    ·
      refine ⟨6368590359648672512715755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4245726906432448341810503 6368590359648672512715755)
      ·
        refine ⟨9552885539473008769073633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6368590359648672512715755 9552885539473008769073633)
        ·
          refine ⟨7164664154604756576805225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9552885539473008769073633 7164664154604756576805225)
          ·
            refine ⟨5373498115953567432603919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7164664154604756576805225 5373498115953567432603919)
            ·
              refine ⟨8060247173930351148905879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5373498115953567432603919 8060247173930351148905879)
              ·
                refine ⟨12090370760895526723358819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8060247173930351148905879 12090370760895526723358819)
                ·
                  refine ⟨18135556141343290085038229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12090370760895526723358819 18135556141343290085038229)
                  ·
                    refine ⟨850104194125466722736167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18135556141343290085038229 850104194125466722736167)
                    ·
                      rfl

theorem cell22_2483358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_2483358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2483358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2483358 prefixEnd_2483358 := by exact prefixLift 2483358
  have htrace : WordTrace (prefixWord ++ tailWord_2483358) baseStart_2483358 baseEnd_2483358 := by
    simpa [prefixWord, tailWord_2483358, baseEnd_2483358] using wordTrace_append hprefix tailTrace_2483358
  have hstable : (prefixWord ++ tailWord_2483358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2483358).length < 2 ^ (prefixWord ++ tailWord_2483358).sum := by decide
  have hdescent : baseEnd_2483358 < baseStart_2483358 := by decide
  rcases family_descends (prefixWord ++ tailWord_2483358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2483388 : List Nat := [2, 2, 2, 3, 2, 1, 1, 3, 3, 3]
def baseStart_2483388 : Nat := 118140960795 + 2483388 * 2 ^ 59
def prefixEnd_2483388 : Nat := 4983230072969 + 3 ^ 40 * 2483388 * 2
def baseEnd_2483388 : Nat := 850114463738556644486075

theorem tailTrace_2483388 : CollatzResearch.WordTrace tailWord_2483388 prefixEnd_2483388 850114463738556644486075 := by
  unfold tailWord_2483388
  simp only [CollatzResearch.WordTrace]
  refine ⟨45288300763558439874441409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60384401018077919832588545 45288300763558439874441409)
  ·
    refine ⟨33966225572668829905831057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45288300763558439874441409 33966225572668829905831057)
    ·
      refine ⟨25474669179501622429373293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33966225572668829905831057 25474669179501622429373293)
      ·
        refine ⟨9553000942313108411014985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25474669179501622429373293 9553000942313108411014985)
        ·
          refine ⟨7164750706734831308261239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9553000942313108411014985 7164750706734831308261239)
          ·
            refine ⟨10747126060102246962391859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7164750706734831308261239 10747126060102246962391859)
            ·
              refine ⟨16120689090153370443587789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10747126060102246962391859 16120689090153370443587789)
              ·
                refine ⟨6045258408807513916345421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16120689090153370443587789 6045258408807513916345421)
                ·
                  refine ⟨2266971903302817718629533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6045258408807513916345421 2266971903302817718629533)
                  ·
                    refine ⟨850114463738556644486075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2266971903302817718629533 850114463738556644486075)
                    ·
                      rfl

theorem cell22_2483388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 3, 3, 3].length) (baseStart_2483388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2483388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2483388 prefixEnd_2483388 := by exact prefixLift 2483388
  have htrace : WordTrace (prefixWord ++ tailWord_2483388) baseStart_2483388 baseEnd_2483388 := by
    simpa [prefixWord, tailWord_2483388, baseEnd_2483388] using wordTrace_append hprefix tailTrace_2483388
  have hstable : (prefixWord ++ tailWord_2483388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2483388).length < 2 ^ (prefixWord ++ tailWord_2483388).sum := by decide
  have hdescent : baseEnd_2483388 < baseStart_2483388 := by decide
  rcases family_descends (prefixWord ++ tailWord_2483388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2483394 : List Nat := [3, 5, 1, 1, 3, 1, 1, 1, 1, 5]
def baseStart_2483394 : Nat := 118140960795 + 2483394 * 2 ^ 59
def prefixEnd_2483394 : Nat := 4983230072969 + 3 ^ 40 * 2483394 * 2
def baseEnd_2483394 : Nat := 850116517661174628836057

theorem tailTrace_2483394 : CollatzResearch.WordTrace tailWord_2483394 prefixEnd_2483394 850116517661174628836057 := by
  unfold tailWord_2483394
  simp only [CollatzResearch.WordTrace]
  refine ⟨22644205091273785693400309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60384546910063428515734157 22644205091273785693400309)
  ·
    refine ⟨2122894227306917408756279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22644205091273785693400309 2122894227306917408756279)
    ·
      refine ⟨3184341340960376113134419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2122894227306917408756279 3184341340960376113134419)
      ·
        refine ⟨4776512011440564169701629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3184341340960376113134419 4776512011440564169701629)
        ·
          refine ⟨1791192004290211563638111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4776512011440564169701629 1791192004290211563638111)
          ·
            refine ⟨2686788006435317345457167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1791192004290211563638111 2686788006435317345457167)
            ·
              refine ⟨4030182009652976018185751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2686788006435317345457167 4030182009652976018185751)
              ·
                refine ⟨6045273014479464027278627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4030182009652976018185751 6045273014479464027278627)
                ·
                  refine ⟨9067909521719196040917941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6045273014479464027278627 9067909521719196040917941)
                  ·
                    refine ⟨850116517661174628836057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9067909521719196040917941 850116517661174628836057)
                    ·
                      rfl

theorem cell22_2483394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_2483394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2483394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2483394 prefixEnd_2483394 := by exact prefixLift 2483394
  have htrace : WordTrace (prefixWord ++ tailWord_2483394) baseStart_2483394 baseEnd_2483394 := by
    simpa [prefixWord, tailWord_2483394, baseEnd_2483394] using wordTrace_append hprefix tailTrace_2483394
  have hstable : (prefixWord ++ tailWord_2483394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2483394).length < 2 ^ (prefixWord ++ tailWord_2483394).sum := by decide
  have hdescent : baseEnd_2483394 < baseStart_2483394 := by decide
  rcases family_descends (prefixWord ++ tailWord_2483394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2483452 : List Nat := [2, 2, 2, 1, 6, 1, 2, 1, 5]
def baseStart_2483452 : Nat := 118140960795 + 2483452 * 2 ^ 59
def prefixEnd_2483452 : Nat := 4983230072969 + 3 ^ 40 * 2483452 * 2
def baseEnd_2483452 : Nat := 283378790748827270295293

theorem tailTrace_2483452 : CollatzResearch.WordTrace tailWord_2483452 prefixEnd_2483452 283378790748827270295293 := by
  unfold tailWord_2483452
  simp only [CollatzResearch.WordTrace]
  refine ⟨45289467899442509339606305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60385957199256679119475073 45289467899442509339606305)
  ·
    refine ⟨33967100924581882004704729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45289467899442509339606305 33967100924581882004704729)
    ·
      refine ⟨25475325693436411503528547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33967100924581882004704729 25475325693436411503528547)
      ·
        refine ⟨38212988540154617255292821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25475325693436411503528547 38212988540154617255292821)
        ·
          refine ⟨1791233837819747683841851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 38212988540154617255292821 1791233837819747683841851)
          ·
            refine ⟨2686850756729621525762777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1791233837819747683841851 2686850756729621525762777)
            ·
              refine ⟨2015138067547216144322083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2686850756729621525762777 2015138067547216144322083)
              ·
                refine ⟨3022707101320824216483125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2015138067547216144322083 3022707101320824216483125)
                ·
                  refine ⟨283378790748827270295293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3022707101320824216483125 283378790748827270295293)
                  ·
                    rfl

theorem cell22_2483452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 2, 1, 5].length) (baseStart_2483452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2483452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2483452 prefixEnd_2483452 := by exact prefixLift 2483452
  have htrace : WordTrace (prefixWord ++ tailWord_2483452) baseStart_2483452 baseEnd_2483452 := by
    simpa [prefixWord, tailWord_2483452, baseEnd_2483452] using wordTrace_append hprefix tailTrace_2483452
  have hstable : (prefixWord ++ tailWord_2483452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2483452).length < 2 ^ (prefixWord ++ tailWord_2483452).sum := by decide
  have hdescent : baseEnd_2483452 < baseStart_2483452 := by decide
  rcases family_descends (prefixWord ++ tailWord_2483452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2483461 : List Nat := [1, 3, 1, 1, 2, 1, 4, 3, 1, 5]
def baseStart_2483461 : Nat := 118140960795 + 2483461 * 2 ^ 59
def prefixEnd_2483461 : Nat := 4983230072969 + 3 ^ 40 * 2483461 * 2
def baseEnd_2483461 : Nat := 850139453130408787410851

theorem tailTrace_2483461 : CollatzResearch.WordTrace tailWord_2483461 prefixEnd_2483461 850139453130408787410851 := by
  unfold tailWord_2483461
  simp only [CollatzResearch.WordTrace]
  refine ⟨90579264055852413216290237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60386176037234942144193491 90579264055852413216290237)
  ·
    refine ⟨33967224020944654956108839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90579264055852413216290237 33967224020944654956108839)
    ·
      refine ⟨50950836031416982434163259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33967224020944654956108839 50950836031416982434163259)
      ·
        refine ⟨76426254047125473651244889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50950836031416982434163259 76426254047125473651244889)
        ·
          refine ⟨57319690535344105238433667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76426254047125473651244889 57319690535344105238433667)
          ·
            refine ⟨85979535803016157857650501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57319690535344105238433667 85979535803016157857650501)
            ·
              refine ⟨16121162963065529598309469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 85979535803016157857650501 16121162963065529598309469)
              ·
                refine ⟨6045436111149573599366051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16121162963065529598309469 6045436111149573599366051)
                ·
                  refine ⟨9068154166724360399049077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6045436111149573599366051 9068154166724360399049077)
                  ·
                    refine ⟨850139453130408787410851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9068154166724360399049077 850139453130408787410851)
                    ·
                      rfl

theorem cell22_2483461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 3, 1, 5].length) (baseStart_2483461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2483461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2483461 prefixEnd_2483461 := by exact prefixLift 2483461
  have htrace : WordTrace (prefixWord ++ tailWord_2483461) baseStart_2483461 baseEnd_2483461 := by
    simpa [prefixWord, tailWord_2483461, baseEnd_2483461] using wordTrace_append hprefix tailTrace_2483461
  have hstable : (prefixWord ++ tailWord_2483461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2483461).length < 2 ^ (prefixWord ++ tailWord_2483461).sum := by decide
  have hdescent : baseEnd_2483461 < baseStart_2483461 := by decide
  rcases family_descends (prefixWord ++ tailWord_2483461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2483493 : List Nat := [1, 3, 1, 2, 4, 1, 2, 2, 2, 4]
def baseStart_2483493 : Nat := 118140960795 + 2483493 * 2 ^ 59
def prefixEnd_2483493 : Nat := 4983230072969 + 3 ^ 40 * 2483493 * 2
def baseEnd_2483493 : Nat := 850150407384371370610753

theorem tailTrace_2483493 : CollatzResearch.WordTrace tailWord_2483493 prefixEnd_2483493 850150407384371370610753 := by
  unfold tailWord_2483493
  simp only [CollatzResearch.WordTrace]
  refine ⟨90580431191736482681455133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60386954127824321787636755 90580431191736482681455133)
  ·
    refine ⟨33967661696901181005545675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90580431191736482681455133 33967661696901181005545675)
    ·
      refine ⟨50951492545351771508318513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33967661696901181005545675 50951492545351771508318513)
      ·
        refine ⟨38213619409013828631238885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50951492545351771508318513 38213619409013828631238885)
        ·
          refine ⟨7165053639190092868357291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38213619409013828631238885 7165053639190092868357291)
          ·
            refine ⟨10747580458785139302535937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7165053639190092868357291 10747580458785139302535937)
            ·
              refine ⟨8060685344088854476901953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10747580458785139302535937 8060685344088854476901953)
              ·
                refine ⟨6045514008066640857676465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8060685344088854476901953 6045514008066640857676465)
                ·
                  refine ⟨4534135506049980643257349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6045514008066640857676465 4534135506049980643257349)
                  ·
                    refine ⟨850150407384371370610753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4534135506049980643257349 850150407384371370610753)
                    ·
                      rfl

theorem cell22_2483493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 2, 2, 4].length) (baseStart_2483493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2483493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2483493 prefixEnd_2483493 := by exact prefixLift 2483493
  have htrace : WordTrace (prefixWord ++ tailWord_2483493) baseStart_2483493 baseEnd_2483493 := by
    simpa [prefixWord, tailWord_2483493, baseEnd_2483493] using wordTrace_append hprefix tailTrace_2483493
  have hstable : (prefixWord ++ tailWord_2483493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2483493).length < 2 ^ (prefixWord ++ tailWord_2483493).sum := by decide
  have hdescent : baseEnd_2483493 < baseStart_2483493 := by decide
  rcases family_descends (prefixWord ++ tailWord_2483493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2483536 : List Nat := [2, 1, 1, 1, 1, 5, 2, 2, 7]
def baseStart_2483536 : Nat := 118140960795 + 2483536 * 2 ^ 59
def prefixEnd_2483536 : Nat := 4983230072969 + 3 ^ 40 * 2483536 * 2
def baseEnd_2483536 : Nat := 283388375721044530595207

theorem tailTrace_2483536 : CollatzResearch.WordTrace tailWord_2483536 prefixEnd_2483536 283388375721044530595207 := by
  unfold tailWord_2483536
  simp only [CollatzResearch.WordTrace]
  refine ⟨45290999765290350512635231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60387999687053800683513641 45290999765290350512635231)
  ·
    refine ⟨67936499647935525768952847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45290999765290350512635231 67936499647935525768952847)
    ·
      refine ⟨101904749471903288653429271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67936499647935525768952847 101904749471903288653429271)
      ·
        refine ⟨152857124207854932980143907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101904749471903288653429271 152857124207854932980143907)
        ·
          refine ⟨229285686311782399470215861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152857124207854932980143907 229285686311782399470215861)
          ·
            refine ⟨21495533091729599950332737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 229285686311782399470215861 21495533091729599950332737)
            ·
              refine ⟨16121649818797199962749553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21495533091729599950332737 16121649818797199962749553)
              ·
                refine ⟨12091237364097899972062165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16121649818797199962749553 12091237364097899972062165)
                ·
                  refine ⟨283388375721044530595207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12091237364097899972062165 283388375721044530595207)
                  ·
                    rfl

theorem cell22_2483536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 2, 7].length) (baseStart_2483536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2483536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2483536 prefixEnd_2483536 := by exact prefixLift 2483536
  have htrace : WordTrace (prefixWord ++ tailWord_2483536) baseStart_2483536 baseEnd_2483536 := by
    simpa [prefixWord, tailWord_2483536, baseEnd_2483536] using wordTrace_append hprefix tailTrace_2483536
  have hstable : (prefixWord ++ tailWord_2483536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2483536).length < 2 ^ (prefixWord ++ tailWord_2483536).sum := by decide
  have hdescent : baseEnd_2483536 < baseStart_2483536 := by decide
  rcases family_descends (prefixWord ++ tailWord_2483536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2483570 : List Nat := [3, 2, 1, 2, 1, 2, 5, 1, 5]
def baseStart_2483570 : Nat := 118140960795 + 2483570 * 2 ^ 59
def prefixEnd_2483570 : Nat := 4983230072969 + 3 ^ 40 * 2483570 * 2
def baseEnd_2483570 : Nat := 283392255352656278811839

theorem tailTrace_2483570 : CollatzResearch.WordTrace tailWord_2483570 prefixEnd_2483570 283392255352656278811839 := by
  unfold tailWord_2483570
  simp only [CollatzResearch.WordTrace]
  refine ⟨22645809903114381208002041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60388826408305016554672109 22645809903114381208002041)
  ·
    refine ⟨16984357427335785906001531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22645809903114381208002041 16984357427335785906001531)
    ·
      refine ⟨25476536141003678859002297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16984357427335785906001531 25476536141003678859002297)
      ·
        refine ⟨19107402105752759144251723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25476536141003678859002297 19107402105752759144251723)
        ·
          refine ⟨28661103158629138716377585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19107402105752759144251723 28661103158629138716377585)
          ·
            refine ⟨21495827368971854037283189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28661103158629138716377585 21495827368971854037283189)
            ·
              refine ⟨2015233815841111315995299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21495827368971854037283189 2015233815841111315995299)
              ·
                refine ⟨3022850723761666973992949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2015233815841111315995299 3022850723761666973992949)
                ·
                  refine ⟨283392255352656278811839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3022850723761666973992949 283392255352656278811839)
                  ·
                    rfl

theorem cell22_2483570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 5, 1, 5].length) (baseStart_2483570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2483570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2483570 prefixEnd_2483570 := by exact prefixLift 2483570
  have htrace : WordTrace (prefixWord ++ tailWord_2483570) baseStart_2483570 baseEnd_2483570 := by
    simpa [prefixWord, tailWord_2483570, baseEnd_2483570] using wordTrace_append hprefix tailTrace_2483570
  have hstable : (prefixWord ++ tailWord_2483570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2483570).length < 2 ^ (prefixWord ++ tailWord_2483570).sum := by decide
  have hdescent : baseEnd_2483570 < baseStart_2483570 := by decide
  rcases family_descends (prefixWord ++ tailWord_2483570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2483615 : List Nat := [1, 1, 2, 5, 1, 4, 1, 1, 6]
def baseStart_2483615 : Nat := 118140960795 + 2483615 * 2 ^ 59
def prefixEnd_2483615 : Nat := 4983230072969 + 3 ^ 40 * 2483615 * 2
def baseEnd_2483615 : Nat := 283397390159201239686793

theorem tailTrace_2483615 : CollatzResearch.WordTrace tailWord_2483615 prefixEnd_2483615 283397390159201239686793 := by
  unfold tailWord_2483615
  simp only [CollatzResearch.WordTrace]
  refine ⟨90584880897294497517396299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60389920598196331678264199 90584880897294497517396299)
  ·
    refine ⟨135877321345941746276094449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90584880897294497517396299 135877321345941746276094449)
    ·
      refine ⟨101907991009456309707070837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135877321345941746276094449 101907991009456309707070837)
      ·
        refine ⟨9553874157136529035037891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 101907991009456309707070837 9553874157136529035037891)
        ·
          refine ⟨14330811235704793552556837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9553874157136529035037891 14330811235704793552556837)
          ·
            refine ⟨2687027106694648791104407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14330811235704793552556837 2687027106694648791104407)
            ·
              refine ⟨4030540660041973186656611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2687027106694648791104407 4030540660041973186656611)
              ·
                refine ⟨6045810990062959779984917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4030540660041973186656611 6045810990062959779984917)
                ·
                  refine ⟨283397390159201239686793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6045810990062959779984917 283397390159201239686793)
                  ·
                    rfl

theorem cell22_2483615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 1, 6].length) (baseStart_2483615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2483615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2483615 prefixEnd_2483615 := by exact prefixLift 2483615
  have htrace : WordTrace (prefixWord ++ tailWord_2483615) baseStart_2483615 baseEnd_2483615 := by
    simpa [prefixWord, tailWord_2483615, baseEnd_2483615] using wordTrace_append hprefix tailTrace_2483615
  have hstable : (prefixWord ++ tailWord_2483615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2483615).length < 2 ^ (prefixWord ++ tailWord_2483615).sum := by decide
  have hdescent : baseEnd_2483615 < baseStart_2483615 := by decide
  rcases family_descends (prefixWord ++ tailWord_2483615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2483645 : List Nat := [1, 4, 1, 2, 2, 1, 4, 1, 2, 4]
def baseStart_2483645 : Nat := 118140960795 + 2483645 * 2 ^ 59
def prefixEnd_2483645 : Nat := 4983230072969 + 3 ^ 40 * 2483645 * 2
def baseEnd_2483645 : Nat := 850202440090693640810287

theorem tailTrace_2483645 : CollatzResearch.WordTrace tailWord_2483645 prefixEnd_2483645 850202440090693640810287 := by
  unfold tailWord_2483645
  simp only [CollatzResearch.WordTrace]
  refine ⟨90585975087185812640988389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60390650058123875093992259 90585975087185812640988389)
  ·
    refine ⟨16984870328847339870185323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90585975087185812640988389 16984870328847339870185323)
    ·
      refine ⟨25477305493271009805277985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16984870328847339870185323 25477305493271009805277985)
      ·
        refine ⟨19107979119953257353958489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25477305493271009805277985 19107979119953257353958489)
        ·
          refine ⟨14330984339964943015468867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19107979119953257353958489 14330984339964943015468867)
          ·
            refine ⟨21496476509947414523203301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14330984339964943015468867 21496476509947414523203301)
            ·
              refine ⟨4030589345615140223100619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21496476509947414523203301 4030589345615140223100619)
              ·
                refine ⟨6045884018422710334650929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4030589345615140223100619 6045884018422710334650929)
                ·
                  refine ⟨4534413013817032750988197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6045884018422710334650929 4534413013817032750988197)
                  ·
                    refine ⟨850202440090693640810287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4534413013817032750988197 850202440090693640810287)
                    ·
                      rfl

theorem cell22_2483645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 1, 2, 4].length) (baseStart_2483645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2483645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2483645 prefixEnd_2483645 := by exact prefixLift 2483645
  have htrace : WordTrace (prefixWord ++ tailWord_2483645) baseStart_2483645 baseEnd_2483645 := by
    simpa [prefixWord, tailWord_2483645, baseEnd_2483645] using wordTrace_append hprefix tailTrace_2483645
  have hstable : (prefixWord ++ tailWord_2483645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2483645).length < 2 ^ (prefixWord ++ tailWord_2483645).sum := by decide
  have hdescent : baseEnd_2483645 < baseStart_2483645 := by decide
  rcases family_descends (prefixWord ++ tailWord_2483645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2483673 : List Nat := [1, 2, 1, 2, 4, 2, 1, 1, 2, 6]
def baseStart_2483673 : Nat := 118140960795 + 2483673 * 2 ^ 59
def prefixEnd_2483673 : Nat := 4983230072969 + 3 ^ 40 * 2483673 * 2
def baseEnd_2483673 : Nat := 850212025062910901110201

theorem tailTrace_2483673 : CollatzResearch.WordTrace tailWord_2483673 prefixEnd_2483673 850212025062910901110201 := by
  unfold tailWord_2483673
  simp only [CollatzResearch.WordTrace]
  refine ⟨90586996331084373423007673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60391330887389582282005115 90586996331084373423007673)
  ·
    refine ⟨67940247248313280067255755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90586996331084373423007673 67940247248313280067255755)
    ·
      refine ⟨101910370872469920100883633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67940247248313280067255755 101910370872469920100883633)
      ·
        refine ⟨76432778154352440075662725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101910370872469920100883633 76432778154352440075662725)
        ·
          refine ⟨14331145903941082514186761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76432778154352440075662725 14331145903941082514186761)
          ·
            refine ⟨10748359427955811885640071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14331145903941082514186761 10748359427955811885640071)
            ·
              refine ⟨16122539141933717828460107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10748359427955811885640071 16122539141933717828460107)
              ·
                refine ⟨24183808712900576742690161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16122539141933717828460107 24183808712900576742690161)
                ·
                  refine ⟨18137856534675432557017621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24183808712900576742690161 18137856534675432557017621)
                  ·
                    refine ⟨850212025062910901110201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18137856534675432557017621 850212025062910901110201)
                    ·
                      rfl

theorem cell22_2483673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 1, 2, 6].length) (baseStart_2483673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2483673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2483673 prefixEnd_2483673 := by exact prefixLift 2483673
  have htrace : WordTrace (prefixWord ++ tailWord_2483673) baseStart_2483673 baseEnd_2483673 := by
    simpa [prefixWord, tailWord_2483673, baseEnd_2483673] using wordTrace_append hprefix tailTrace_2483673
  have hstable : (prefixWord ++ tailWord_2483673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2483673).length < 2 ^ (prefixWord ++ tailWord_2483673).sum := by decide
  have hdescent : baseEnd_2483673 < baseStart_2483673 := by decide
  rcases family_descends (prefixWord ++ tailWord_2483673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2483709 : List Nat := [1, 4, 1, 1, 1, 5, 2, 3, 1, 3]
def baseStart_2483709 : Nat := 118140960795 + 2483709 * 2 ^ 59
def prefixEnd_2483709 : Nat := 4983230072969 + 3 ^ 40 * 2483709 * 2
def baseEnd_2483709 : Nat := 850224348598618807210091

theorem tailTrace_2483709 : CollatzResearch.WordTrace tailWord_2483709 prefixEnd_2483709 850224348598618807210091 := by
  unfold tailWord_2483709
  simp only [CollatzResearch.WordTrace]
  refine ⟨90588309358953951571318181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60392206239302634380878787 90588309358953951571318181)
  ·
    refine ⟨16985308004803865919622159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90588309358953951571318181 16985308004803865919622159)
    ·
      refine ⟨25477962007205798879433239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16985308004803865919622159 25477962007205798879433239)
      ·
        refine ⟨38216943010808698319149859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25477962007205798879433239 38216943010808698319149859)
        ·
          refine ⟨57325414516213047478724789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38216943010808698319149859 57325414516213047478724789)
          ·
            refine ⟨5374257610894973201130449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 57325414516213047478724789 5374257610894973201130449)
            ·
              refine ⟨4030693208171229900847837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5374257610894973201130449 4030693208171229900847837)
              ·
                refine ⟨1511509953064211212817939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4030693208171229900847837 1511509953064211212817939)
                ·
                  refine ⟨2267264929596316819226909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1511509953064211212817939 2267264929596316819226909)
                  ·
                    refine ⟨850224348598618807210091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2267264929596316819226909 850224348598618807210091)
                    ·
                      rfl

theorem cell22_2483709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 3, 1, 3].length) (baseStart_2483709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2483709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2483709 prefixEnd_2483709 := by exact prefixLift 2483709
  have htrace : WordTrace (prefixWord ++ tailWord_2483709) baseStart_2483709 baseEnd_2483709 := by
    simpa [prefixWord, tailWord_2483709, baseEnd_2483709] using wordTrace_append hprefix tailTrace_2483709
  have hstable : (prefixWord ++ tailWord_2483709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2483709).length < 2 ^ (prefixWord ++ tailWord_2483709).sum := by decide
  have hdescent : baseEnd_2483709 < baseStart_2483709 := by decide
  rcases family_descends (prefixWord ++ tailWord_2483709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2483722 : List Nat := [3, 1, 2, 2, 2, 4, 1, 2, 5]
def baseStart_2483722 : Nat := 118140960795 + 2483722 * 2 ^ 59
def prefixEnd_2483722 : Nat := 4983230072969 + 3 ^ 40 * 2483722 * 2
def baseEnd_2483722 : Nat := 283409599588097035545017

theorem tailTrace_2483722 : CollatzResearch.WordTrace tailWord_2483722 prefixEnd_2483722 283409599588097035545017 := by
  unfold tailWord_2483722
  simp only [CollatzResearch.WordTrace]
  refine ⟨22647195876976713697885355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60392522338604569861027613 22647195876976713697885355)
  ·
    refine ⟨33970793815465070546828033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22647195876976713697885355 33970793815465070546828033)
    ·
      refine ⟨25478095361598802910121025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33970793815465070546828033 25478095361598802910121025)
      ·
        refine ⟨19108571521199102182590769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25478095361598802910121025 19108571521199102182590769)
        ·
          refine ⟨14331428640899326636943077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19108571521199102182590769 14331428640899326636943077)
          ·
            refine ⟨2687142870168623744426827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14331428640899326636943077 2687142870168623744426827)
            ·
              refine ⟨4030714305252935616640241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2687142870168623744426827 4030714305252935616640241)
              ·
                refine ⟨3023035728939701712480181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4030714305252935616640241 3023035728939701712480181)
                ·
                  refine ⟨283409599588097035545017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3023035728939701712480181 283409599588097035545017)
                  ·
                    rfl

theorem cell22_2483722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 2, 5].length) (baseStart_2483722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2483722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2483722 prefixEnd_2483722 := by exact prefixLift 2483722
  have htrace : WordTrace (prefixWord ++ tailWord_2483722) baseStart_2483722 baseEnd_2483722 := by
    simpa [prefixWord, tailWord_2483722, baseEnd_2483722] using wordTrace_append hprefix tailTrace_2483722
  have hstable : (prefixWord ++ tailWord_2483722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2483722).length < 2 ^ (prefixWord ++ tailWord_2483722).sum := by decide
  have hdescent : baseEnd_2483722 < baseStart_2483722 := by decide
  rcases family_descends (prefixWord ++ tailWord_2483722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2483767 : List Nat := [1, 1, 3, 1, 2, 4, 3, 3, 4]
def baseStart_2483767 : Nat := 118140960795 + 2483767 * 2 ^ 59
def prefixEnd_2483767 : Nat := 4983230072969 + 3 ^ 40 * 2483767 * 2
def baseEnd_2483767 : Nat := 283414734394641996419971

theorem tailTrace_2483767 : CollatzResearch.WordTrace tailWord_2483767 prefixEnd_2483767 283414734394641996419971 := by
  unfold tailWord_2483767
  simp only [CollatzResearch.WordTrace]
  refine ⟨90590424792743827476929555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60393616528495884984619703 90590424792743827476929555)
  ·
    refine ⟨135885637189115741215394333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90590424792743827476929555 135885637189115741215394333)
    ·
      refine ⟨50957113945918402955772875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135885637189115741215394333 50957113945918402955772875)
      ·
        refine ⟨76435670918877604433659313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50957113945918402955772875 76435670918877604433659313)
        ·
          refine ⟨57326753189158203325244485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76435670918877604433659313 57326753189158203325244485)
          ·
            refine ⟨10748766222967163123483341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57326753189158203325244485 10748766222967163123483341)
            ·
              refine ⟨4030787333612686171306253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10748766222967163123483341 4030787333612686171306253)
              ·
                refine ⟨1511545250104757314239845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4030787333612686171306253 1511545250104757314239845)
                ·
                  refine ⟨283414734394641996419971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1511545250104757314239845 283414734394641996419971)
                  ·
                    rfl

theorem cell22_2483767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 3, 4].length) (baseStart_2483767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2483767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2483767 prefixEnd_2483767 := by exact prefixLift 2483767
  have htrace : WordTrace (prefixWord ++ tailWord_2483767) baseStart_2483767 baseEnd_2483767 := by
    simpa [prefixWord, tailWord_2483767, baseEnd_2483767] using wordTrace_append hprefix tailTrace_2483767
  have hstable : (prefixWord ++ tailWord_2483767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2483767).length < 2 ^ (prefixWord ++ tailWord_2483767).sum := by decide
  have hdescent : baseEnd_2483767 < baseStart_2483767 := by decide
  rcases family_descends (prefixWord ++ tailWord_2483767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2483799 : List Nat := [1, 1, 3, 2, 2, 3, 4, 1, 2, 3]
def baseStart_2483799 : Nat := 118140960795 + 2483799 * 2 ^ 59
def prefixEnd_2483799 : Nat := 4983230072969 + 3 ^ 40 * 2483799 * 2
def baseEnd_2483799 : Nat := 850255157437888572459815

theorem tailTrace_2483799 : CollatzResearch.WordTrace tailWord_2483799 prefixEnd_2483799 850255157437888572459815 := by
  unfold tailWord_2483799
  simp only [CollatzResearch.WordTrace]
  refine ⟨90591591928627896942094451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60394394619085264628062967 90591591928627896942094451)
  ·
    refine ⟨135887387892941845413141677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90591591928627896942094451 135887387892941845413141677)
    ·
      refine ⟨50957770459853192029928129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135887387892941845413141677 50957770459853192029928129)
      ·
        refine ⟨38218327844889894022446097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50957770459853192029928129 38218327844889894022446097)
        ·
          refine ⟨28663745883667420516834573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38218327844889894022446097 28663745883667420516834573)
          ·
            refine ⟨10748904706375282693812965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28663745883667420516834573 10748904706375282693812965)
            ·
              refine ⟨2015419632445365505089931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10748904706375282693812965 2015419632445365505089931)
              ·
                refine ⟨3023129448668048257634897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2015419632445365505089931 3023129448668048257634897)
                ·
                  refine ⟨2267347086501036193226173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3023129448668048257634897 2267347086501036193226173)
                  ·
                    refine ⟨850255157437888572459815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2267347086501036193226173 850255157437888572459815)
                    ·
                      rfl

theorem cell22_2483799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 4, 1, 2, 3].length) (baseStart_2483799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2483799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2483799 prefixEnd_2483799 := by exact prefixLift 2483799
  have htrace : WordTrace (prefixWord ++ tailWord_2483799) baseStart_2483799 baseEnd_2483799 := by
    simpa [prefixWord, tailWord_2483799, baseEnd_2483799] using wordTrace_append hprefix tailTrace_2483799
  have hstable : (prefixWord ++ tailWord_2483799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2483799).length < 2 ^ (prefixWord ++ tailWord_2483799).sum := by decide
  have hdescent : baseEnd_2483799 < baseStart_2483799 := by decide
  rcases family_descends (prefixWord ++ tailWord_2483799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2483887 : List Nat := [1, 1, 2, 1, 2, 4, 3, 3, 1, 4]
def baseStart_2483887 : Nat := 118140960795 + 2483887 * 2 ^ 59
def prefixEnd_2483887 : Nat := 4983230072969 + 3 ^ 40 * 2483887 * 2
def baseEnd_2483887 : Nat := 850285281636285676259545

theorem tailTrace_2483887 : CollatzResearch.WordTrace tailWord_2483887 prefixEnd_2483887 850285281636285676259545 := by
  unfold tailWord_2483887
  simp only [CollatzResearch.WordTrace]
  refine ⟨90594801552309087971297915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60396534368206058647531943 90594801552309087971297915)
  ·
    refine ⟨135892202328463631956946873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90594801552309087971297915 135892202328463631956946873)
    ·
      refine ⟨101919151746347723967710155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135892202328463631956946873 101919151746347723967710155)
      ·
        refine ⟨152878727619521585951565233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101919151746347723967710155 152878727619521585951565233)
        ·
          refine ⟨114659045714641189463673925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152878727619521585951565233 114659045714641189463673925)
          ·
            refine ⟨21498571071495223024438861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 114659045714641189463673925 21498571071495223024438861)
            ·
              refine ⟨8061964151810708634164573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21498571071495223024438861 8061964151810708634164573)
              ·
                refine ⟨3023236556929015737811715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8061964151810708634164573 3023236556929015737811715)
                ·
                  refine ⟨4534854835393523606717573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3023236556929015737811715 4534854835393523606717573)
                  ·
                    refine ⟨850285281636285676259545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4534854835393523606717573 850285281636285676259545)
                    ·
                      rfl

theorem cell22_2483887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 3, 1, 4].length) (baseStart_2483887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2483887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2483887 prefixEnd_2483887 := by exact prefixLift 2483887
  have htrace : WordTrace (prefixWord ++ tailWord_2483887) baseStart_2483887 baseEnd_2483887 := by
    simpa [prefixWord, tailWord_2483887, baseEnd_2483887] using wordTrace_append hprefix tailTrace_2483887
  have hstable : (prefixWord ++ tailWord_2483887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2483887).length < 2 ^ (prefixWord ++ tailWord_2483887).sum := by decide
  have hdescent : baseEnd_2483887 < baseStart_2483887 := by decide
  rcases family_descends (prefixWord ++ tailWord_2483887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2483902 : List Nat := [4, 2, 1, 1, 2, 2, 1, 3, 6]
def baseStart_2483902 : Nat := 118140960795 + 2483902 * 2 ^ 59
def prefixEnd_2483902 : Nat := 4983230072969 + 3 ^ 40 * 2483902 * 2
def baseEnd_2483902 : Nat := 283430138814276879044833

theorem tailTrace_2483902 : CollatzResearch.WordTrace tailWord_2483902 prefixEnd_2483902 283430138814276879044833 := by
  unfold tailWord_2483902
  simp only [CollatzResearch.WordTrace]
  refine ⟨11324418580906843191636745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60396899098169830355395973 11324418580906843191636745)
  ·
    refine ⟨8493313935680132393727559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11324418580906843191636745 8493313935680132393727559)
    ·
      refine ⟨12739970903520198590591339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8493313935680132393727559 12739970903520198590591339)
      ·
        refine ⟨19109956355280297885887009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12739970903520198590591339 19109956355280297885887009)
        ·
          refine ⟨14332467266460223414415257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19109956355280297885887009 14332467266460223414415257)
          ·
            refine ⟨10749350449845167560811443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14332467266460223414415257 10749350449845167560811443)
            ·
              refine ⟨16124025674767751341217165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10749350449845167560811443 16124025674767751341217165)
              ·
                refine ⟨6046509628037906752956437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16124025674767751341217165 6046509628037906752956437)
                ·
                  refine ⟨283430138814276879044833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6046509628037906752956437 283430138814276879044833)
                  ·
                    rfl

theorem cell22_2483902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 3, 6].length) (baseStart_2483902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2483902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2483902 prefixEnd_2483902 := by exact prefixLift 2483902
  have htrace : WordTrace (prefixWord ++ tailWord_2483902) baseStart_2483902 baseEnd_2483902 := by
    simpa [prefixWord, tailWord_2483902, baseEnd_2483902] using wordTrace_append hprefix tailTrace_2483902
  have hstable : (prefixWord ++ tailWord_2483902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2483902).length < 2 ^ (prefixWord ++ tailWord_2483902).sum := by decide
  have hdescent : baseEnd_2483902 < baseStart_2483902 := by decide
  rcases family_descends (prefixWord ++ tailWord_2483902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2483949 : List Nat := [1, 5, 1, 2, 1, 3, 1, 2, 2, 4]
def baseStart_2483949 : Nat := 118140960795 + 2483949 * 2 ^ 59
def prefixEnd_2483949 : Nat := 4983230072969 + 3 ^ 40 * 2483949 * 2
def baseEnd_2483949 : Nat := 850306505503338181209355

theorem tailTrace_2483949 : CollatzResearch.WordTrace tailWord_2483949 prefixEnd_2483949 850306505503338181209355 := by
  unfold tailWord_2483949
  simp only [CollatzResearch.WordTrace]
  refine ⟨90597062878084472560054901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60398041918722981706703267 90597062878084472560054901)
  ·
    refine ⟨8493474644820419302505147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 90597062878084472560054901 8493474644820419302505147)
    ·
      refine ⟨12740211967230628953757721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8493474644820419302505147 12740211967230628953757721)
      ·
        refine ⟨9555158975422971715318291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12740211967230628953757721 9555158975422971715318291)
        ·
          refine ⟨14332738463134457572977437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9555158975422971715318291 14332738463134457572977437)
          ·
            refine ⟨5374776923675421589866539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14332738463134457572977437 5374776923675421589866539)
            ·
              refine ⟨8062165385513132384799809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5374776923675421589866539 8062165385513132384799809)
              ·
                refine ⟨6046624039134849288599857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8062165385513132384799809 6046624039134849288599857)
                ·
                  refine ⟨4534968029351136966449893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6046624039134849288599857 4534968029351136966449893)
                  ·
                    refine ⟨850306505503338181209355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4534968029351136966449893 850306505503338181209355)
                    ·
                      rfl

theorem cell22_2483949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 2, 2, 4].length) (baseStart_2483949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2483949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2483949 prefixEnd_2483949 := by exact prefixLift 2483949
  have htrace : WordTrace (prefixWord ++ tailWord_2483949) baseStart_2483949 baseEnd_2483949 := by
    simpa [prefixWord, tailWord_2483949, baseEnd_2483949] using wordTrace_append hprefix tailTrace_2483949
  have hstable : (prefixWord ++ tailWord_2483949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2483949).length < 2 ^ (prefixWord ++ tailWord_2483949).sum := by decide
  have hdescent : baseEnd_2483949 < baseStart_2483949 := by decide
  rcases family_descends (prefixWord ++ tailWord_2483949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2483996 : List Nat := [2, 2, 3, 1, 1, 2, 2, 5, 1, 3]
def baseStart_2483996 : Nat := 118140960795 + 2483996 * 2 ^ 59
def prefixEnd_2483996 : Nat := 4983230072969 + 3 ^ 40 * 2483996 * 2
def baseEnd_2483996 : Nat := 850322594563845725284211

theorem tailTrace_2483996 : CollatzResearch.WordTrace tailWord_2483996 prefixEnd_2483996 850322594563845725284211 := by
  unfold tailWord_2483996
  simp only [CollatzResearch.WordTrace]
  refine ⟨45299388554457099793507921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60399184739276133058010561 45299388554457099793507921)
  ·
    refine ⟨33974541415842824845130941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45299388554457099793507921 33974541415842824845130941)
    ·
      refine ⟨12740453030941059316924103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33974541415842824845130941 12740453030941059316924103)
      ·
        refine ⟨19110679546411588975386155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12740453030941059316924103 19110679546411588975386155)
        ·
          refine ⟨28666019319617383463079233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19110679546411588975386155 28666019319617383463079233)
          ·
            refine ⟨21499514489713037597309425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28666019319617383463079233 21499514489713037597309425)
            ·
              refine ⟨16124635867284778197982069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21499514489713037597309425 16124635867284778197982069)
              ·
                refine ⟨1511684612557947956060819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16124635867284778197982069 1511684612557947956060819)
                ·
                  refine ⟨2267526918836921934091229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1511684612557947956060819 2267526918836921934091229)
                  ·
                    refine ⟨850322594563845725284211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2267526918836921934091229 850322594563845725284211)
                    ·
                      rfl

theorem cell22_2483996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 5, 1, 3].length) (baseStart_2483996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2483996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2483996 prefixEnd_2483996 := by exact prefixLift 2483996
  have htrace : WordTrace (prefixWord ++ tailWord_2483996) baseStart_2483996 baseEnd_2483996 := by
    simpa [prefixWord, tailWord_2483996, baseEnd_2483996] using wordTrace_append hprefix tailTrace_2483996
  have hstable : (prefixWord ++ tailWord_2483996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2483996).length < 2 ^ (prefixWord ++ tailWord_2483996).sum := by decide
  have hdescent : baseEnd_2483996 < baseStart_2483996 := by decide
  rcases family_descends (prefixWord ++ tailWord_2483996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2484037 : List Nat := [1, 3, 1, 1, 1, 2, 5, 2, 6]
def baseStart_2484037 : Nat := 118140960795 + 2484037 * 2 ^ 59
def prefixEnd_2484037 : Nat := 4983230072969 + 3 ^ 40 * 2484037 * 2
def baseEnd_2484037 : Nat := 283445543233911761669695

theorem tailTrace_2484037 : CollatzResearch.WordTrace tailWord_2484037 prefixEnd_2484037 283445543233911761669695 := by
  unfold tailWord_2484037
  simp only [CollatzResearch.WordTrace]
  refine ⟨90600272501765663589258365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60400181667843775726172243 90600272501765663589258365)
  ·
    refine ⟨33975102188162123845971887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90600272501765663589258365 33975102188162123845971887)
    ·
      refine ⟨50962653282243185768957831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33975102188162123845971887 50962653282243185768957831)
      ·
        refine ⟨76443979923364778653436747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50962653282243185768957831 76443979923364778653436747)
        ·
          refine ⟨114665969885047167980155121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76443979923364778653436747 114665969885047167980155121)
          ·
            refine ⟨85999477413785375985116341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114665969885047167980155121 85999477413785375985116341)
            ·
              refine ⟨8062451007542378998604657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 85999477413785375985116341 8062451007542378998604657)
              ·
                refine ⟨6046838255656784248953493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8062451007542378998604657 6046838255656784248953493)
                ·
                  refine ⟨283445543233911761669695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6046838255656784248953493 283445543233911761669695)
                  ·
                    rfl

theorem cell22_2484037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 2, 6].length) (baseStart_2484037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2484037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2484037 prefixEnd_2484037 := by exact prefixLift 2484037
  have htrace : WordTrace (prefixWord ++ tailWord_2484037) baseStart_2484037 baseEnd_2484037 := by
    simpa [prefixWord, tailWord_2484037, baseEnd_2484037] using wordTrace_append hprefix tailTrace_2484037
  have hstable : (prefixWord ++ tailWord_2484037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2484037).length < 2 ^ (prefixWord ++ tailWord_2484037).sum := by decide
  have hdescent : baseEnd_2484037 < baseStart_2484037 := by decide
  rcases family_descends (prefixWord ++ tailWord_2484037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2484082 : List Nat := [3, 2, 1, 2, 1, 1, 1, 11]
def baseStart_2484082 : Nat := 118140960795 + 2484082 * 2 ^ 59
def prefixEnd_2484082 : Nat := 4983230072969 + 3 ^ 40 * 2484082 * 2
def baseEnd_2484082 : Nat := 94483559346818907514883

theorem tailTrace_2484082 : CollatzResearch.WordTrace tailWord_2484082 prefixEnd_2484082 94483559346818907514883 := by
  unfold tailWord_2484082
  simp only [CollatzResearch.WordTrace]
  refine ⟨22650478446650659068661625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60401275857735090849764333 22650478446650659068661625)
  ·
    refine ⟨16987858834987994301496219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22650478446650659068661625 16987858834987994301496219)
    ·
      refine ⟨25481788252481991452244329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16987858834987994301496219 25481788252481991452244329)
      ·
        refine ⟨19111341189361493589183247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25481788252481991452244329 19111341189361493589183247)
        ·
          refine ⟨28667011784042240383774871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19111341189361493589183247 28667011784042240383774871)
          ·
            refine ⟨43000517676063360575662307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28667011784042240383774871 43000517676063360575662307)
            ·
              refine ⟨64500776514095040863493461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43000517676063360575662307 64500776514095040863493461)
              ·
                refine ⟨94483559346818907514883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 64500776514095040863493461 94483559346818907514883)
                ·
                  rfl

theorem cell22_2484082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 11].length) (baseStart_2484082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2484082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2484082 prefixEnd_2484082 := by exact prefixLift 2484082
  have htrace : WordTrace (prefixWord ++ tailWord_2484082) baseStart_2484082 baseEnd_2484082 := by
    simpa [prefixWord, tailWord_2484082, baseEnd_2484082] using wordTrace_append hprefix tailTrace_2484082
  have hstable : (prefixWord ++ tailWord_2484082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2484082).length < 2 ^ (prefixWord ++ tailWord_2484082).sum := by decide
  have hdescent : baseEnd_2484082 < baseStart_2484082 := by decide
  rcases family_descends (prefixWord ++ tailWord_2484082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2484099 : List Nat := [1, 1, 1, 3, 4, 2, 4, 6]
def baseStart_2484099 : Nat := 118140960795 + 2484099 * 2 ^ 59
def prefixEnd_2484099 : Nat := 4983230072969 + 3 ^ 40 * 2484099 * 2
def baseEnd_2484099 : Nat := 94484205952087532217655

theorem tailTrace_2484099 : CollatzResearch.WordTrace tailWord_2484099 prefixEnd_2484099 94484205952087532217655 := by
  unfold tailWord_2484099
  simp only [CollatzResearch.WordTrace]
  refine ⟨90602533827541048178015351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60401689218360698785343567 90602533827541048178015351)
  ·
    refine ⟨135903800741311572267023027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90602533827541048178015351 135903800741311572267023027)
    ·
      refine ⟨203855701111967358400534541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135903800741311572267023027 203855701111967358400534541)
      ·
        refine ⟨76445887916987759400200453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 203855701111967358400534541 76445887916987759400200453)
        ·
          refine ⟨14333603984435204887537585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76445887916987759400200453 14333603984435204887537585)
          ·
            refine ⟨10750202988326403665653189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14333603984435204887537585 10750202988326403665653189)
            ·
              refine ⟨2015663060311200687309973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10750202988326403665653189 2015663060311200687309973)
              ·
                refine ⟨94484205952087532217655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2015663060311200687309973 94484205952087532217655)
                ·
                  rfl

theorem cell22_2484099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 4, 6].length) (baseStart_2484099 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2484099 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2484099 prefixEnd_2484099 := by exact prefixLift 2484099
  have htrace : WordTrace (prefixWord ++ tailWord_2484099) baseStart_2484099 baseEnd_2484099 := by
    simpa [prefixWord, tailWord_2484099, baseEnd_2484099] using wordTrace_append hprefix tailTrace_2484099
  have hstable : (prefixWord ++ tailWord_2484099).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2484099).length < 2 ^ (prefixWord ++ tailWord_2484099).sum := by decide
  have hdescent : baseEnd_2484099 < baseStart_2484099 := by decide
  rcases family_descends (prefixWord ++ tailWord_2484099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2484178 : List Nat := [3, 2, 2, 3, 2, 1, 2, 2, 5]
def baseStart_2484178 : Nat := 118140960795 + 2484178 * 2 ^ 59
def prefixEnd_2484178 : Nat := 4983230072969 + 3 ^ 40 * 2484178 * 2
def baseEnd_2484178 : Nat := 283461632294419305744551

theorem tailTrace_2484178 : CollatzResearch.WordTrace tailWord_2484178 prefixEnd_2484178 283461632294419305744551 := by
  unfold tailWord_2484178
  simp only [CollatzResearch.WordTrace]
  refine ⟨22651353798563711167535297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60403610129503229780094125 22651353798563711167535297)
  ·
    refine ⟨16988515348922783375651473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22651353798563711167535297 16988515348922783375651473)
    ·
      refine ⟨12741386511692087531738605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16988515348922783375651473 12741386511692087531738605)
      ·
        refine ⟨4778019941884532824401977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12741386511692087531738605 4778019941884532824401977)
        ·
          refine ⟨3583514956413399618301483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4778019941884532824401977 3583514956413399618301483)
          ·
            refine ⟨5375272434620099427452225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3583514956413399618301483 5375272434620099427452225)
            ·
              refine ⟨4031454325965074570589169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5375272434620099427452225 4031454325965074570589169)
              ·
                refine ⟨3023590744473805927941877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4031454325965074570589169 3023590744473805927941877)
                ·
                  refine ⟨283461632294419305744551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3023590744473805927941877 283461632294419305744551)
                  ·
                    rfl

theorem cell22_2484178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 2, 5].length) (baseStart_2484178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2484178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2484178 prefixEnd_2484178 := by exact prefixLift 2484178
  have htrace : WordTrace (prefixWord ++ tailWord_2484178) baseStart_2484178 baseEnd_2484178 := by
    simpa [prefixWord, tailWord_2484178, baseEnd_2484178] using wordTrace_append hprefix tailTrace_2484178
  have hstable : (prefixWord ++ tailWord_2484178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2484178).length < 2 ^ (prefixWord ++ tailWord_2484178).sum := by decide
  have hdescent : baseEnd_2484178 < baseStart_2484178 := by decide
  rcases family_descends (prefixWord ++ tailWord_2484178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2484182 : List Nat := [5, 2, 1, 1, 3, 1, 1, 4, 1, 3]
def baseStart_2484182 : Nat := 118140960795 + 2484182 * 2 ^ 59
def prefixEnd_2484182 : Nat := 4983230072969 + 3 ^ 40 * 2484182 * 2
def baseEnd_2484182 : Nat := 850386266165003240133641

theorem tailTrace_2484182 : CollatzResearch.WordTrace tailWord_2484182 prefixEnd_2484182 850386266165003240133641 := by
  unfold tailWord_2484182
  simp only [CollatzResearch.WordTrace]
  refine ⟨5662847567890022084580425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 60403707390826902235524533 5662847567890022084580425)
  ·
    refine ⟨4247135675917516563435319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5662847567890022084580425 4247135675917516563435319)
    ·
      refine ⟨6370703513876274845152979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4247135675917516563435319 6370703513876274845152979)
      ·
        refine ⟨9556055270814412267729469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6370703513876274845152979 9556055270814412267729469)
        ·
          refine ⟨3583520726555404600398551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9556055270814412267729469 3583520726555404600398551)
          ·
            refine ⟨5375281089833106900597827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3583520726555404600398551 5375281089833106900597827)
            ·
              refine ⟨8062921634749660350896741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5375281089833106900597827 8062921634749660350896741)
              ·
                refine ⟨1511797806515561315793139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8062921634749660350896741 1511797806515561315793139)
                ·
                  refine ⟨2267696709773341973689709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1511797806515561315793139 2267696709773341973689709)
                  ·
                    refine ⟨850386266165003240133641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2267696709773341973689709 850386266165003240133641)
                    ·
                      rfl

theorem cell22_2484182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 4, 1, 3].length) (baseStart_2484182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2484182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2484182 prefixEnd_2484182 := by exact prefixLift 2484182
  have htrace : WordTrace (prefixWord ++ tailWord_2484182) baseStart_2484182 baseEnd_2484182 := by
    simpa [prefixWord, tailWord_2484182, baseEnd_2484182] using wordTrace_append hprefix tailTrace_2484182
  have hstable : (prefixWord ++ tailWord_2484182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2484182).length < 2 ^ (prefixWord ++ tailWord_2484182).sum := by decide
  have hdescent : baseEnd_2484182 < baseStart_2484182 := by decide
  rcases family_descends (prefixWord ++ tailWord_2484182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2484206 : List Nat := [4, 1, 2, 1, 3, 2, 1, 2, 6]
def baseStart_2484206 : Nat := 118140960795 + 2484206 * 2 ^ 59
def prefixEnd_2484206 : Nat := 4983230072969 + 3 ^ 40 * 2484206 * 2
def baseEnd_2484206 : Nat := 283464827285158392511189

theorem tailTrace_2484206 : CollatzResearch.WordTrace tailWord_2484206 prefixEnd_2484206 283464827285158392511189 := by
  unfold tailWord_2484206
  simp only [CollatzResearch.WordTrace]
  refine ⟨11325804554769175681520059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60404290958768936968106981 11325804554769175681520059)
  ·
    refine ⟨16988706832153763522280089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11325804554769175681520059 16988706832153763522280089)
    ·
      refine ⟨12741530124115322641710067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16988706832153763522280089 12741530124115322641710067)
      ·
        refine ⟨19112295186172983962565101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12741530124115322641710067 19112295186172983962565101)
        ·
          refine ⟨7167110694814868985961913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19112295186172983962565101 7167110694814868985961913)
          ·
            refine ⟨5375333021111151739471435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7167110694814868985961913 5375333021111151739471435)
            ·
              refine ⟨8062999531666727609207153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5375333021111151739471435 8062999531666727609207153)
              ·
                refine ⟨6047249648750045706905365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8062999531666727609207153 6047249648750045706905365)
                ·
                  refine ⟨283464827285158392511189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6047249648750045706905365 283464827285158392511189)
                  ·
                    rfl

theorem cell22_2484206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 2, 6].length) (baseStart_2484206 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2484206 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2484206 prefixEnd_2484206 := by exact prefixLift 2484206
  have htrace : WordTrace (prefixWord ++ tailWord_2484206) baseStart_2484206 baseEnd_2484206 := by
    simpa [prefixWord, tailWord_2484206, baseEnd_2484206] using wordTrace_append hprefix tailTrace_2484206
  have hstable : (prefixWord ++ tailWord_2484206).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2484206).length < 2 ^ (prefixWord ++ tailWord_2484206).sum := by decide
  have hdescent : baseEnd_2484206 < baseStart_2484206 := by decide
  rcases family_descends (prefixWord ++ tailWord_2484206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2484279 : List Nat := [1, 1, 3, 1, 2, 2, 3, 2, 7]
def baseStart_2484279 : Nat := 118140960795 + 2484279 * 2 ^ 59
def prefixEnd_2484279 : Nat := 4983230072969 + 3 ^ 40 * 2484279 * 2
def baseEnd_2484279 : Nat := 283473157082442440152781

theorem tailTrace_2484279 : CollatzResearch.WordTrace tailWord_2484279 prefixEnd_2484279 283473157082442440152781 := by
  unfold tailWord_2484279
  simp only [CollatzResearch.WordTrace]
  refine ⟨90609098966888938919567891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60406065977925959279711927 90609098966888938919567891)
  ·
    refine ⟨135913648450333408379351837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90609098966888938919567891 135913648450333408379351837)
    ·
      refine ⟨50967618168875028142256939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135913648450333408379351837 50967618168875028142256939)
      ·
        refine ⟨76451427253312542213385409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50967618168875028142256939 76451427253312542213385409)
        ·
          refine ⟨57338570439984406660039057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76451427253312542213385409 57338570439984406660039057)
          ·
            refine ⟨43003927829988304995029293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57338570439984406660039057 43003927829988304995029293)
            ·
              refine ⟨16126472936245614373135985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43003927829988304995029293 16126472936245614373135985)
              ·
                refine ⟨12094854702184210779851989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16126472936245614373135985 12094854702184210779851989)
                ·
                  refine ⟨283473157082442440152781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12094854702184210779851989 283473157082442440152781)
                  ·
                    rfl

theorem cell22_2484279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 2, 7].length) (baseStart_2484279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2484279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2484279 prefixEnd_2484279 := by exact prefixLift 2484279
  have htrace : WordTrace (prefixWord ++ tailWord_2484279) baseStart_2484279 baseEnd_2484279 := by
    simpa [prefixWord, tailWord_2484279, baseEnd_2484279] using wordTrace_append hprefix tailTrace_2484279
  have hstable : (prefixWord ++ tailWord_2484279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2484279).length < 2 ^ (prefixWord ++ tailWord_2484279).sum := by decide
  have hdescent : baseEnd_2484279 < baseStart_2484279 := by decide
  rcases family_descends (prefixWord ++ tailWord_2484279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2484356 : List Nat := [2, 3, 2, 1, 2, 1, 1, 2, 3, 5]
def baseStart_2484356 : Nat := 118140960795 + 2484356 * 2 ^ 59
def prefixEnd_2484356 : Nat := 4983230072969 + 3 ^ 40 * 2484356 * 2
def baseEnd_2484356 : Nat := 850445829920924786283107

theorem tailTrace_2484356 : CollatzResearch.WordTrace tailWord_2484356 prefixEnd_2484356 850445829920924786283107 := by
  unfold tailWord_2484356
  simp only [CollatzResearch.WordTrace]
  refine ⟨45305953693804990535060461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60407938258406654046747281 45305953693804990535060461)
  ·
    refine ⟨16989732635176871450647673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45305953693804990535060461 16989732635176871450647673)
    ·
      refine ⟨12742299476382653587985755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16989732635176871450647673 12742299476382653587985755)
      ·
        refine ⟨19113449214573980381978633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12742299476382653587985755 19113449214573980381978633)
        ·
          refine ⟨14335086910930485286483975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19113449214573980381978633 14335086910930485286483975)
          ·
            refine ⟨21502630366395727929725963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14335086910930485286483975 21502630366395727929725963)
            ·
              refine ⟨32253945549593591894588945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21502630366395727929725963 32253945549593591894588945)
              ·
                refine ⟨24190459162195193920941709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32253945549593591894588945 24190459162195193920941709)
                ·
                  refine ⟨9071422185823197720353141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24190459162195193920941709 9071422185823197720353141)
                  ·
                    refine ⟨850445829920924786283107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9071422185823197720353141 850445829920924786283107)
                    ·
                      rfl

theorem cell22_2484356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_2484356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2484356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2484356 prefixEnd_2484356 := by exact prefixLift 2484356
  have htrace : WordTrace (prefixWord ++ tailWord_2484356) baseStart_2484356 baseEnd_2484356 := by
    simpa [prefixWord, tailWord_2484356, baseEnd_2484356] using wordTrace_append hprefix tailTrace_2484356
  have hstable : (prefixWord ++ tailWord_2484356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2484356).length < 2 ^ (prefixWord ++ tailWord_2484356).sum := by decide
  have hdescent : baseEnd_2484356 < baseStart_2484356 := by decide
  rcases family_descends (prefixWord ++ tailWord_2484356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2484373 : List Nat := [1, 3, 2, 1, 1, 1, 3, 5, 2, 3]
def baseStart_2484373 : Nat := 118140960795 + 2484373 * 2 ^ 59
def prefixEnd_2484373 : Nat := 4983230072969 + 3 ^ 40 * 2484373 * 2
def baseEnd_2484373 : Nat := 850451649368342408608055

theorem tailTrace_2484373 : CollatzResearch.WordTrace tailWord_2484373 prefixEnd_2484373 850451649368342408608055 := by
  unfold tailWord_2484373
  simp only [CollatzResearch.WordTrace]
  refine ⟨90612527428548392973489773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60408351619032261982326515 90612527428548392973489773)
  ·
    refine ⟨33979697785705647365058665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90612527428548392973489773 33979697785705647365058665)
    ·
      refine ⟨25484773339279235523793999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33979697785705647365058665 25484773339279235523793999)
      ·
        refine ⟨38227160008918853285690999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25484773339279235523793999 38227160008918853285690999)
        ·
          refine ⟨57340740013378279928536499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38227160008918853285690999 57340740013378279928536499)
          ·
            refine ⟨86011110020067419892804749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57340740013378279928536499 86011110020067419892804749)
            ·
              refine ⟨32254166257525282459801781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86011110020067419892804749 32254166257525282459801781)
              ·
                refine ⟨3023828086642995230606417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32254166257525282459801781 3023828086642995230606417)
                ·
                  refine ⟨2267871064982246422954813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3023828086642995230606417 2267871064982246422954813)
                  ·
                    refine ⟨850451649368342408608055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2267871064982246422954813 850451649368342408608055)
                    ·
                      rfl

theorem cell22_2484373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 5, 2, 3].length) (baseStart_2484373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2484373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2484373 prefixEnd_2484373 := by exact prefixLift 2484373
  have htrace : WordTrace (prefixWord ++ tailWord_2484373) baseStart_2484373 baseEnd_2484373 := by
    simpa [prefixWord, tailWord_2484373, baseEnd_2484373] using wordTrace_append hprefix tailTrace_2484373
  have hstable : (prefixWord ++ tailWord_2484373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2484373).length < 2 ^ (prefixWord ++ tailWord_2484373).sum := by decide
  have hdescent : baseEnd_2484373 < baseStart_2484373 := by decide
  rcases family_descends (prefixWord ++ tailWord_2484373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2484388 : List Nat := [2, 3, 1, 2, 4, 1, 1, 1, 1, 6]
def baseStart_2484388 : Nat := 118140960795 + 2484388 * 2 ^ 59
def prefixEnd_2484388 : Nat := 4983230072969 + 3 ^ 40 * 2484388 * 2
def baseEnd_2484388 : Nat := 850456784174887369483009

theorem tailTrace_2484388 : CollatzResearch.WordTrace tailWord_2484388 prefixEnd_2484388 850456784174887369483009 := by
  unfold tailWord_2484388
  simp only [CollatzResearch.WordTrace]
  refine ⟨45306537261747025267642909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60408716348996033690190545 45306537261747025267642909)
  ·
    refine ⟨16989951473155134475366091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45306537261747025267642909 16989951473155134475366091)
    ·
      refine ⟨25484927209732701713049137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16989951473155134475366091 25484927209732701713049137)
      ·
        refine ⟨19113695407299526284786853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25484927209732701713049137 19113695407299526284786853)
        ·
          refine ⟨3583817888868661178397535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19113695407299526284786853 3583817888868661178397535)
          ·
            refine ⟨5375726833302991767596303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3583817888868661178397535 5375726833302991767596303)
            ·
              refine ⟨8063590249954487651394455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5375726833302991767596303 8063590249954487651394455)
              ·
                refine ⟨12095385374931731477091683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8063590249954487651394455 12095385374931731477091683)
                ·
                  refine ⟨18143078062397597215637525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12095385374931731477091683 18143078062397597215637525)
                  ·
                    refine ⟨850456784174887369483009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18143078062397597215637525 850456784174887369483009)
                    ·
                      rfl

theorem cell22_2484388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 1, 1, 6].length) (baseStart_2484388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2484388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2484388 prefixEnd_2484388 := by exact prefixLift 2484388
  have htrace : WordTrace (prefixWord ++ tailWord_2484388) baseStart_2484388 baseEnd_2484388 := by
    simpa [prefixWord, tailWord_2484388, baseEnd_2484388] using wordTrace_append hprefix tailTrace_2484388
  have hstable : (prefixWord ++ tailWord_2484388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2484388).length < 2 ^ (prefixWord ++ tailWord_2484388).sum := by decide
  have hdescent : baseEnd_2484388 < baseStart_2484388 := by decide
  rcases family_descends (prefixWord ++ tailWord_2484388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2484394 : List Nat := [3, 1, 5, 1, 2, 2, 2, 1, 1, 4]
def baseStart_2484394 : Nat := 118140960795 + 2484394 * 2 ^ 59
def prefixEnd_2484394 : Nat := 4983230072969 + 3 ^ 40 * 2484394 * 2
def baseEnd_2484394 : Nat := 850458838097505353832991

theorem tailTrace_2484394 : CollatzResearch.WordTrace tailWord_2484394 prefixEnd_2484394 850458838097505353832991 := by
  unfold tailWord_2484394
  simp only [CollatzResearch.WordTrace]
  refine ⟨22653323340368078390001059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60408862240981542373336157 22653323340368078390001059)
  ·
    refine ⟨33979985010552117585001589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22653323340368078390001059 33979985010552117585001589)
    ·
      refine ⟨3185623594739261023593899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33979985010552117585001589 3185623594739261023593899)
      ·
        refine ⟨4778435392108891535390849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3185623594739261023593899 4778435392108891535390849)
        ·
          refine ⟨3583826544081668651543137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4778435392108891535390849 3583826544081668651543137)
          ·
            refine ⟨2687869908061251488657353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3583826544081668651543137 2687869908061251488657353)
            ·
              refine ⟨2015902431045938616493015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2687869908061251488657353 2015902431045938616493015)
              ·
                refine ⟨3023853646568907924739523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2015902431045938616493015 3023853646568907924739523)
                ·
                  refine ⟨4535780469853361887109285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3023853646568907924739523 4535780469853361887109285)
                  ·
                    refine ⟨850458838097505353832991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4535780469853361887109285 850458838097505353832991)
                    ·
                      rfl

theorem cell22_2484394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_2484394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2484394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2484394 prefixEnd_2484394 := by exact prefixLift 2484394
  have htrace : WordTrace (prefixWord ++ tailWord_2484394) baseStart_2484394 baseEnd_2484394 := by
    simpa [prefixWord, tailWord_2484394, baseEnd_2484394] using wordTrace_append hprefix tailTrace_2484394
  have hstable : (prefixWord ++ tailWord_2484394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2484394).length < 2 ^ (prefixWord ++ tailWord_2484394).sum := by decide
  have hdescent : baseEnd_2484394 < baseStart_2484394 := by decide
  rcases family_descends (prefixWord ++ tailWord_2484394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2484437 : List Nat := [1, 3, 2, 4, 3, 1, 2, 6]
def baseStart_2484437 : Nat := 118140960795 + 2484437 * 2 ^ 59
def prefixEnd_2484437 : Nat := 4983230072969 + 3 ^ 40 * 2484437 * 2
def baseEnd_2484437 : Nat := 94497061986251952778651

theorem tailTrace_2484437 : CollatzResearch.WordTrace tailWord_2484437 prefixEnd_2484437 94497061986251952778651 := by
  unfold tailWord_2484437
  simp only [CollatzResearch.WordTrace]
  refine ⟨90614861700316531903819565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60409907800211021269213043 90614861700316531903819565)
  ·
    refine ⟨33980573137618699463932337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90614861700316531903819565 33980573137618699463932337)
    ·
      refine ⟨25485429853214024597949253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33980573137618699463932337 25485429853214024597949253)
      ·
        refine ⟨4778518097477629612115485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25485429853214024597949253 4778518097477629612115485)
        ·
          refine ⟨1791944286554111104543307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4778518097477629612115485 1791944286554111104543307)
          ·
            refine ⟨2687916429831166656814961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1791944286554111104543307 2687916429831166656814961)
            ·
              refine ⟨2015937322373374992611221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2687916429831166656814961 2015937322373374992611221)
              ·
                refine ⟨94497061986251952778651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2015937322373374992611221 94497061986251952778651)
                ·
                  rfl

theorem cell22_2484437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 2, 6].length) (baseStart_2484437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2484437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2484437 prefixEnd_2484437 := by exact prefixLift 2484437
  have htrace : WordTrace (prefixWord ++ tailWord_2484437) baseStart_2484437 baseEnd_2484437 := by
    simpa [prefixWord, tailWord_2484437, baseEnd_2484437] using wordTrace_append hprefix tailTrace_2484437
  have hstable : (prefixWord ++ tailWord_2484437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2484437).length < 2 ^ (prefixWord ++ tailWord_2484437).sum := by decide
  have hdescent : baseEnd_2484437 < baseStart_2484437 := by decide
  rcases family_descends (prefixWord ++ tailWord_2484437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2484482 : List Nat := [3, 4, 1, 1, 2, 1, 4, 1, 5]
def baseStart_2484482 : Nat := 118140960795 + 2484482 * 2 ^ 59
def prefixEnd_2484482 : Nat := 4983230072969 + 3 ^ 40 * 2484482 * 2
def baseEnd_2484482 : Nat := 283496320765300819210907

theorem tailTrace_2484482 : CollatzResearch.WordTrace tailWord_2484482 prefixEnd_2484482 283496320765300819210907 := by
  unfold tailWord_2484482
  simp only [CollatzResearch.WordTrace]
  refine ⟨22654125746288376147301925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60411001990102336392805133 22654125746288376147301925)
  ·
    refine ⟨4247648577429070527619111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22654125746288376147301925 4247648577429070527619111)
    ·
      refine ⟨6371472866143605791428667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4247648577429070527619111 6371472866143605791428667)
      ·
        refine ⟨9557209299215408687143001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6371472866143605791428667 9557209299215408687143001)
        ·
          refine ⟨7167906974411556515357251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9557209299215408687143001 7167906974411556515357251)
          ·
            refine ⟨10751860461617334773035877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7167906974411556515357251 10751860461617334773035877)
            ·
              refine ⟨2015973836553250269944227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10751860461617334773035877 2015973836553250269944227)
              ·
                refine ⟨3023960754829875404916341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2015973836553250269944227 3023960754829875404916341)
                ·
                  refine ⟨283496320765300819210907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3023960754829875404916341 283496320765300819210907)
                  ·
                    rfl

theorem cell22_2484482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 4, 1, 5].length) (baseStart_2484482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2484482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2484482 prefixEnd_2484482 := by exact prefixLift 2484482
  have htrace : WordTrace (prefixWord ++ tailWord_2484482) baseStart_2484482 baseEnd_2484482 := by
    simpa [prefixWord, tailWord_2484482, baseEnd_2484482] using wordTrace_append hprefix tailTrace_2484482
  have hstable : (prefixWord ++ tailWord_2484482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2484482).length < 2 ^ (prefixWord ++ tailWord_2484482).sum := by decide
  have hdescent : baseEnd_2484482 < baseStart_2484482 := by decide
  rcases family_descends (prefixWord ++ tailWord_2484482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2484512 : List Nat := [2, 1, 1, 5, 2, 2, 3, 1, 1, 4]
def baseStart_2484512 : Nat := 118140960795 + 2484512 * 2 ^ 59
def prefixEnd_2484512 : Nat := 4983230072969 + 3 ^ 40 * 2484512 * 2
def baseEnd_2484512 : Nat := 850499231908992379382629

theorem tailTrace_2484512 : CollatzResearch.WordTrace tailWord_2484512 prefixEnd_2484512 850499231908992379382629 := by
  unfold tailWord_2484512
  simp only [CollatzResearch.WordTrace]
  refine ⟨45308798587522409856399895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60411731450029879808533193 45308798587522409856399895)
  ·
    refine ⟨67963197881283614784599843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45308798587522409856399895 67963197881283614784599843)
    ·
      refine ⟨101944796821925422176899765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67963197881283614784599843 101944796821925422176899765)
      ·
        refine ⟨9557324702055508329084353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 101944796821925422176899765 9557324702055508329084353)
        ·
          refine ⟨7167993526541631246813265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9557324702055508329084353 7167993526541631246813265)
          ·
            refine ⟨5375995144906223435109949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7167993526541631246813265 5375995144906223435109949)
            ·
              refine ⟨2015998179339833788166231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5375995144906223435109949 2015998179339833788166231)
              ·
                refine ⟨3023997269009750682249347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2015998179339833788166231 3023997269009750682249347)
                ·
                  refine ⟨4535995903514626023374021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3023997269009750682249347 4535995903514626023374021)
                  ·
                    refine ⟨850499231908992379382629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4535995903514626023374021 850499231908992379382629)
                    ·
                      rfl

theorem cell22_2484512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 3, 1, 1, 4].length) (baseStart_2484512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2484512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2484512 prefixEnd_2484512 := by exact prefixLift 2484512
  have htrace : WordTrace (prefixWord ++ tailWord_2484512) baseStart_2484512 baseEnd_2484512 := by
    simpa [prefixWord, tailWord_2484512, baseEnd_2484512] using wordTrace_append hprefix tailTrace_2484512
  have hstable : (prefixWord ++ tailWord_2484512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2484512).length < 2 ^ (prefixWord ++ tailWord_2484512).sum := by decide
  have hdescent : baseEnd_2484512 < baseStart_2484512 := by decide
  rcases family_descends (prefixWord ++ tailWord_2484512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2484538 : List Nat := [3, 1, 1, 1, 4, 2, 3, 7]
def baseStart_2484538 : Nat := 118140960795 + 2484538 * 2 ^ 59
def prefixEnd_2484538 : Nat := 4983230072969 + 3 ^ 40 * 2484538 * 2
def baseEnd_2484538 : Nat := 94500903582259664248061

theorem tailTrace_2484538 : CollatzResearch.WordTrace tailWord_2484538 prefixEnd_2484538 94500903582259664248061 := by
  unfold tailWord_2484538
  simp only [CollatzResearch.WordTrace]
  refine ⟨22654636368237656538311567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60412363648633750768830845 22654636368237656538311567)
  ·
    refine ⟨33981954552356484807467351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22654636368237656538311567 33981954552356484807467351)
    ·
      refine ⟨50972931828534727211201027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33981954552356484807467351 50972931828534727211201027)
      ·
        refine ⟨76459397742802090816801541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50972931828534727211201027 76459397742802090816801541)
        ·
          refine ⟨14336137076775392028150289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76459397742802090816801541 14336137076775392028150289)
          ·
            refine ⟨10752102807581544021112717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14336137076775392028150289 10752102807581544021112717)
            ·
              refine ⟨4032038552843079007917269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10752102807581544021112717 4032038552843079007917269)
              ·
                refine ⟨94500903582259664248061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4032038552843079007917269 94500903582259664248061)
                ·
                  rfl

theorem cell22_2484538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 7].length) (baseStart_2484538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2484538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2484538 prefixEnd_2484538 := by exact prefixLift 2484538
  have htrace : WordTrace (prefixWord ++ tailWord_2484538) baseStart_2484538 baseEnd_2484538 := by
    simpa [prefixWord, tailWord_2484538, baseEnd_2484538] using wordTrace_append hprefix tailTrace_2484538
  have hstable : (prefixWord ++ tailWord_2484538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2484538).length < 2 ^ (prefixWord ++ tailWord_2484538).sum := by decide
  have hdescent : baseEnd_2484538 < baseStart_2484538 := by decide
  rcases family_descends (prefixWord ++ tailWord_2484538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2484542 : List Nat := [4, 2, 1, 2, 1, 2, 2, 3, 2, 3]
def baseStart_2484542 : Nat := 118140960795 + 2484542 * 2 ^ 59
def prefixEnd_2484542 : Nat := 4983230072969 + 3 ^ 40 * 2484542 * 2
def baseEnd_2484542 : Nat := 850509501522082301132537

theorem tailTrace_2484542 : CollatzResearch.WordTrace tailWord_2484542 prefixEnd_2484542 850509501522082301132537 := by
  unfold tailWord_2484542
  simp only [CollatzResearch.WordTrace]
  refine ⟨11327336420617016854548985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60412460909957423224261253 11327336420617016854548985)
  ·
    refine ⟨8495502315462762640911739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11327336420617016854548985 8495502315462762640911739)
    ·
      refine ⟨12743253473194143961367609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8495502315462762640911739 12743253473194143961367609)
      ·
        refine ⟨9557440104895607971025707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12743253473194143961367609 9557440104895607971025707)
        ·
          refine ⟨14336160157343411956538561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9557440104895607971025707 14336160157343411956538561)
          ·
            refine ⟨10752120118007558967403921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14336160157343411956538561 10752120118007558967403921)
            ·
              refine ⟨8064090088505669225552941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10752120118007558967403921 8064090088505669225552941)
              ·
                refine ⟨3024033783189625959582353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8064090088505669225552941 3024033783189625959582353)
                ·
                  refine ⟨2268025337392219469686765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3024033783189625959582353 2268025337392219469686765)
                  ·
                    refine ⟨850509501522082301132537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2268025337392219469686765 850509501522082301132537)
                    ·
                      rfl

theorem cell22_2484542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 3, 2, 3].length) (baseStart_2484542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2484542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2484542 prefixEnd_2484542 := by exact prefixLift 2484542
  have htrace : WordTrace (prefixWord ++ tailWord_2484542) baseStart_2484542 baseEnd_2484542 := by
    simpa [prefixWord, tailWord_2484542, baseEnd_2484542] using wordTrace_append hprefix tailTrace_2484542
  have hstable : (prefixWord ++ tailWord_2484542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2484542).length < 2 ^ (prefixWord ++ tailWord_2484542).sum := by decide
  have hdescent : baseEnd_2484542 < baseStart_2484542 := by decide
  rcases family_descends (prefixWord ++ tailWord_2484542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2484638 : List Nat := [4, 3, 1, 2, 1, 2, 3, 2, 1, 3]
def baseStart_2484638 : Nat := 118140960795 + 2484638 * 2 ^ 59
def prefixEnd_2484638 : Nat := 4983230072969 + 3 ^ 40 * 2484638 * 2
def baseEnd_2484638 : Nat := 850542364283970050732243

theorem tailTrace_2484638 : CollatzResearch.WordTrace tailWord_2484638 prefixEnd_2484638 850542364283970050732243 := by
  unfold tailWord_2484638
  simp only [CollatzResearch.WordTrace]
  refine ⟨11327774096573542903985821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60414795181725562154591045 11327774096573542903985821)
  ·
    refine ⟨4247915286215078588994683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11327774096573542903985821 4247915286215078588994683)
    ·
      refine ⟨6371872929322617883492025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4247915286215078588994683 6371872929322617883492025)
      ·
        refine ⟨4778904696991963412619019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6371872929322617883492025 4778904696991963412619019)
        ·
          refine ⟨7168357045487945118928529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4778904696991963412619019 7168357045487945118928529)
          ·
            refine ⟨5376267784115958839196397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7168357045487945118928529 5376267784115958839196397)
            ·
              refine ⟨2016100419043484564698649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5376267784115958839196397 2016100419043484564698649)
              ·
                refine ⟨1512075314282613423523987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2016100419043484564698649 1512075314282613423523987)
                ·
                  refine ⟨2268112971423920135285981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1512075314282613423523987 2268112971423920135285981)
                  ·
                    refine ⟨850542364283970050732243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2268112971423920135285981 850542364283970050732243)
                    ·
                      rfl

theorem cell22_2484638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 3, 2, 1, 3].length) (baseStart_2484638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2484638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2484638 prefixEnd_2484638 := by exact prefixLift 2484638
  have htrace : WordTrace (prefixWord ++ tailWord_2484638) baseStart_2484638 baseEnd_2484638 := by
    simpa [prefixWord, tailWord_2484638, baseEnd_2484638] using wordTrace_append hprefix tailTrace_2484638
  have hstable : (prefixWord ++ tailWord_2484638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2484638).length < 2 ^ (prefixWord ++ tailWord_2484638).sum := by decide
  have hdescent : baseEnd_2484638 < baseStart_2484638 := by decide
  rcases family_descends (prefixWord ++ tailWord_2484638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2484690 : List Nat := [3, 2, 2, 4, 11]
def baseStart_2484690 : Nat := 118140960795 + 2484690 * 2 ^ 59
def prefixEnd_2484690 : Nat := 4983230072969 + 3 ^ 40 * 2484690 * 2
def baseEnd_2484690 : Nat := 3500247592373083326881

theorem tailTrace_2484690 : CollatzResearch.WordTrace tailWord_2484690 prefixEnd_2484690 3500247592373083326881 := by
  unfold tailWord_2484690
  simp only [CollatzResearch.WordTrace]
  refine ⟨22656022342099989028194881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60416059578933304075186349 22656022342099989028194881)
  ·
    refine ⟨16992016756574991771146161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22656022342099989028194881 16992016756574991771146161)
    ·
      refine ⟨12744012567431243828359621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16992016756574991771146161 12744012567431243828359621)
      ·
        refine ⟨2389502356393358217817429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12744012567431243828359621 2389502356393358217817429)
        ·
          refine ⟨3500247592373083326881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 2389502356393358217817429 3500247592373083326881)
          ·
            rfl

theorem cell22_2484690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 11].length) (baseStart_2484690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2484690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2484690 prefixEnd_2484690 := by exact prefixLift 2484690
  have htrace : WordTrace (prefixWord ++ tailWord_2484690) baseStart_2484690 baseEnd_2484690 := by
    simpa [prefixWord, tailWord_2484690, baseEnd_2484690] using wordTrace_append hprefix tailTrace_2484690
  have hstable : (prefixWord ++ tailWord_2484690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2484690).length < 2 ^ (prefixWord ++ tailWord_2484690).sum := by decide
  have hdescent : baseEnd_2484690 < baseStart_2484690 := by decide
  rcases family_descends (prefixWord ++ tailWord_2484690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2484692 : List Nat := [2, 4, 1, 2, 2, 1, 2, 2, 2, 4]
def baseStart_2484692 : Nat := 118140960795 + 2484692 * 2 ^ 59
def prefixEnd_2484692 : Nat := 4983230072969 + 3 ^ 40 * 2484692 * 2
def baseEnd_2484692 : Nat := 850560849587531909882077

theorem tailTrace_2484692 : CollatzResearch.WordTrace tailWord_2484692 prefixEnd_2484692 850560849587531909882077 := by
  unfold tailWord_2484692
  simp only [CollatzResearch.WordTrace]
  refine ⟨45312081157196355227176165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60416108209595140302901553 45312081157196355227176165)
  ·
    refine ⟨8496015216974316605095531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45312081157196355227176165 8496015216974316605095531)
    ·
      refine ⟨12744022825461474907643297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8496015216974316605095531 12744022825461474907643297)
      ·
        refine ⟨9558017119096106180732473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12744022825461474907643297 9558017119096106180732473)
        ·
          refine ⟨7168512839322079635549355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9558017119096106180732473 7168512839322079635549355)
          ·
            refine ⟨10752769258983119453324033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7168512839322079635549355 10752769258983119453324033)
            ·
              refine ⟨8064576944237339589993025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10752769258983119453324033 8064576944237339589993025)
              ·
                refine ⟨6048432708178004692494769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8064576944237339589993025 6048432708178004692494769)
                ·
                  refine ⟨4536324531133503519371077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6048432708178004692494769 4536324531133503519371077)
                  ·
                    refine ⟨850560849587531909882077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4536324531133503519371077 850560849587531909882077)
                    ·
                      rfl

theorem cell22_2484692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 2, 2, 4].length) (baseStart_2484692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2484692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2484692 prefixEnd_2484692 := by exact prefixLift 2484692
  have htrace : WordTrace (prefixWord ++ tailWord_2484692) baseStart_2484692 baseEnd_2484692 := by
    simpa [prefixWord, tailWord_2484692, baseEnd_2484692] using wordTrace_append hprefix tailTrace_2484692
  have hstable : (prefixWord ++ tailWord_2484692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2484692).length < 2 ^ (prefixWord ++ tailWord_2484692).sum := by decide
  have hdescent : baseEnd_2484692 < baseStart_2484692 := by decide
  rcases family_descends (prefixWord ++ tailWord_2484692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2484707 : List Nat := [1, 1, 1, 6, 3, 2, 1, 7]
def baseStart_2484707 : Nat := 118140960795 + 2484707 * 2 ^ 59
def prefixEnd_2484707 : Nat := 4983230072969 + 3 ^ 40 * 2484707 * 2
def baseEnd_2484707 : Nat := 94507331599341874528559

theorem tailTrace_2484707 : CollatzResearch.WordTrace tailWord_2484707 prefixEnd_2484707 94507331599341874528559 := by
  unfold tailWord_2484707
  simp only [CollatzResearch.WordTrace]
  refine ⟨90624709409338368016148375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60416472939558912010765583 90624709409338368016148375)
  ·
    refine ⟨135937064114007552024222563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90624709409338368016148375 135937064114007552024222563)
    ·
      refine ⟨203905596171011328036333845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135937064114007552024222563 203905596171011328036333845)
      ·
        refine ⟨9558074820516156001703149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 203905596171011328036333845 9558074820516156001703149)
        ·
          refine ⟨3584278057693558500638681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9558074820516156001703149 3584278057693558500638681)
          ·
            refine ⟨2688208543270168875479011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3584278057693558500638681 2688208543270168875479011)
            ·
              refine ⟨4032312814905253313218517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2688208543270168875479011 4032312814905253313218517)
              ·
                refine ⟨94507331599341874528559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4032312814905253313218517 94507331599341874528559)
                ·
                  rfl

theorem cell22_2484707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 7].length) (baseStart_2484707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2484707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2484707 prefixEnd_2484707 := by exact prefixLift 2484707
  have htrace : WordTrace (prefixWord ++ tailWord_2484707) baseStart_2484707 baseEnd_2484707 := by
    simpa [prefixWord, tailWord_2484707, baseEnd_2484707] using wordTrace_append hprefix tailTrace_2484707
  have hstable : (prefixWord ++ tailWord_2484707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2484707).length < 2 ^ (prefixWord ++ tailWord_2484707).sum := by decide
  have hdescent : baseEnd_2484707 < baseStart_2484707 := by decide
  rcases family_descends (prefixWord ++ tailWord_2484707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2484739 : List Nat := [1, 1, 1, 3, 2, 1, 6, 3, 1, 3]
def baseStart_2484739 : Nat := 118140960795 + 2484739 * 2 ^ 59
def prefixEnd_2484739 : Nat := 4983230072969 + 3 ^ 40 * 2484739 * 2
def baseEnd_2484739 : Nat := 850576938648039453956933

theorem tailTrace_2484739 : CollatzResearch.WordTrace tailWord_2484739 prefixEnd_2484739 850576938648039453956933 := by
  unfold tailWord_2484739
  simp only [CollatzResearch.WordTrace]
  refine ⟨90625876545222437481313271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60417251030148291654208847 90625876545222437481313271)
  ·
    refine ⟨135938814817833656221969907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90625876545222437481313271 135938814817833656221969907)
    ·
      refine ⟨203908222226750484332954861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135938814817833656221969907 203908222226750484332954861)
      ·
        refine ⟨76465583335031431624858073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 203908222226750484332954861 76465583335031431624858073)
        ·
          refine ⟨57349187501273573718643555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76465583335031431624858073 57349187501273573718643555)
          ·
            refine ⟨86023781251910360577965333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57349187501273573718643555 86023781251910360577965333)
            ·
              refine ⟨4032364746183298152092125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 86023781251910360577965333 4032364746183298152092125)
              ·
                refine ⟨1512136779818736807034547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4032364746183298152092125 1512136779818736807034547)
                ·
                  refine ⟨2268205169728105210551821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1512136779818736807034547 2268205169728105210551821)
                  ·
                    refine ⟨850576938648039453956933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2268205169728105210551821 850576938648039453956933)
                    ·
                      rfl

theorem cell22_2484739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 3, 1, 3].length) (baseStart_2484739 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2484739 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2484739 prefixEnd_2484739 := by exact prefixLift 2484739
  have htrace : WordTrace (prefixWord ++ tailWord_2484739) baseStart_2484739 baseEnd_2484739 := by
    simpa [prefixWord, tailWord_2484739, baseEnd_2484739] using wordTrace_append hprefix tailTrace_2484739
  have hstable : (prefixWord ++ tailWord_2484739).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2484739).length < 2 ^ (prefixWord ++ tailWord_2484739).sum := by decide
  have hdescent : baseEnd_2484739 < baseStart_2484739 := by decide
  rcases family_descends (prefixWord ++ tailWord_2484739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2484756 : List Nat := [2, 4, 3, 1, 1, 2, 2, 1, 3, 3]
def baseStart_2484756 : Nat := 118140960795 + 2484756 * 2 ^ 59
def prefixEnd_2484756 : Nat := 4983230072969 + 3 ^ 40 * 2484756 * 2
def baseEnd_2484756 : Nat := 850582758095457076281881

theorem tailTrace_2484756 : CollatzResearch.WordTrace tailWord_2484756 prefixEnd_2484756 850582758095457076281881 := by
  unfold tailWord_2484756
  simp only [CollatzResearch.WordTrace]
  refine ⟨45313248293080424692341061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60417664390773899589788081 45313248293080424692341061)
  ·
    refine ⟨8496234054952579629813949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45313248293080424692341061 8496234054952579629813949)
    ·
      refine ⟨3186087770607217361180231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8496234054952579629813949 3186087770607217361180231)
      ·
        refine ⟨4779131655910826041770347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3186087770607217361180231 4779131655910826041770347)
        ·
          refine ⟨7168697483866239062655521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4779131655910826041770347 7168697483866239062655521)
          ·
            refine ⟨5376523112899679296991641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7168697483866239062655521 5376523112899679296991641)
            ·
              refine ⟨4032392334674759472743731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5376523112899679296991641 4032392334674759472743731)
              ·
                refine ⟨6048588502012139209115597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4032392334674759472743731 6048588502012139209115597)
                ·
                  refine ⟨2268220688254552203418349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6048588502012139209115597 2268220688254552203418349)
                  ·
                    refine ⟨850582758095457076281881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2268220688254552203418349 850582758095457076281881)
                    ·
                      rfl

theorem cell22_2484756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_2484756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2484756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2484756 prefixEnd_2484756 := by exact prefixLift 2484756
  have htrace : WordTrace (prefixWord ++ tailWord_2484756) baseStart_2484756 baseEnd_2484756 := by
    simpa [prefixWord, tailWord_2484756, baseEnd_2484756] using wordTrace_append hprefix tailTrace_2484756
  have hstable : (prefixWord ++ tailWord_2484756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2484756).length < 2 ^ (prefixWord ++ tailWord_2484756).sum := by decide
  have hdescent : baseEnd_2484756 < baseStart_2484756 := by decide
  rcases family_descends (prefixWord ++ tailWord_2484756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2484812 : List Nat := [2, 2, 1, 3, 1, 2, 1, 3, 4, 3]
def baseStart_2484812 : Nat := 118140960795 + 2484812 * 2 ^ 59
def prefixEnd_2484812 : Nat := 4983230072969 + 3 ^ 40 * 2484812 * 2
def baseEnd_2484812 : Nat := 850601928039891596881709

theorem tailTrace_2484812 : CollatzResearch.WordTrace tailWord_2484812 prefixEnd_2484812 850601928039891596881709 := by
  unfold tailWord_2484812
  simp only [CollatzResearch.WordTrace]
  refine ⟨45314269536978985474360345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60419026049305313965813793 45314269536978985474360345)
  ·
    refine ⟨33985702152734239105770259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45314269536978985474360345 33985702152734239105770259)
    ·
      refine ⟨50978553229101358658655389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33985702152734239105770259 50978553229101358658655389)
      ·
        refine ⟨19116957460913009496995771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50978553229101358658655389 19116957460913009496995771)
        ·
          refine ⟨28675436191369514245493657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19116957460913009496995771 28675436191369514245493657)
          ·
            refine ⟨21506577143527135684120243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28675436191369514245493657 21506577143527135684120243)
            ·
              refine ⟨32259865715290703526180365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21506577143527135684120243 32259865715290703526180365)
              ·
                refine ⟨12097449643234013822317637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32259865715290703526180365 12097449643234013822317637)
                ·
                  refine ⟨2268271808106377591684557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12097449643234013822317637 2268271808106377591684557)
                  ·
                    refine ⟨850601928039891596881709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2268271808106377591684557 850601928039891596881709)
                    ·
                      rfl

theorem cell22_2484812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 3, 4, 3].length) (baseStart_2484812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2484812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2484812 prefixEnd_2484812 := by exact prefixLift 2484812
  have htrace : WordTrace (prefixWord ++ tailWord_2484812) baseStart_2484812 baseEnd_2484812 := by
    simpa [prefixWord, tailWord_2484812, baseEnd_2484812] using wordTrace_append hprefix tailTrace_2484812
  have hstable : (prefixWord ++ tailWord_2484812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2484812).length < 2 ^ (prefixWord ++ tailWord_2484812).sum := by decide
  have hdescent : baseEnd_2484812 < baseStart_2484812 := by decide
  rcases family_descends (prefixWord ++ tailWord_2484812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2484887 : List Nat := [1, 1, 3, 3, 2, 1, 1, 5, 5]
def baseStart_2484887 : Nat := 118140960795 + 2484887 * 2 ^ 59
def prefixEnd_2484887 : Nat := 4983230072969 + 3 ^ 40 * 2484887 * 2
def baseEnd_2484887 : Nat := 283542534024205467085493

theorem tailTrace_2484887 : CollatzResearch.WordTrace tailWord_2484887 prefixEnd_2484887 283542534024205467085493 := by
  unfold tailWord_2484887
  simp only [CollatzResearch.WordTrace]
  refine ⟨90631274548686258757700915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60420849699124172505133943 90631274548686258757700915)
  ·
    refine ⟨135946911823029388136551373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90631274548686258757700915 135946911823029388136551373)
    ·
      refine ⟨50980091933636020551206765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135946911823029388136551373 50980091933636020551206765)
      ·
        refine ⟨19117534475113507706702537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50980091933636020551206765 19117534475113507706702537)
        ·
          refine ⟨14338150856335130780026903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19117534475113507706702537 14338150856335130780026903)
          ·
            refine ⟨21507226284502696170040355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14338150856335130780026903 21507226284502696170040355)
            ·
              refine ⟨32260839426754044255060533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21507226284502696170040355 32260839426754044255060533)
              ·
                refine ⟨3024453696258191648911925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32260839426754044255060533 3024453696258191648911925)
                ·
                  refine ⟨283542534024205467085493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3024453696258191648911925 283542534024205467085493)
                  ·
                    rfl

theorem cell22_2484887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 5, 5].length) (baseStart_2484887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2484887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2484887 prefixEnd_2484887 := by exact prefixLift 2484887
  have htrace : WordTrace (prefixWord ++ tailWord_2484887) baseStart_2484887 baseEnd_2484887 := by
    simpa [prefixWord, tailWord_2484887, baseEnd_2484887] using wordTrace_append hprefix tailTrace_2484887
  have hstable : (prefixWord ++ tailWord_2484887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2484887).length < 2 ^ (prefixWord ++ tailWord_2484887).sum := by decide
  have hdescent : baseEnd_2484887 < baseStart_2484887 := by decide
  rcases family_descends (prefixWord ++ tailWord_2484887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2484964 : List Nat := [2, 3, 1, 1, 1, 4, 1, 2, 4, 3]
def baseStart_2484964 : Nat := 118140960795 + 2484964 * 2 ^ 59
def prefixEnd_2484964 : Nat := 4983230072969 + 3 ^ 40 * 2484964 * 2
def baseEnd_2484964 : Nat := 850653960746213867081243

theorem tailTrace_2484964 : CollatzResearch.WordTrace tailWord_2484964 prefixEnd_2484964 850653960746213867081243 := by
  unfold tailWord_2484964
  simp only [CollatzResearch.WordTrace]
  refine ⟨45317041484703650454126973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60422721979604867272169297 45317041484703650454126973)
  ·
    refine ⟨16993890556763868920297615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45317041484703650454126973 16993890556763868920297615)
    ·
      refine ⟨25490835835145803380446423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16993890556763868920297615 25490835835145803380446423)
      ·
        refine ⟨38236253752718705070669635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25490835835145803380446423 38236253752718705070669635)
        ·
          refine ⟨57354380629078057606004453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38236253752718705070669635 57354380629078057606004453)
          ·
            refine ⟨10753946367952135801125835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57354380629078057606004453 10753946367952135801125835)
            ·
              refine ⟨16130919551928203701688753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10753946367952135801125835 16130919551928203701688753)
              ·
                refine ⟨12098189663946152776266565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16130919551928203701688753 12098189663946152776266565)
                ·
                  refine ⟨2268410561989903645549981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12098189663946152776266565 2268410561989903645549981)
                  ·
                    refine ⟨850653960746213867081243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2268410561989903645549981 850653960746213867081243)
                    ·
                      rfl

theorem cell22_2484964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 2, 4, 3].length) (baseStart_2484964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2484964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2484964 prefixEnd_2484964 := by exact prefixLift 2484964
  have htrace : WordTrace (prefixWord ++ tailWord_2484964) baseStart_2484964 baseEnd_2484964 := by
    simpa [prefixWord, tailWord_2484964, baseEnd_2484964] using wordTrace_append hprefix tailTrace_2484964
  have hstable : (prefixWord ++ tailWord_2484964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2484964).length < 2 ^ (prefixWord ++ tailWord_2484964).sum := by decide
  have hdescent : baseEnd_2484964 < baseStart_2484964 := by decide
  rcases family_descends (prefixWord ++ tailWord_2484964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2484994 : List Nat := [3, 4, 1, 1, 1, 2, 1, 9]
def baseStart_2484994 : Nat := 118140960795 + 2484994 * 2 ^ 59
def prefixEnd_2484994 : Nat := 4983230072969 + 3 ^ 40 * 2484994 * 2
def baseEnd_2484994 : Nat := 94518247817700420981239

theorem tailTrace_2484994 : CollatzResearch.WordTrace tailWord_2484994 prefixEnd_2484994 94518247817700420981239 := by
  unfold tailWord_2484994
  simp only [CollatzResearch.WordTrace]
  refine ⟨22658794289824654007961509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60423451439532410687897357 22658794289824654007961509)
  ·
    refine ⟨4248523929342122626492783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22658794289824654007961509 4248523929342122626492783)
    ·
      refine ⟨6372785894013183939739175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4248523929342122626492783 6372785894013183939739175)
      ·
        refine ⟨9559178841019775909608763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6372785894013183939739175 9559178841019775909608763)
        ·
          refine ⟨14338768261529663864413145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9559178841019775909608763 14338768261529663864413145)
          ·
            refine ⟨10754076196147247898309859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14338768261529663864413145 10754076196147247898309859)
            ·
              refine ⟨16131114294220871847464789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10754076196147247898309859 16131114294220871847464789)
              ·
                refine ⟨94518247817700420981239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16131114294220871847464789 94518247817700420981239)
                ·
                  rfl

theorem cell22_2484994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 9].length) (baseStart_2484994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2484994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2484994 prefixEnd_2484994 := by exact prefixLift 2484994
  have htrace : WordTrace (prefixWord ++ tailWord_2484994) baseStart_2484994 baseEnd_2484994 := by
    simpa [prefixWord, tailWord_2484994, baseEnd_2484994] using wordTrace_append hprefix tailTrace_2484994
  have hstable : (prefixWord ++ tailWord_2484994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2484994).length < 2 ^ (prefixWord ++ tailWord_2484994).sum := by decide
  have hdescent : baseEnd_2484994 < baseStart_2484994 := by decide
  rcases family_descends (prefixWord ++ tailWord_2484994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2485009 : List Nat := [1, 2, 2, 1, 1, 3, 2, 4, 3, 3]
def baseStart_2485009 : Nat := 118140960795 + 2485009 * 2 ^ 59
def prefixEnd_2485009 : Nat := 4983230072969 + 3 ^ 40 * 2485009 * 2
def baseEnd_2485009 : Nat := 850669365165848749706105

theorem tailTrace_2485009 : CollatzResearch.WordTrace tailWord_2485009 prefixEnd_2485009 850669365165848749706105 := by
  unfold tailWord_2485009
  simp only [CollatzResearch.WordTrace]
  refine ⟨90635724254244273593642081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60423816169496182395761387 90635724254244273593642081)
  ·
    refine ⟨67976793190683205195231561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90635724254244273593642081 67976793190683205195231561)
    ·
      refine ⟨50982594893012403896423671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67976793190683205195231561 50982594893012403896423671)
      ·
        refine ⟨76473892339518605844635507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50982594893012403896423671 76473892339518605844635507)
        ·
          refine ⟨114710838509277908766953261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76473892339518605844635507 114710838509277908766953261)
          ·
            refine ⟨43016564440979215787607473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 114710838509277908766953261 43016564440979215787607473)
            ·
              refine ⟨32262423330734411840705605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43016564440979215787607473 32262423330734411840705605)
              ·
                refine ⟨6049204374512702220132301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32262423330734411840705605 6049204374512702220132301)
                ·
                  refine ⟨2268451640442263332549613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6049204374512702220132301 2268451640442263332549613)
                  ·
                    refine ⟨850669365165848749706105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2268451640442263332549613 850669365165848749706105)
                    ·
                      rfl

theorem cell22_2485009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 4, 3, 3].length) (baseStart_2485009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2485009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2485009 prefixEnd_2485009 := by exact prefixLift 2485009
  have htrace : WordTrace (prefixWord ++ tailWord_2485009) baseStart_2485009 baseEnd_2485009 := by
    simpa [prefixWord, tailWord_2485009, baseEnd_2485009] using wordTrace_append hprefix tailTrace_2485009
  have hstable : (prefixWord ++ tailWord_2485009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2485009).length < 2 ^ (prefixWord ++ tailWord_2485009).sum := by decide
  have hdescent : baseEnd_2485009 < baseStart_2485009 := by decide
  rcases family_descends (prefixWord ++ tailWord_2485009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2485043 : List Nat := [1, 1, 1, 2, 6, 2, 1, 4, 1, 3]
def baseStart_2485043 : Nat := 118140960795 + 2485043 * 2 ^ 59
def prefixEnd_2485043 : Nat := 4983230072969 + 3 ^ 40 * 2485043 * 2
def baseEnd_2485043 : Nat := 850681004060683994356001

theorem tailTrace_2485043 : CollatzResearch.WordTrace tailWord_2485043 prefixEnd_2485043 850681004060683994356001 := by
  unfold tailWord_2485043
  simp only [CollatzResearch.WordTrace]
  refine ⟨90636964336121097400379783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60424642890747398266919855 90636964336121097400379783)
  ·
    refine ⟨135955446504181646100569675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90636964336121097400379783 135955446504181646100569675)
    ·
      refine ⟨203933169756272469150854513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135955446504181646100569675 203933169756272469150854513)
      ·
        refine ⟨152949877317204351863140885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 203933169756272469150854513 152949877317204351863140885)
        ·
          refine ⟨7169525499243953993584729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 152949877317204351863140885 7169525499243953993584729)
          ·
            refine ⟨5377144124432965495188547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7169525499243953993584729 5377144124432965495188547)
            ·
              refine ⟨8065716186649448242782821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5377144124432965495188547 8065716186649448242782821)
              ·
                refine ⟨1512321784996771545521779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8065716186649448242782821 1512321784996771545521779)
                ·
                  refine ⟨2268482677495157318282669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1512321784996771545521779 2268482677495157318282669)
                  ·
                    refine ⟨850681004060683994356001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2268482677495157318282669 850681004060683994356001)
                    ·
                      rfl

theorem cell22_2485043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 4, 1, 3].length) (baseStart_2485043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2485043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2485043 prefixEnd_2485043 := by exact prefixLift 2485043
  have htrace : WordTrace (prefixWord ++ tailWord_2485043) baseStart_2485043 baseEnd_2485043 := by
    simpa [prefixWord, tailWord_2485043, baseEnd_2485043] using wordTrace_append hprefix tailTrace_2485043
  have hstable : (prefixWord ++ tailWord_2485043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2485043).length < 2 ^ (prefixWord ++ tailWord_2485043).sum := by decide
  have hdescent : baseEnd_2485043 < baseStart_2485043 := by decide
  rcases family_descends (prefixWord ++ tailWord_2485043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2485060 : List Nat := [2, 3, 4, 2, 1, 1, 1, 2, 3, 3]
def baseStart_2485060 : Nat := 118140960795 + 2485060 * 2 ^ 59
def prefixEnd_2485060 : Nat := 4983230072969 + 3 ^ 40 * 2485060 * 2
def baseEnd_2485060 : Nat := 850686823508101616680949

theorem tailTrace_2485060 : CollatzResearch.WordTrace tailWord_2485060 prefixEnd_2485060 850686823508101616680949 := by
  unfold tailWord_2485060
  simp only [CollatzResearch.WordTrace]
  refine ⟨45318792188529754651874317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60425056251373006202499089 45318792188529754651874317)
  ·
    refine ⟨16994547070698657994452869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45318792188529754651874317 16994547070698657994452869)
    ·
      refine ⟨3186477575755998373959913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16994547070698657994452869 3186477575755998373959913)
      ·
        refine ⟨2389858181816998780469935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3186477575755998373959913 2389858181816998780469935)
        ·
          refine ⟨3584787272725498170704903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2389858181816998780469935 3584787272725498170704903)
          ·
            refine ⟨5377180909088247256057355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3584787272725498170704903 5377180909088247256057355)
            ·
              refine ⟨8065771363632370884086033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5377180909088247256057355 8065771363632370884086033)
              ·
                refine ⟨6049328522724278163064525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8065771363632370884086033 6049328522724278163064525)
                ·
                  refine ⟨2268498196021604311149197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6049328522724278163064525 2268498196021604311149197)
                  ·
                    refine ⟨850686823508101616680949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2268498196021604311149197 850686823508101616680949)
                    ·
                      rfl

theorem cell22_2485060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_2485060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2485060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2485060 prefixEnd_2485060 := by exact prefixLift 2485060
  have htrace : WordTrace (prefixWord ++ tailWord_2485060) baseStart_2485060 baseEnd_2485060 := by
    simpa [prefixWord, tailWord_2485060, baseEnd_2485060] using wordTrace_append hprefix tailTrace_2485060
  have hstable : (prefixWord ++ tailWord_2485060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2485060).length < 2 ^ (prefixWord ++ tailWord_2485060).sum := by decide
  have hdescent : baseEnd_2485060 < baseStart_2485060 := by decide
  rcases family_descends (prefixWord ++ tailWord_2485060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2485090 : List Nat := [3, 3, 2, 1, 4, 1, 1, 2, 5]
def baseStart_2485090 : Nat := 118140960795 + 2485090 * 2 ^ 59
def prefixEnd_2485090 : Nat := 4983230072969 + 3 ^ 40 * 2485090 * 2
def baseEnd_2485090 : Nat := 283565697707063846143619

theorem tailTrace_2485090 : CollatzResearch.WordTrace tailWord_2485090 prefixEnd_2485090 283565697707063846143619 := by
  unfold tailWord_2485090
  simp only [CollatzResearch.WordTrace]
  refine ⟨22659669641737706106835181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60425785711300549618227149 22659669641737706106835181)
  ·
    refine ⟨8497376115651639790063193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22659669641737706106835181 8497376115651639790063193)
    ·
      refine ⟨6373032086738729842547395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8497376115651639790063193 6373032086738729842547395)
      ·
        refine ⟨9559548130108094763821093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6373032086738729842547395 9559548130108094763821093)
        ·
          refine ⟨1792415274395267768216455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9559548130108094763821093 1792415274395267768216455)
          ·
            refine ⟨2688622911592901652324683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1792415274395267768216455 2688622911592901652324683)
            ·
              refine ⟨4032934367389352478487025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2688622911592901652324683 4032934367389352478487025)
              ·
                refine ⟨3024700775542014358865269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4032934367389352478487025 3024700775542014358865269)
                ·
                  refine ⟨283565697707063846143619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3024700775542014358865269 283565697707063846143619)
                  ·
                    rfl

theorem cell22_2485090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 2, 5].length) (baseStart_2485090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2485090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2485090 prefixEnd_2485090 := by exact prefixLift 2485090
  have htrace : WordTrace (prefixWord ++ tailWord_2485090) baseStart_2485090 baseEnd_2485090 := by
    simpa [prefixWord, tailWord_2485090, baseEnd_2485090] using wordTrace_append hprefix tailTrace_2485090
  have hstable : (prefixWord ++ tailWord_2485090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2485090).length < 2 ^ (prefixWord ++ tailWord_2485090).sum := by decide
  have hdescent : baseEnd_2485090 < baseStart_2485090 := by decide
  rcases family_descends (prefixWord ++ tailWord_2485090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2485116 : List Nat := [2, 2, 2, 1, 1, 1, 1, 7, 2, 3]
def baseStart_2485116 : Nat := 118140960795 + 2485116 * 2 ^ 59
def prefixEnd_2485116 : Nat := 4983230072969 + 3 ^ 40 * 2485116 * 2
def baseEnd_2485116 : Nat := 850705993452536137280777

theorem tailTrace_2485116 : CollatzResearch.WordTrace tailWord_2485116 prefixEnd_2485116 850705993452536137280777 := by
  unfold tailWord_2485116
  simp only [CollatzResearch.WordTrace]
  refine ⟨45319813432428315433893601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60426417909904420578524801 45319813432428315433893601)
  ·
    refine ⟨33989860074321236575420201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45319813432428315433893601 33989860074321236575420201)
    ·
      refine ⟨25492395055740927431565151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33989860074321236575420201 25492395055740927431565151)
      ·
        refine ⟨38238592583611391147347727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25492395055740927431565151 38238592583611391147347727)
        ·
          refine ⟨57357888875417086721021591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38238592583611391147347727 57357888875417086721021591)
          ·
            refine ⟨86036833313125630081532387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57357888875417086721021591 86036833313125630081532387)
            ·
              refine ⟨129055249969688445122298581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86036833313125630081532387 129055249969688445122298581)
              ·
                refine ⟨3024732421164572932553873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 129055249969688445122298581 3024732421164572932553873)
                ·
                  refine ⟨2268549315873429699415405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3024732421164572932553873 2268549315873429699415405)
                  ·
                    refine ⟨850705993452536137280777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2268549315873429699415405 850705993452536137280777)
                    ·
                      rfl

theorem cell22_2485116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 7, 2, 3].length) (baseStart_2485116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2485116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2485116 prefixEnd_2485116 := by exact prefixLift 2485116
  have htrace : WordTrace (prefixWord ++ tailWord_2485116) baseStart_2485116 baseEnd_2485116 := by
    simpa [prefixWord, tailWord_2485116, baseEnd_2485116] using wordTrace_append hprefix tailTrace_2485116
  have hstable : (prefixWord ++ tailWord_2485116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2485116).length < 2 ^ (prefixWord ++ tailWord_2485116).sum := by decide
  have hdescent : baseEnd_2485116 < baseStart_2485116 := by decide
  rcases family_descends (prefixWord ++ tailWord_2485116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2485129 : List Nat := [1, 2, 1, 1, 5, 3, 1, 8]
def baseStart_2485129 : Nat := 118140960795 + 2485129 * 2 ^ 59
def prefixEnd_2485129 : Nat := 4983230072969 + 3 ^ 40 * 2485129 * 2
def baseEnd_2485129 : Nat := 94523382624245381856193

theorem tailTrace_2485129 : CollatzResearch.WordTrace tailWord_2485129 prefixEnd_2485129 94523382624245381856193 := by
  unfold tailWord_2485129
  simp only [CollatzResearch.WordTrace]
  refine ⟨90640101013809534088010441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60426734009206356058673627 90640101013809534088010441)
  ·
    refine ⟨67980075760357150566007831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90640101013809534088010441 67980075760357150566007831)
    ·
      refine ⟨101970113640535725849011747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67980075760357150566007831 101970113640535725849011747)
      ·
        refine ⟨152955170460803588773517621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101970113640535725849011747 152955170460803588773517621)
        ·
          refine ⟨14339547230700336447517277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 152955170460803588773517621 14339547230700336447517277)
          ·
            refine ⟨5377330211512626167818979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14339547230700336447517277 5377330211512626167818979)
            ·
              refine ⟨8065995317268939251728469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5377330211512626167818979 8065995317268939251728469)
              ·
                refine ⟨94523382624245381856193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8065995317268939251728469 94523382624245381856193)
                ·
                  rfl

theorem cell22_2485129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 8].length) (baseStart_2485129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2485129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2485129 prefixEnd_2485129 := by exact prefixLift 2485129
  have htrace : WordTrace (prefixWord ++ tailWord_2485129) baseStart_2485129 baseEnd_2485129 := by
    simpa [prefixWord, tailWord_2485129, baseEnd_2485129] using wordTrace_append hprefix tailTrace_2485129
  have hstable : (prefixWord ++ tailWord_2485129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2485129).length < 2 ^ (prefixWord ++ tailWord_2485129).sum := by decide
  have hdescent : baseEnd_2485129 < baseStart_2485129 := by decide
  rcases family_descends (prefixWord ++ tailWord_2485129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2485146 : List Nat := [3, 1, 1, 4, 3, 2, 8]
def baseStart_2485146 : Nat := 118140960795 + 2485146 * 2 ^ 59
def prefixEnd_2485146 : Nat := 4983230072969 + 3 ^ 40 * 2485146 * 2
def baseEnd_2485146 : Nat := 31508009743171335519655

theorem tailTrace_2485146 : CollatzResearch.WordTrace tailWord_2485146 prefixEnd_2485146 31508009743171335519655 := by
  unfold tailWord_2485146
  simp only [CollatzResearch.WordTrace]
  refine ⟨22660180263686986497844823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60427147369831963994252861 22660180263686986497844823)
  ·
    refine ⟨33990270395530479746767235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22660180263686986497844823 33990270395530479746767235)
    ·
      refine ⟨50985405593295719620150853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33990270395530479746767235 50985405593295719620150853)
      ·
        refine ⟨9559763548742947428778285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50985405593295719620150853 9559763548742947428778285)
        ·
          refine ⟨3584911330778605285791857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9559763548742947428778285 3584911330778605285791857)
          ·
            refine ⟨2688683498083953964343893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3584911330778605285791857 2688683498083953964343893)
            ·
              refine ⟨31508009743171335519655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2688683498083953964343893 31508009743171335519655)
              ·
                rfl

theorem cell22_2485146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 8].length) (baseStart_2485146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2485146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2485146 prefixEnd_2485146 := by exact prefixLift 2485146
  have htrace : WordTrace (prefixWord ++ tailWord_2485146) baseStart_2485146 baseEnd_2485146 := by
    simpa [prefixWord, tailWord_2485146, baseEnd_2485146] using wordTrace_append hprefix tailTrace_2485146
  have hstable : (prefixWord ++ tailWord_2485146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2485146).length < 2 ^ (prefixWord ++ tailWord_2485146).sum := by decide
  have hdescent : baseEnd_2485146 < baseStart_2485146 := by decide
  rcases family_descends (prefixWord ++ tailWord_2485146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2485148 : List Nat := [2, 2, 3, 3, 2, 1, 1, 2, 2, 4]
def baseStart_2485148 : Nat := 118140960795 + 2485148 * 2 ^ 59
def prefixEnd_2485148 : Nat := 4983230072969 + 3 ^ 40 * 2485148 * 2
def baseEnd_2485148 : Nat := 850716947706498720480679

theorem tailTrace_2485148 : CollatzResearch.WordTrace tailWord_2485148 prefixEnd_2485148 850716947706498720480679 := by
  unfold tailWord_2485148
  simp only [CollatzResearch.WordTrace]
  refine ⟨45320397000370350166476049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60427196000493800221968065 45320397000370350166476049)
  ·
    refine ⟨33990297750277762624857037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45320397000370350166476049 33990297750277762624857037)
    ·
      refine ⟨12746361656354160984321389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33990297750277762624857037 12746361656354160984321389)
      ·
        refine ⟨4779885621132810369120521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12746361656354160984321389 4779885621132810369120521)
        ·
          refine ⟨3584914215849607776840391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4779885621132810369120521 3584914215849607776840391)
          ·
            refine ⟨5377371323774411665260587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3584914215849607776840391 5377371323774411665260587)
            ·
              refine ⟨8066056985661617497890881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5377371323774411665260587 8066056985661617497890881)
              ·
                refine ⟨6049542739246213123418161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8066056985661617497890881 6049542739246213123418161)
                ·
                  refine ⟨4537157054434659842563621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6049542739246213123418161 4537157054434659842563621)
                  ·
                    refine ⟨850716947706498720480679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4537157054434659842563621 850716947706498720480679)
                    ·
                      rfl

theorem cell22_2485148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 2, 2, 4].length) (baseStart_2485148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2485148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2485148 prefixEnd_2485148 := by exact prefixLift 2485148
  have htrace : WordTrace (prefixWord ++ tailWord_2485148) baseStart_2485148 baseEnd_2485148 := by
    simpa [prefixWord, tailWord_2485148, baseEnd_2485148] using wordTrace_append hprefix tailTrace_2485148
  have hstable : (prefixWord ++ tailWord_2485148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2485148).length < 2 ^ (prefixWord ++ tailWord_2485148).sum := by decide
  have hdescent : baseEnd_2485148 < baseStart_2485148 := by decide
  rcases family_descends (prefixWord ++ tailWord_2485148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2485238 : List Nat := [5, 1, 1, 1, 3, 1, 2, 1, 3, 4]
def baseStart_2485238 : Nat := 118140960795 + 2485238 * 2 ^ 59
def prefixEnd_2485238 : Nat := 4983230072969 + 3 ^ 40 * 2485238 * 2
def baseEnd_2485238 : Nat := 850747756545768485730403

theorem tailTrace_2485238 : CollatzResearch.WordTrace tailWord_2485238 prefixEnd_2485238 850747756545768485730403 := by
  unfold tailWord_2485238
  simp only [CollatzResearch.WordTrace]
  refine ⟨5665254785650915356483023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 60429384380276430469152245 5665254785650915356483023)
  ·
    refine ⟨8497882178476373034724535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5665254785650915356483023 8497882178476373034724535)
    ·
      refine ⟨12746823267714559552086803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8497882178476373034724535 12746823267714559552086803)
      ·
        refine ⟨19120234901571839328130205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12746823267714559552086803 19120234901571839328130205)
        ·
          refine ⟨7170088088089439748048827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19120234901571839328130205 7170088088089439748048827)
          ·
            refine ⟨10755132132134159622073241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7170088088089439748048827 10755132132134159622073241)
            ·
              refine ⟨8066349099100619716554931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10755132132134159622073241 8066349099100619716554931)
              ·
                refine ⟨12099523648650929574832397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8066349099100619716554931 12099523648650929574832397)
                ·
                  refine ⟨4537321368244098590562149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12099523648650929574832397 4537321368244098590562149)
                  ·
                    refine ⟨850747756545768485730403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4537321368244098590562149 850747756545768485730403)
                    ·
                      rfl

theorem cell22_2485238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 1, 3, 4].length) (baseStart_2485238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2485238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2485238 prefixEnd_2485238 := by exact prefixLift 2485238
  have htrace : WordTrace (prefixWord ++ tailWord_2485238) baseStart_2485238 baseEnd_2485238 := by
    simpa [prefixWord, tailWord_2485238, baseEnd_2485238] using wordTrace_append hprefix tailTrace_2485238
  have hstable : (prefixWord ++ tailWord_2485238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2485238).length < 2 ^ (prefixWord ++ tailWord_2485238).sum := by decide
  have hdescent : baseEnd_2485238 < baseStart_2485238 := by decide
  rcases family_descends (prefixWord ++ tailWord_2485238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2485253 : List Nat := [1, 3, 1, 1, 2, 3, 4, 3, 4]
def baseStart_2485253 : Nat := 118140960795 + 2485253 * 2 ^ 59
def prefixEnd_2485253 : Nat := 4983230072969 + 3 ^ 40 * 2485253 * 2
def baseEnd_2485253 : Nat := 283584297117437815535119

theorem tailTrace_2485253 : CollatzResearch.WordTrace tailWord_2485253 prefixEnd_2485253 283584297117437815535119 := by
  unfold tailWord_2485253
  simp only [CollatzResearch.WordTrace]
  refine ⟨90644623665360303265524413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60429749110240202177016275 90644623665360303265524413)
  ·
    refine ⟨33991733874510113724571655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90644623665360303265524413 33991733874510113724571655)
    ·
      refine ⟨50987600811765170586857483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33991733874510113724571655 50987600811765170586857483)
      ·
        refine ⟨76481401217647755880286225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50987600811765170586857483 76481401217647755880286225)
        ·
          refine ⟨57361050913235816910214669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76481401217647755880286225 57361050913235816910214669)
          ·
            refine ⟨21510394092463431341330501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57361050913235816910214669 21510394092463431341330501)
            ·
              refine ⟨4033198892336893376499469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21510394092463431341330501 4033198892336893376499469)
              ·
                refine ⟨1512449584626335016187301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4033198892336893376499469 1512449584626335016187301)
                ·
                  refine ⟨283584297117437815535119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1512449584626335016187301 283584297117437815535119)
                  ·
                    rfl

theorem cell22_2485253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 3, 4].length) (baseStart_2485253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2485253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2485253 prefixEnd_2485253 := by exact prefixLift 2485253
  have htrace : WordTrace (prefixWord ++ tailWord_2485253) baseStart_2485253 baseEnd_2485253 := by
    simpa [prefixWord, tailWord_2485253, baseEnd_2485253] using wordTrace_append hprefix tailTrace_2485253
  have hstable : (prefixWord ++ tailWord_2485253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2485253).length < 2 ^ (prefixWord ++ tailWord_2485253).sum := by decide
  have hdescent : baseEnd_2485253 < baseStart_2485253 := by decide
  rcases family_descends (prefixWord ++ tailWord_2485253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2485285 : List Nat := [1, 3, 1, 2, 2, 2, 5, 1, 2, 3]
def baseStart_2485285 : Nat := 118140960795 + 2485285 * 2 ^ 59
def prefixEnd_2485285 : Nat := 4983230072969 + 3 ^ 40 * 2485285 * 2
def baseEnd_2485285 : Nat := 850763845606276029805259

theorem tailTrace_2485285 : CollatzResearch.WordTrace tailWord_2485285 prefixEnd_2485285 850763845606276029805259 := by
  unfold tailWord_2485285
  simp only [CollatzResearch.WordTrace]
  refine ⟨90645790801244372730689309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60430527200829581820459539 90645790801244372730689309)
  ·
    refine ⟨33992171550466639774008491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90645790801244372730689309 33992171550466639774008491)
    ·
      refine ⟨50988257325699959661012737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33992171550466639774008491 50988257325699959661012737)
      ·
        refine ⟨38241192994274969745759553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50988257325699959661012737 38241192994274969745759553)
        ·
          refine ⟨28680894745706227309319665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38241192994274969745759553 28680894745706227309319665)
          ·
            refine ⟨21510671059279670481989749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28680894745706227309319665 21510671059279670481989749)
            ·
              refine ⟨2016625411807469107686539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21510671059279670481989749 2016625411807469107686539)
              ·
                refine ⟨3024938117711203661529809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2016625411807469107686539 3024938117711203661529809)
                ·
                  refine ⟨2268703588283402746147357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3024938117711203661529809 2268703588283402746147357)
                  ·
                    refine ⟨850763845606276029805259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2268703588283402746147357 850763845606276029805259)
                    ·
                      rfl

theorem cell22_2485285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 5, 1, 2, 3].length) (baseStart_2485285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2485285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2485285 prefixEnd_2485285 := by exact prefixLift 2485285
  have htrace : WordTrace (prefixWord ++ tailWord_2485285) baseStart_2485285 baseEnd_2485285 := by
    simpa [prefixWord, tailWord_2485285, baseEnd_2485285] using wordTrace_append hprefix tailTrace_2485285
  have hstable : (prefixWord ++ tailWord_2485285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2485285).length < 2 ^ (prefixWord ++ tailWord_2485285).sum := by decide
  have hdescent : baseEnd_2485285 < baseStart_2485285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2485285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2485326 : List Nat := [4, 1, 1, 1, 1, 3, 1, 3, 7]
def baseStart_2485326 : Nat := 118140960795 + 2485326 * 2 ^ 59
def prefixEnd_2485326 : Nat := 4983230072969 + 3 ^ 40 * 2485326 * 2
def baseEnd_2485326 : Nat := 283592626914721863176711

theorem tailTrace_2485326 : CollatzResearch.WordTrace tailWord_2485326 prefixEnd_2485326 283592626914721863176711 := by
  unfold tailWord_2485326
  simp only [CollatzResearch.WordTrace]
  refine ⟨11330910774261979591616479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60431524129397224488621221 11330910774261979591616479)
  ·
    refine ⟨16996366161392969387424719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11330910774261979591616479 16996366161392969387424719)
    ·
      refine ⟨25494549242089454081137079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16996366161392969387424719 25494549242089454081137079)
      ·
        refine ⟨38241823863134181121705619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25494549242089454081137079 38241823863134181121705619)
        ·
          refine ⟨57362735794701271682558429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38241823863134181121705619 57362735794701271682558429)
          ·
            refine ⟨21511025923012976880959411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57362735794701271682558429 21511025923012976880959411)
            ·
              refine ⟨32266538884519465321439117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21511025923012976880959411 32266538884519465321439117)
              ·
                refine ⟨12099952081694799495539669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32266538884519465321439117 12099952081694799495539669)
                ·
                  refine ⟨283592626914721863176711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12099952081694799495539669 283592626914721863176711)
                  ·
                    rfl

theorem cell22_2485326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 3, 7].length) (baseStart_2485326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2485326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2485326 prefixEnd_2485326 := by exact prefixLift 2485326
  have htrace : WordTrace (prefixWord ++ tailWord_2485326) baseStart_2485326 baseEnd_2485326 := by
    simpa [prefixWord, tailWord_2485326, baseEnd_2485326] using wordTrace_append hprefix tailTrace_2485326
  have hstable : (prefixWord ++ tailWord_2485326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2485326).length < 2 ^ (prefixWord ++ tailWord_2485326).sum := by decide
  have hdescent : baseEnd_2485326 < baseStart_2485326 := by decide
  rcases family_descends (prefixWord ++ tailWord_2485326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2485330 : List Nat := [3, 2, 2, 1, 3, 1, 3, 1, 3, 3]
def baseStart_2485330 : Nat := 118140960795 + 2485330 * 2 ^ 59
def prefixEnd_2485330 : Nat := 4983230072969 + 3 ^ 40 * 2485330 * 2
def baseEnd_2485330 : Nat := 850779250025910912430121

theorem tailTrace_2485330 : CollatzResearch.WordTrace tailWord_2485330 prefixEnd_2485330 850779250025910912430121 := by
  unfold tailWord_2485330
  simp only [CollatzResearch.WordTrace]
  refine ⟨22661858021520336354019361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60431621390720896944051629 22661858021520336354019361)
  ·
    refine ⟨16996393516140252265514521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22661858021520336354019361 16996393516140252265514521)
    ·
      refine ⟨12747295137105189199135891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16996393516140252265514521 12747295137105189199135891)
      ·
        refine ⟨19120942705657783798703837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12747295137105189199135891 19120942705657783798703837)
        ·
          refine ⟨7170353514621668924513939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19120942705657783798703837 7170353514621668924513939)
          ·
            refine ⟨10755530271932503386770909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7170353514621668924513939 10755530271932503386770909)
            ·
              refine ⟨4033323851974688770039091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10755530271932503386770909 4033323851974688770039091)
              ·
                refine ⟨6049985777962033155058637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4033323851974688770039091 6049985777962033155058637)
                ·
                  refine ⟨2268744666735762433146989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6049985777962033155058637 2268744666735762433146989)
                  ·
                    refine ⟨850779250025910912430121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2268744666735762433146989 850779250025910912430121)
                    ·
                      rfl

theorem cell22_2485330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 1, 3, 3].length) (baseStart_2485330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2485330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2485330 prefixEnd_2485330 := by exact prefixLift 2485330
  have htrace : WordTrace (prefixWord ++ tailWord_2485330) baseStart_2485330 baseEnd_2485330 := by
    simpa [prefixWord, tailWord_2485330, baseEnd_2485330] using wordTrace_append hprefix tailTrace_2485330
  have hstable : (prefixWord ++ tailWord_2485330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2485330).length < 2 ^ (prefixWord ++ tailWord_2485330).sum := by decide
  have hdescent : baseEnd_2485330 < baseStart_2485330 := by decide
  rcases family_descends (prefixWord ++ tailWord_2485330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2485381 : List Nat := [1, 3, 1, 1, 7, 1, 2, 2, 1, 3]
def baseStart_2485381 : Nat := 118140960795 + 2485381 * 2 ^ 59
def prefixEnd_2485381 : Nat := 4983230072969 + 3 ^ 40 * 2485381 * 2
def baseEnd_2485381 : Nat := 850796708368163779404965

theorem tailTrace_2485381 : CollatzResearch.WordTrace tailWord_2485381 prefixEnd_2485381 850796708368163779404965 := by
  unfold tailWord_2485381
  simp only [CollatzResearch.WordTrace]
  refine ⟨90649292208896581126183997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60432861472597720750789331 90649292208896581126183997)
  ·
    refine ⟨33993484578336217922318999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90649292208896581126183997 33993484578336217922318999)
    ·
      refine ⟨50990226867504326883478499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33993484578336217922318999 50990226867504326883478499)
      ·
        refine ⟨76485340301256490325217749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50990226867504326883478499 76485340301256490325217749)
        ·
          refine ⟨1792625163310698991997291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 76485340301256490325217749 1792625163310698991997291)
          ·
            refine ⟨2688937744966048487995937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1792625163310698991997291 2688937744966048487995937)
            ·
              refine ⟨2016703308724536365996953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2688937744966048487995937 2016703308724536365996953)
              ·
                refine ⟨1512527481543402274497715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2016703308724536365996953 1512527481543402274497715)
                ·
                  refine ⟨2268791222315103411746573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1512527481543402274497715 2268791222315103411746573)
                  ·
                    refine ⟨850796708368163779404965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2268791222315103411746573 850796708368163779404965)
                    ·
                      rfl

theorem cell22_2485381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 2, 2, 1, 3].length) (baseStart_2485381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2485381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2485381 prefixEnd_2485381 := by exact prefixLift 2485381
  have htrace : WordTrace (prefixWord ++ tailWord_2485381) baseStart_2485381 baseEnd_2485381 := by
    simpa [prefixWord, tailWord_2485381, baseEnd_2485381] using wordTrace_append hprefix tailTrace_2485381
  have hstable : (prefixWord ++ tailWord_2485381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2485381).length < 2 ^ (prefixWord ++ tailWord_2485381).sum := by decide
  have hdescent : baseEnd_2485381 < baseStart_2485381 := by decide
  rcases family_descends (prefixWord ++ tailWord_2485381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2485454 : List Nat := [4, 1, 1, 1, 5, 1, 3, 1, 2, 3]
def baseStart_2485454 : Nat := 118140960795 + 2485454 * 2 ^ 59
def prefixEnd_2485454 : Nat := 4983230072969 + 3 ^ 40 * 2485454 * 2
def baseEnd_2485454 : Nat := 850821697760015922329741

theorem tailTrace_2485454 : CollatzResearch.WordTrace tailWord_2485454 prefixEnd_2485454 850821697760015922329741 := by
  unfold tailWord_2485454
  simp only [CollatzResearch.WordTrace]
  refine ⟨11331494342204014324198927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60434636491754743062394277 11331494342204014324198927)
  ·
    refine ⟨16997241513306021486298391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11331494342204014324198927 16997241513306021486298391)
    ·
      refine ⟨25495862269959032229447587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16997241513306021486298391 25495862269959032229447587)
      ·
        refine ⟨38243793404938548344171381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25495862269959032229447587 38243793404938548344171381)
        ·
          refine ⟨3585355631712988907266067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38243793404938548344171381 3585355631712988907266067)
          ·
            refine ⟨5378033447569483360899101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3585355631712988907266067 5378033447569483360899101)
            ·
              refine ⟨2016762542838556260337163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5378033447569483360899101 2016762542838556260337163)
              ·
                refine ⟨3025143814257834390505745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2016762542838556260337163 3025143814257834390505745)
                ·
                  refine ⟨2268857860693375792879309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3025143814257834390505745 2268857860693375792879309)
                  ·
                    refine ⟨850821697760015922329741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2268857860693375792879309 850821697760015922329741)
                    ·
                      rfl

theorem cell22_2485454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 3, 1, 2, 3].length) (baseStart_2485454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2485454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2485454 prefixEnd_2485454 := by exact prefixLift 2485454
  have htrace : WordTrace (prefixWord ++ tailWord_2485454) baseStart_2485454 baseEnd_2485454 := by
    simpa [prefixWord, tailWord_2485454, baseEnd_2485454] using wordTrace_append hprefix tailTrace_2485454
  have hstable : (prefixWord ++ tailWord_2485454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2485454).length < 2 ^ (prefixWord ++ tailWord_2485454).sum := by decide
  have hdescent : baseEnd_2485454 < baseStart_2485454 := by decide
  rcases family_descends (prefixWord ++ tailWord_2485454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2485557 : List Nat := [1, 3, 3, 1, 2, 3, 1, 4, 4]
def baseStart_2485557 : Nat := 118140960795 + 2485557 * 2 ^ 59
def prefixEnd_2485557 : Nat := 4983230072969 + 3 ^ 40 * 2485557 * 2
def baseEnd_2485557 : Nat := 283618985588319329001475

theorem tailTrace_2485557 : CollatzResearch.WordTrace tailWord_2485557 prefixEnd_2485557 283618985588319329001475 := by
  unfold tailWord_2485557
  simp only [CollatzResearch.WordTrace]
  refine ⟨90655711456258963184590925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60437140970839308789727283 90655711456258963184590925)
  ·
    refine ⟨33995891796097111194221597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90655711456258963184590925 33995891796097111194221597)
    ·
      refine ⟨12748459423536416697833099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33995891796097111194221597 12748459423536416697833099)
      ·
        refine ⟨19122689135304625046749649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12748459423536416697833099 19122689135304625046749649)
        ·
          refine ⟨14342016851478468785062237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19122689135304625046749649 14342016851478468785062237)
          ·
            refine ⟨5378256319304425794398339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14342016851478468785062237 5378256319304425794398339)
            ·
              refine ⟨8067384478956638691597509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5378256319304425794398339 8067384478956638691597509)
              ·
                refine ⟨1512634589804369754674533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8067384478956638691597509 1512634589804369754674533)
                ·
                  refine ⟨283618985588319329001475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1512634589804369754674533 283618985588319329001475)
                  ·
                    rfl

theorem cell22_2485557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 4, 4].length) (baseStart_2485557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2485557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2485557 prefixEnd_2485557 := by exact prefixLift 2485557
  have htrace : WordTrace (prefixWord ++ tailWord_2485557) baseStart_2485557 baseEnd_2485557 := by
    simpa [prefixWord, tailWord_2485557, baseEnd_2485557] using wordTrace_append hprefix tailTrace_2485557
  have hstable : (prefixWord ++ tailWord_2485557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2485557).length < 2 ^ (prefixWord ++ tailWord_2485557).sum := by decide
  have hdescent : baseEnd_2485557 < baseStart_2485557 := by decide
  rcases family_descends (prefixWord ++ tailWord_2485557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2485572 : List Nat := [2, 3, 4, 1, 1, 1, 1, 3, 1, 5]
def baseStart_2485572 : Nat := 118140960795 + 2485572 * 2 ^ 59
def prefixEnd_2485572 : Nat := 4983230072969 + 3 ^ 40 * 2485572 * 2
def baseEnd_2485572 : Nat := 850862091571502947879379

theorem tailTrace_2485572 : CollatzResearch.WordTrace tailWord_2485572 prefixEnd_2485572 850862091571502947879379 := by
  unfold tailWord_2485572
  simp only [CollatzResearch.WordTrace]
  refine ⟨45328129275602310373193485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60437505700803080497591313 45328129275602310373193485)
  ·
    refine ⟨16998048478350866389947557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45328129275602310373193485 16998048478350866389947557)
    ·
      refine ⟨3187134089690787448115167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16998048478350866389947557 3187134089690787448115167)
      ·
        refine ⟨4780701134536181172172751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3187134089690787448115167 4780701134536181172172751)
        ·
          refine ⟨7171051701804271758259127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4780701134536181172172751 7171051701804271758259127)
          ·
            refine ⟨10756577552706407637388691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7171051701804271758259127 10756577552706407637388691)
            ·
              refine ⟨16134866329059611456083037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10756577552706407637388691 16134866329059611456083037)
              ·
                refine ⟨6050574873397354296031139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16134866329059611456083037 6050574873397354296031139)
                ·
                  refine ⟨9075862310096031444046709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6050574873397354296031139 9075862310096031444046709)
                  ·
                    refine ⟨850862091571502947879379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9075862310096031444046709 850862091571502947879379)
                    ·
                      rfl

theorem cell22_2485572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_2485572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2485572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2485572 prefixEnd_2485572 := by exact prefixLift 2485572
  have htrace : WordTrace (prefixWord ++ tailWord_2485572) baseStart_2485572 baseEnd_2485572 := by
    simpa [prefixWord, tailWord_2485572, baseEnd_2485572] using wordTrace_append hprefix tailTrace_2485572
  have hstable : (prefixWord ++ tailWord_2485572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2485572).length < 2 ^ (prefixWord ++ tailWord_2485572).sum := by decide
  have hdescent : baseEnd_2485572 < baseStart_2485572 := by decide
  rcases family_descends (prefixWord ++ tailWord_2485572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2485585 : List Nat := [1, 2, 2, 1, 4, 1, 5, 6]
def baseStart_2485585 : Nat := 118140960795 + 2485585 * 2 ^ 59
def prefixEnd_2485585 : Nat := 4983230072969 + 3 ^ 40 * 2485585 * 2
def baseEnd_2485585 : Nat := 94540726859686138589371

theorem tailTrace_2485585 : CollatzResearch.WordTrace tailWord_2485585 prefixEnd_2485585 94540726859686138589371 := by
  unfold tailWord_2485585
  simp only [CollatzResearch.WordTrace]
  refine ⟨90656732700157523966610209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60437821800105015977740139 90656732700157523966610209)
  ·
    refine ⟨67992549525118142974957657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90656732700157523966610209 67992549525118142974957657)
    ·
      refine ⟨50994412143838607231218243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67992549525118142974957657 50994412143838607231218243)
      ·
        refine ⟨76491618215757910846827365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50994412143838607231218243 76491618215757910846827365)
        ·
          refine ⟨14342178415454608283780131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76491618215757910846827365 14342178415454608283780131)
          ·
            refine ⟨21513267623181912425670197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14342178415454608283780131 21513267623181912425670197)
            ·
              refine ⟨2016868839673304289906581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21513267623181912425670197 2016868839673304289906581)
              ·
                refine ⟨94540726859686138589371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2016868839673304289906581 94540726859686138589371)
                ·
                  rfl

theorem cell22_2485585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 5, 6].length) (baseStart_2485585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2485585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2485585 prefixEnd_2485585 := by exact prefixLift 2485585
  have htrace : WordTrace (prefixWord ++ tailWord_2485585) baseStart_2485585 baseEnd_2485585 := by
    simpa [prefixWord, tailWord_2485585, baseEnd_2485585] using wordTrace_append hprefix tailTrace_2485585
  have hstable : (prefixWord ++ tailWord_2485585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2485585).length < 2 ^ (prefixWord ++ tailWord_2485585).sum := by decide
  have hdescent : baseEnd_2485585 < baseStart_2485585 := by decide
  rcases family_descends (prefixWord ++ tailWord_2485585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2485722 : List Nat := [3, 1, 1, 2, 3, 2, 2, 2, 2, 4]
def baseStart_2485722 : Nat := 118140960795 + 2485722 * 2 ^ 59
def prefixEnd_2485722 : Nat := 4983230072969 + 3 ^ 40 * 2485722 * 2
def baseEnd_2485722 : Nat := 850913439636952556628919

theorem tailTrace_2485722 : CollatzResearch.WordTrace tailWord_2485722 prefixEnd_2485722 850913439636952556628919 := by
  unfold tailWord_2485722
  simp only [CollatzResearch.WordTrace]
  refine ⟨22665432375165299091086855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60441153000440797576231613 22665432375165299091086855)
  ·
    refine ⟨33998148562747948636630283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22665432375165299091086855 33998148562747948636630283)
    ·
      refine ⟨50997222844121922954945425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33998148562747948636630283 50997222844121922954945425)
      ·
        refine ⟨38247917133091442216209069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50997222844121922954945425 38247917133091442216209069)
        ·
          refine ⟨14342968924909290831078401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38247917133091442216209069 14342968924909290831078401)
          ·
            refine ⟨10757226693681968123308801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14342968924909290831078401 10757226693681968123308801)
            ·
              refine ⟨8067920020261476092481601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10757226693681968123308801 8067920020261476092481601)
              ·
                refine ⟨6050940015196107069361201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8067920020261476092481601 6050940015196107069361201)
                ·
                  refine ⟨4538205011397080302020901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6050940015196107069361201 4538205011397080302020901)
                  ·
                    refine ⟨850913439636952556628919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4538205011397080302020901 850913439636952556628919)
                    ·
                      rfl

theorem cell22_2485722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 2, 2, 4].length) (baseStart_2485722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2485722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2485722 prefixEnd_2485722 := by exact prefixLift 2485722
  have htrace : WordTrace (prefixWord ++ tailWord_2485722) baseStart_2485722 baseEnd_2485722 := by
    simpa [prefixWord, tailWord_2485722, baseEnd_2485722] using wordTrace_append hprefix tailTrace_2485722
  have hstable : (prefixWord ++ tailWord_2485722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2485722).length < 2 ^ (prefixWord ++ tailWord_2485722).sum := by decide
  have hdescent : baseEnd_2485722 < baseStart_2485722 := by decide
  rcases family_descends (prefixWord ++ tailWord_2485722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2485752 : List Nat := [2, 1, 2, 1, 1, 5, 1, 1, 5, 3]
def baseStart_2485752 : Nat := 118140960795 + 2485752 * 2 ^ 59
def prefixEnd_2485752 : Nat := 4983230072969 + 3 ^ 40 * 2485752 * 2
def baseEnd_2485752 : Nat := 850923709250042478378827

theorem tailTrace_2485752 : CollatzResearch.WordTrace tailWord_2485752 prefixEnd_2485752 850923709250042478378827 := by
  unfold tailWord_2485752
  simp only [CollatzResearch.WordTrace]
  refine ⟨45331411845276255743969755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60441882460368340991959673 45331411845276255743969755)
  ·
    refine ⟨67997117767914383615954633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45331411845276255743969755 67997117767914383615954633)
    ·
      refine ⟨50997838325935787711965975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67997117767914383615954633 50997838325935787711965975)
      ·
        refine ⟨76496757488903681567948963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50997838325935787711965975 76496757488903681567948963)
        ·
          refine ⟨114745136233355522351923445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76496757488903681567948963 114745136233355522351923445)
          ·
            refine ⟨10757356521877080220492823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 114745136233355522351923445 10757356521877080220492823)
            ·
              refine ⟨16136034782815620330739235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10757356521877080220492823 16136034782815620330739235)
              ·
                refine ⟨24204052174223430496108853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16136034782815620330739235 24204052174223430496108853)
                ·
                  refine ⟨2269129891333446609010205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24204052174223430496108853 2269129891333446609010205)
                  ·
                    refine ⟨850923709250042478378827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2269129891333446609010205 850923709250042478378827)
                    ·
                      rfl

theorem cell22_2485752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 1, 5, 3].length) (baseStart_2485752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2485752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2485752 prefixEnd_2485752 := by exact prefixLift 2485752
  have htrace : WordTrace (prefixWord ++ tailWord_2485752) baseStart_2485752 baseEnd_2485752 := by
    simpa [prefixWord, tailWord_2485752, baseEnd_2485752] using wordTrace_append hprefix tailTrace_2485752
  have hstable : (prefixWord ++ tailWord_2485752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2485752).length < 2 ^ (prefixWord ++ tailWord_2485752).sum := by decide
  have hdescent : baseEnd_2485752 < baseStart_2485752 := by decide
  rcases family_descends (prefixWord ++ tailWord_2485752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2485765 : List Nat := [1, 3, 1, 1, 2, 2, 1, 4, 7]
def baseStart_2485765 : Nat := 118140960795 + 2485765 * 2 ^ 59
def prefixEnd_2485765 : Nat := 4983230072969 + 3 ^ 40 * 2485765 * 2
def baseEnd_2485765 : Nat := 283642719805238259267929

theorem tailTrace_2485765 : CollatzResearch.WordTrace tailWord_2485765 prefixEnd_2485765 283642719805238259267929 := by
  unfold tailWord_2485765
  simp only [CollatzResearch.WordTrace]
  refine ⟨90663297839505414708162749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60442198559670276472108499 90663297839505414708162749)
  ·
    refine ⟨33998736689814530515561031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90663297839505414708162749 33998736689814530515561031)
    ·
      refine ⟨50998105034721795773341547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33998736689814530515561031 50998105034721795773341547)
      ·
        refine ⟨76497157552082693660012321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50998105034721795773341547 76497157552082693660012321)
        ·
          refine ⟨57372868164062020245009241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76497157552082693660012321 57372868164062020245009241)
          ·
            refine ⟨43029651123046515183756931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57372868164062020245009241 43029651123046515183756931)
            ·
              refine ⟨64544476684569772775635397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43029651123046515183756931 64544476684569772775635397)
              ·
                refine ⟨12102089378356832395431637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64544476684569772775635397 12102089378356832395431637)
                ·
                  refine ⟨283642719805238259267929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12102089378356832395431637 283642719805238259267929)
                  ·
                    rfl

theorem cell22_2485765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 4, 7].length) (baseStart_2485765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2485765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2485765 prefixEnd_2485765 := by exact prefixLift 2485765
  have htrace : WordTrace (prefixWord ++ tailWord_2485765) baseStart_2485765 baseEnd_2485765 := by
    simpa [prefixWord, tailWord_2485765, baseEnd_2485765] using wordTrace_append hprefix tailTrace_2485765
  have hstable : (prefixWord ++ tailWord_2485765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2485765).length < 2 ^ (prefixWord ++ tailWord_2485765).sum := by decide
  have hdescent : baseEnd_2485765 < baseStart_2485765 := by decide
  rcases family_descends (prefixWord ++ tailWord_2485765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2485820 : List Nat := [2, 2, 2, 2, 5, 1, 1, 3, 1, 3]
def baseStart_2485820 : Nat := 118140960795 + 2485820 * 2 ^ 59
def prefixEnd_2485820 : Nat := 4983230072969 + 3 ^ 40 * 2485820 * 2
def baseEnd_2485820 : Nat := 850946987039712967678619

theorem tailTrace_2485820 : CollatzResearch.WordTrace tailWord_2485820 prefixEnd_2485820 850946987039712967678619 := by
  unfold tailWord_2485820
  simp only [CollatzResearch.WordTrace]
  refine ⟨45332651927153079550707457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60443535902870772734276609 45332651927153079550707457)
  ·
    refine ⟨33999488945364809663030593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45332651927153079550707457 33999488945364809663030593)
    ·
      refine ⟨25499616709023607247272945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33999488945364809663030593 25499616709023607247272945)
      ·
        refine ⟨19124712531767705435454709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25499616709023607247272945 19124712531767705435454709)
        ·
          refine ⟨1792941799853222384573879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19124712531767705435454709 1792941799853222384573879)
          ·
            refine ⟨2689412699779833576860819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1792941799853222384573879 2689412699779833576860819)
            ·
              refine ⟨4034119049669750365291229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2689412699779833576860819 4034119049669750365291229)
              ·
                refine ⟨1512794643626156386984211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4034119049669750365291229 1512794643626156386984211)
                ·
                  refine ⟨2269191965439234580476317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1512794643626156386984211 2269191965439234580476317)
                  ·
                    refine ⟨850946987039712967678619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2269191965439234580476317 850946987039712967678619)
                    ·
                      rfl

theorem cell22_2485820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 3, 1, 3].length) (baseStart_2485820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2485820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2485820 prefixEnd_2485820 := by exact prefixLift 2485820
  have htrace : WordTrace (prefixWord ++ tailWord_2485820) baseStart_2485820 baseEnd_2485820 := by
    simpa [prefixWord, tailWord_2485820, baseEnd_2485820] using wordTrace_append hprefix tailTrace_2485820
  have hstable : (prefixWord ++ tailWord_2485820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2485820).length < 2 ^ (prefixWord ++ tailWord_2485820).sum := by decide
  have hdescent : baseEnd_2485820 < baseStart_2485820 := by decide
  rcases family_descends (prefixWord ++ tailWord_2485820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2485857 : List Nat := [1, 2, 3, 1, 1, 3, 1, 2, 4, 4]
def baseStart_2485857 : Nat := 118140960795 + 2485857 * 2 ^ 59
def prefixEnd_2485857 : Nat := 4983230072969 + 3 ^ 40 * 2485857 * 2
def baseEnd_2485857 : Nat := 850959652895857204503505

theorem tailTrace_2485857 : CollatzResearch.WordTrace tailWord_2485857 prefixEnd_2485857 850959652895857204503505 := by
  unfold tailWord_2485857
  simp only [CollatzResearch.WordTrace]
  refine ⟨90666653355172114420511825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60444435570114742947007883 90666653355172114420511825)
  ·
    refine ⟨67999990016379085815383869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90666653355172114420511825 67999990016379085815383869)
    ·
      refine ⟨25499996256142157180768951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67999990016379085815383869 25499996256142157180768951)
      ·
        refine ⟨38249994384213235771153427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25499996256142157180768951 38249994384213235771153427)
        ·
          refine ⟨57374991576319853656730141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38249994384213235771153427 57374991576319853656730141)
          ·
            refine ⟨21515621841119945121273803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57374991576319853656730141 21515621841119945121273803)
            ·
              refine ⟨32273432761679917681910705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21515621841119945121273803 32273432761679917681910705)
              ·
                refine ⟨24205074571259938261433029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32273432761679917681910705 24205074571259938261433029)
                ·
                  refine ⟨4538451482111238424018693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24205074571259938261433029 4538451482111238424018693)
                  ·
                    refine ⟨850959652895857204503505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4538451482111238424018693 850959652895857204503505)
                    ·
                      rfl

theorem cell22_2485857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 2, 4, 4].length) (baseStart_2485857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2485857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2485857 prefixEnd_2485857 := by exact prefixLift 2485857
  have htrace : WordTrace (prefixWord ++ tailWord_2485857) baseStart_2485857 baseEnd_2485857 := by
    simpa [prefixWord, tailWord_2485857, baseEnd_2485857] using wordTrace_append hprefix tailTrace_2485857
  have hstable : (prefixWord ++ tailWord_2485857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2485857).length < 2 ^ (prefixWord ++ tailWord_2485857).sum := by decide
  have hdescent : baseEnd_2485857 < baseStart_2485857 := by decide
  rcases family_descends (prefixWord ++ tailWord_2485857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
