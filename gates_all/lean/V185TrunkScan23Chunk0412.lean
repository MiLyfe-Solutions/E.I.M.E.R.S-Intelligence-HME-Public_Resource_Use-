import V185TrunkScan23Chunk0411

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2436041 : List Nat := [1, 2, 1, 1, 2, 1, 2, 1, 6, 6]
def baseStart_2436041 : Nat := 118140960795 + 2436041 * 2 ^ 59
def prefixEnd_2436041 : Nat := 4983230072969 + 3 ^ 40 * 2436041 * 2
def baseEnd_2436041 : Nat := 416953309019802904028119

theorem tailTrace_2436041 : CollatzResearch.WordTrace tailWord_2436041 prefixEnd_2436041 416953309019802904028119 := by
  unfold tailWord_2436041
  simp only [CollatzResearch.WordTrace]
  refine ⟨88849714567646974525059977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59233143045097983016706651 88849714567646974525059977)
  ·
    refine ⟨66637285925735230893794983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88849714567646974525059977 66637285925735230893794983)
    ·
      refine ⟨99955928888602846340692475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66637285925735230893794983 99955928888602846340692475)
      ·
        refine ⟨149933893332904269511038713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99955928888602846340692475 149933893332904269511038713)
        ·
          refine ⟨112450419999678202133279035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149933893332904269511038713 112450419999678202133279035)
          ·
            refine ⟨168675629999517303199918553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112450419999678202133279035 168675629999517303199918553)
            ·
              refine ⟨126506722499637977399938915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 168675629999517303199918553 126506722499637977399938915)
              ·
                refine ⟨189760083749456966099908373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126506722499637977399938915 189760083749456966099908373)
                ·
                  refine ⟨8895003925755795285933205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 189760083749456966099908373 8895003925755795285933205)
                  ·
                    refine ⟨416953309019802904028119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8895003925755795285933205 416953309019802904028119)
                    ·
                      rfl

theorem cell23_2436041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 6, 6].length) (baseStart_2436041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2436041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2436041 prefixEnd_2436041 := by exact prefixLift 2436041
  have htrace : WordTrace (prefixWord ++ tailWord_2436041) baseStart_2436041 baseEnd_2436041 := by
    simpa [prefixWord, tailWord_2436041, baseEnd_2436041] using wordTrace_append hprefix tailTrace_2436041
  have hstable : (prefixWord ++ tailWord_2436041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2436041).length < 2 ^ (prefixWord ++ tailWord_2436041).sum := by decide
  have hdescent : baseEnd_2436041 < baseStart_2436041 := by decide
  rcases family_descends (prefixWord ++ tailWord_2436041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2436058 : List Nat := [3, 1, 1, 2, 4, 1, 1, 2, 2, 6]
def baseStart_2436058 : Nat := 118140960795 + 2436058 * 2 ^ 59
def prefixEnd_2436058 : Nat := 4983230072969 + 3 ^ 40 * 2436058 * 2
def baseEnd_2436058 : Nat := 416956218743511715190593

theorem tailTrace_2436058 : CollatzResearch.WordTrace tailWord_2436058 prefixEnd_2436058 416956218743511715190593 := by
  unfold tailWord_2436058
  simp only [CollatzResearch.WordTrace]
  refine ⟨22212583652146346607107207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59233556405723590952285885 22212583652146346607107207)
  ·
    refine ⟨33318875478219519910660811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22212583652146346607107207 33318875478219519910660811)
    ·
      refine ⟨49978313217329279865991217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33318875478219519910660811 49978313217329279865991217)
      ·
        refine ⟨37483734912996959899493413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49978313217329279865991217 37483734912996959899493413)
        ·
          refine ⟨7028200296186929981155015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37483734912996959899493413 7028200296186929981155015)
          ·
            refine ⟨10542300444280394971732523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7028200296186929981155015 10542300444280394971732523)
            ·
              refine ⟨15813450666420592457598785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10542300444280394971732523 15813450666420592457598785)
              ·
                refine ⟨11860087999815444343199089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15813450666420592457598785 11860087999815444343199089)
                ·
                  refine ⟨8895065999861583257399317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11860087999815444343199089 8895065999861583257399317)
                  ·
                    refine ⟨416956218743511715190593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8895065999861583257399317 416956218743511715190593)
                    ·
                      rfl

theorem cell23_2436058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 2, 2, 6].length) (baseStart_2436058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2436058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2436058 prefixEnd_2436058 := by exact prefixLift 2436058
  have htrace : WordTrace (prefixWord ++ tailWord_2436058) baseStart_2436058 baseEnd_2436058 := by
    simpa [prefixWord, tailWord_2436058, baseEnd_2436058] using wordTrace_append hprefix tailTrace_2436058
  have hstable : (prefixWord ++ tailWord_2436058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2436058).length < 2 ^ (prefixWord ++ tailWord_2436058).sum := by decide
  have hdescent : baseEnd_2436058 < baseStart_2436058 := by decide
  rcases family_descends (prefixWord ++ tailWord_2436058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2436068 : List Nat := [2, 3, 1, 1, 1, 1, 2, 3, 2, 4, 3]
def baseStart_2436068 : Nat := 118140960795 + 2436068 * 2 ^ 59
def prefixEnd_2436068 : Nat := 4983230072969 + 3 ^ 40 * 2436068 * 2
def baseEnd_2436068 : Nat := 1250873791037080106446733

theorem tailTrace_2436068 : CollatzResearch.WordTrace tailWord_2436068 prefixEnd_2436068 1250873791037080106446733 := by
  unfold tailWord_2436068
  simp only [CollatzResearch.WordTrace]
  refine ⟨44425349669274579068146429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59233799559032772090861905 44425349669274579068146429)
  ·
    refine ⟨16659506125977967150554911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44425349669274579068146429 16659506125977967150554911)
    ·
      refine ⟨24989259188966950725832367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16659506125977967150554911 24989259188966950725832367)
      ·
        refine ⟨37483888783450426088748551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24989259188966950725832367 37483888783450426088748551)
        ·
          refine ⟨56225833175175639133122827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37483888783450426088748551 56225833175175639133122827)
          ·
            refine ⟨84338749762763458699684241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56225833175175639133122827 84338749762763458699684241)
            ·
              refine ⟨63254062322072594024763181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84338749762763458699684241 63254062322072594024763181)
              ·
                refine ⟨23720273370777222759286193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63254062322072594024763181 23720273370777222759286193)
                ·
                  refine ⟨17790205028082917069464645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23720273370777222759286193 17790205028082917069464645)
                  ·
                    refine ⟨3335663442765546950524621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17790205028082917069464645 3335663442765546950524621)
                    ·
                      refine ⟨1250873791037080106446733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3335663442765546950524621 1250873791037080106446733)
                      ·
                        rfl

theorem cell23_2436068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 3, 2, 4, 3].length) (baseStart_2436068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2436068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2436068 prefixEnd_2436068 := by exact prefixLift 2436068
  have htrace : WordTrace (prefixWord ++ tailWord_2436068) baseStart_2436068 baseEnd_2436068 := by
    simpa [prefixWord, tailWord_2436068, baseEnd_2436068] using wordTrace_append hprefix tailTrace_2436068
  have hstable : (prefixWord ++ tailWord_2436068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2436068).length < 2 ^ (prefixWord ++ tailWord_2436068).sum := by decide
  have hdescent : baseEnd_2436068 < baseStart_2436068 := by decide
  rcases family_descends (prefixWord ++ tailWord_2436068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2436122 : List Nat := [3, 1, 1, 3, 1, 2, 5, 2, 5]
def baseStart_2436122 : Nat := 118140960795 + 2436122 * 2 ^ 59
def prefixEnd_2436122 : Nat := 4983230072969 + 3 ^ 40 * 2436122 * 2
def baseEnd_2436122 : Nat := 138989057665824766130165

theorem tailTrace_2436122 : CollatzResearch.WordTrace tailWord_2436122 prefixEnd_2436122 138989057665824766130165 := by
  unfold tailWord_2436122
  simp only [CollatzResearch.WordTrace]
  refine ⟨22213167220088381339689655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59235112586902350239172413 22213167220088381339689655)
  ·
    refine ⟨33319750830132572009534483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22213167220088381339689655 33319750830132572009534483)
    ·
      refine ⟨49979626245198858014301725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33319750830132572009534483 49979626245198858014301725)
      ·
        refine ⟨18742359841949571755363147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49979626245198858014301725 18742359841949571755363147)
        ·
          refine ⟨28113539762924357633044721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18742359841949571755363147 28113539762924357633044721)
          ·
            refine ⟨21085154822193268224783541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28113539762924357633044721 21085154822193268224783541)
            ·
              refine ⟨1976733264580618896073457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21085154822193268224783541 1976733264580618896073457)
              ·
                refine ⟨1482549948435464172055093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1976733264580618896073457 1482549948435464172055093)
                ·
                  refine ⟨138989057665824766130165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1482549948435464172055093 138989057665824766130165)
                  ·
                    rfl

theorem cell23_2436122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 5, 2, 5].length) (baseStart_2436122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2436122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2436122 prefixEnd_2436122 := by exact prefixLift 2436122
  have htrace : WordTrace (prefixWord ++ tailWord_2436122) baseStart_2436122 baseEnd_2436122 := by
    simpa [prefixWord, tailWord_2436122, baseEnd_2436122] using wordTrace_append hprefix tailTrace_2436122
  have hstable : (prefixWord ++ tailWord_2436122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2436122).length < 2 ^ (prefixWord ++ tailWord_2436122).sum := by decide
  have hdescent : baseEnd_2436122 < baseStart_2436122 := by decide
  rcases family_descends (prefixWord ++ tailWord_2436122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2436168 : List Nat := [2, 1, 3, 1, 1, 1, 4, 1, 2, 1, 6]
def baseStart_2436168 : Nat := 118140960795 + 2436168 * 2 ^ 59
def prefixEnd_2436168 : Nat := 4983230072969 + 3 ^ 40 * 2436168 * 2
def baseEnd_2436168 : Nat := 1250925139102529715196273

theorem tailTrace_2436168 : CollatzResearch.WordTrace tailWord_2436168 prefixEnd_2436168 1250925139102529715196273 := by
  unfold tailWord_2436168
  simp only [CollatzResearch.WordTrace]
  refine ⟨44427173319093437607466579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59236231092124583476622105 44427173319093437607466579)
  ·
    refine ⟨66640759978640156411199869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44427173319093437607466579 66640759978640156411199869)
    ·
      refine ⟨24990284991990058654199951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66640759978640156411199869 24990284991990058654199951)
      ·
        refine ⟨37485427487985087981299927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24990284991990058654199951 37485427487985087981299927)
        ·
          refine ⟨56228141231977631971949891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37485427487985087981299927 56228141231977631971949891)
          ·
            refine ⟨84342211847966447957924837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56228141231977631971949891 84342211847966447957924837)
            ·
              refine ⟨15814164721493708992110907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 84342211847966447957924837 15814164721493708992110907)
              ·
                refine ⟨23721247082240563488166361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15814164721493708992110907 23721247082240563488166361)
                ·
                  refine ⟨17790935311680422616124771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23721247082240563488166361 17790935311680422616124771)
                  ·
                    refine ⟨26686402967520633924187157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17790935311680422616124771 26686402967520633924187157)
                    ·
                      refine ⟨1250925139102529715196273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26686402967520633924187157 1250925139102529715196273)
                      ·
                        rfl

theorem cell23_2436168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 1, 2, 1, 6].length) (baseStart_2436168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2436168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2436168 prefixEnd_2436168 := by exact prefixLift 2436168
  have htrace : WordTrace (prefixWord ++ tailWord_2436168) baseStart_2436168 baseEnd_2436168 := by
    simpa [prefixWord, tailWord_2436168, baseEnd_2436168] using wordTrace_append hprefix tailTrace_2436168
  have hstable : (prefixWord ++ tailWord_2436168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2436168).length < 2 ^ (prefixWord ++ tailWord_2436168).sum := by decide
  have hdescent : baseEnd_2436168 < baseStart_2436168 := by decide
  rcases family_descends (prefixWord ++ tailWord_2436168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2436229 : List Nat := [1, 3, 1, 1, 7, 1, 1, 2, 6]
def baseStart_2436229 : Nat := 118140960795 + 2436229 * 2 ^ 59
def prefixEnd_2436229 : Nat := 4983230072969 + 3 ^ 40 * 2436229 * 2
def baseEnd_2436229 : Nat := 138995162380272664059277

theorem tailTrace_2436229 : CollatzResearch.WordTrace tailWord_2436229 prefixEnd_2436229 138995162380272664059277 := by
  unfold tailWord_2436229
  simp only [CollatzResearch.WordTrace]
  refine ⟨88856571490965882632903741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59237714327310588421935827 88856571490965882632903741)
  ·
    refine ⟨33321214309112205987338903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88856571490965882632903741 33321214309112205987338903)
    ·
      refine ⟨49981821463668308981008355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33321214309112205987338903 49981821463668308981008355)
      ·
        refine ⟨74972732195502463471512533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49981821463668308981008355 74972732195502463471512533)
        ·
          refine ⟨1757173410832088987613575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 74972732195502463471512533 1757173410832088987613575)
          ·
            refine ⟨2635760116248133481420363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1757173410832088987613575 2635760116248133481420363)
            ·
              refine ⟨3953640174372200222130545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2635760116248133481420363 3953640174372200222130545)
              ·
                refine ⟨2965230130779150166597909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3953640174372200222130545 2965230130779150166597909)
                ·
                  refine ⟨138995162380272664059277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2965230130779150166597909 138995162380272664059277)
                  ·
                    rfl

theorem cell23_2436229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 2, 6].length) (baseStart_2436229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2436229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2436229 prefixEnd_2436229 := by exact prefixLift 2436229
  have htrace : WordTrace (prefixWord ++ tailWord_2436229) baseStart_2436229 baseEnd_2436229 := by
    simpa [prefixWord, tailWord_2436229, baseEnd_2436229] using wordTrace_append hprefix tailTrace_2436229
  have hstable : (prefixWord ++ tailWord_2436229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2436229).length < 2 ^ (prefixWord ++ tailWord_2436229).sum := by decide
  have hdescent : baseEnd_2436229 < baseStart_2436229 := by decide
  rcases family_descends (prefixWord ++ tailWord_2436229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2436245 : List Nat := [1, 3, 2, 1, 1, 1, 2, 4, 3, 1, 4]
def baseStart_2436245 : Nat := 118140960795 + 2436245 * 2 ^ 59
def prefixEnd_2436245 : Nat := 4983230072969 + 3 ^ 40 * 2436245 * 2
def baseEnd_2436245 : Nat := 1250964677112925913933419

theorem tailTrace_2436245 : CollatzResearch.WordTrace tailWord_2436245 prefixEnd_2436245 1250964677112925913933419 := by
  unfold tailWord_2436245
  simp only [CollatzResearch.WordTrace]
  refine ⟨88857155058907917365486189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59238103372605278243657459 88857155058907917365486189)
  ·
    refine ⟨33321433147090469012057321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88857155058907917365486189 33321433147090469012057321)
    ·
      refine ⟨24991074860317851759042991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33321433147090469012057321 24991074860317851759042991)
      ·
        refine ⟨37486612290476777638564487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24991074860317851759042991 37486612290476777638564487)
        ·
          refine ⟨56229918435715166457846731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37486612290476777638564487 56229918435715166457846731)
          ·
            refine ⟨84344877653572749686770097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56229918435715166457846731 84344877653572749686770097)
            ·
              refine ⟨63258658240179562265077573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84344877653572749686770097 63258658240179562265077573)
              ·
                refine ⟨11860998420033667924702045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63258658240179562265077573 11860998420033667924702045)
                ·
                  refine ⟨4447874407512625471763267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11860998420033667924702045 4447874407512625471763267)
                  ·
                    refine ⟨6671811611268938207644901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4447874407512625471763267 6671811611268938207644901)
                    ·
                      refine ⟨1250964677112925913933419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6671811611268938207644901 1250964677112925913933419)
                      ·
                        rfl

theorem cell23_2436245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 4, 3, 1, 4].length) (baseStart_2436245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2436245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2436245 prefixEnd_2436245 := by exact prefixLift 2436245
  have htrace : WordTrace (prefixWord ++ tailWord_2436245) baseStart_2436245 baseEnd_2436245 := by
    simpa [prefixWord, tailWord_2436245, baseEnd_2436245] using wordTrace_append hprefix tailTrace_2436245
  have hstable : (prefixWord ++ tailWord_2436245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2436245).length < 2 ^ (prefixWord ++ tailWord_2436245).sum := by decide
  have hdescent : baseEnd_2436245 < baseStart_2436245 := by decide
  rcases family_descends (prefixWord ++ tailWord_2436245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2436273 : List Nat := [1, 2, 2, 5, 1, 3, 1, 3, 1, 1, 3]
def baseStart_2436273 : Nat := 118140960795 + 2436273 * 2 ^ 59
def prefixEnd_2436273 : Nat := 4983230072969 + 3 ^ 40 * 2436273 * 2
def baseEnd_2436273 : Nat := 1250979054571251804383291

theorem tailTrace_2436273 : CollatzResearch.WordTrace tailWord_2436273 prefixEnd_2436273 1250979054571251804383291 := by
  unfold tailWord_2436273
  simp only [CollatzResearch.WordTrace]
  refine ⟨88858176302806478147505473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59238784201870985431670315 88858176302806478147505473)
  ·
    refine ⟨66643632227104858610629105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88858176302806478147505473 66643632227104858610629105)
    ·
      refine ⟨49982724170328643957971829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66643632227104858610629105 49982724170328643957971829)
      ·
        refine ⟨4685880390968310371059859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 49982724170328643957971829 4685880390968310371059859)
        ·
          refine ⟨7028820586452465556589789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4685880390968310371059859 7028820586452465556589789)
          ·
            refine ⟨2635807719919674583721171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7028820586452465556589789 2635807719919674583721171)
            ·
              refine ⟨3953711579879511875581757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2635807719919674583721171 3953711579879511875581757)
              ·
                refine ⟨1482641842454816953343159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3953711579879511875581757 1482641842454816953343159)
                ·
                  refine ⟨2223962763682225430014739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1482641842454816953343159 2223962763682225430014739)
                  ·
                    refine ⟨3335944145523338145022109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2223962763682225430014739 3335944145523338145022109)
                    ·
                      refine ⟨1250979054571251804383291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3335944145523338145022109 1250979054571251804383291)
                      ·
                        rfl

theorem cell23_2436273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 3, 1, 1, 3].length) (baseStart_2436273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2436273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2436273 prefixEnd_2436273 := by exact prefixLift 2436273
  have htrace : WordTrace (prefixWord ++ tailWord_2436273) baseStart_2436273 baseEnd_2436273 := by
    simpa [prefixWord, tailWord_2436273, baseEnd_2436273] using wordTrace_append hprefix tailTrace_2436273
  have hstable : (prefixWord ++ tailWord_2436273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2436273).length < 2 ^ (prefixWord ++ tailWord_2436273).sum := by decide
  have hdescent : baseEnd_2436273 < baseStart_2436273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2436273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2436275 : List Nat := [1, 1, 1, 2, 3, 2, 2, 4, 1, 2, 4]
def baseStart_2436275 : Nat := 118140960795 + 2436275 * 2 ^ 59
def prefixEnd_2436275 : Nat := 4983230072969 + 3 ^ 40 * 2436275 * 2
def baseEnd_2436275 : Nat := 1250980081532560796558281

theorem tailTrace_2436275 : CollatzResearch.WordTrace tailWord_2436275 prefixEnd_2436275 1250980081532560796558281 := by
  unfold tailWord_2436275
  simp only [CollatzResearch.WordTrace]
  refine ⟨88858249248799232489078279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59238832832532821659385519 88858249248799232489078279)
  ·
    refine ⟨133287373873198848733617419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88858249248799232489078279 133287373873198848733617419)
    ·
      refine ⟨199931060809798273100426129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133287373873198848733617419 199931060809798273100426129)
      ·
        refine ⟨149948295607348704825319597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199931060809798273100426129 149948295607348704825319597)
        ·
          refine ⟨56230610852755764309494849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 149948295607348704825319597 56230610852755764309494849)
          ·
            refine ⟨42172958139566823232121137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56230610852755764309494849 42172958139566823232121137)
            ·
              refine ⟨31629718604675117424090853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42172958139566823232121137 31629718604675117424090853)
              ·
                refine ⟨5930572238376584517017035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31629718604675117424090853 5930572238376584517017035)
                ·
                  refine ⟨8895858357564876775525553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5930572238376584517017035 8895858357564876775525553)
                  ·
                    refine ⟨6671893768173657581644165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8895858357564876775525553 6671893768173657581644165)
                    ·
                      refine ⟨1250980081532560796558281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6671893768173657581644165 1250980081532560796558281)
                      ·
                        rfl

theorem cell23_2436275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 4, 1, 2, 4].length) (baseStart_2436275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2436275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2436275 prefixEnd_2436275 := by exact prefixLift 2436275
  have htrace : WordTrace (prefixWord ++ tailWord_2436275) baseStart_2436275 baseEnd_2436275 := by
    simpa [prefixWord, tailWord_2436275, baseEnd_2436275] using wordTrace_append hprefix tailTrace_2436275
  have hstable : (prefixWord ++ tailWord_2436275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2436275).length < 2 ^ (prefixWord ++ tailWord_2436275).sum := by decide
  have hdescent : baseEnd_2436275 < baseStart_2436275 := by decide
  rcases family_descends (prefixWord ++ tailWord_2436275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2436289 : List Nat := [1, 2, 6, 1, 1, 1, 2, 1, 4, 4]
def baseStart_2436289 : Nat := 118140960795 + 2436289 * 2 ^ 59
def prefixEnd_2436289 : Nat := 4983230072969 + 3 ^ 40 * 2436289 * 2
def baseEnd_2436289 : Nat := 416995756753907913927739

theorem tailTrace_2436289 : CollatzResearch.WordTrace tailWord_2436289 prefixEnd_2436289 416995756753907913927739 := by
  unfold tailWord_2436289
  simp only [CollatzResearch.WordTrace]
  refine ⟨88858759870748512880087921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59239173247165675253391947 88858759870748512880087921)
  ·
    refine ⟨66644069903061384660065941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88858759870748512880087921 66644069903061384660065941)
    ·
      refine ⟨3123940776706002405940591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 66644069903061384660065941 3123940776706002405940591)
      ·
        refine ⟨4685911165059003608910887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3123940776706002405940591 4685911165059003608910887)
        ·
          refine ⟨7028866747588505413366331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4685911165059003608910887 7028866747588505413366331)
          ·
            refine ⟨10543300121382758120049497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7028866747588505413366331 10543300121382758120049497)
            ·
              refine ⟨7907475091037068590037123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10543300121382758120049497 7907475091037068590037123)
              ·
                refine ⟨11861212636555602885055685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7907475091037068590037123 11861212636555602885055685)
                ·
                  refine ⟨2223977369354175540947941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11861212636555602885055685 2223977369354175540947941)
                  ·
                    refine ⟨416995756753907913927739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2223977369354175540947941 416995756753907913927739)
                    ·
                      rfl

theorem cell23_2436289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_2436289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2436289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2436289 prefixEnd_2436289 := by exact prefixLift 2436289
  have htrace : WordTrace (prefixWord ++ tailWord_2436289) baseStart_2436289 baseEnd_2436289 := by
    simpa [prefixWord, tailWord_2436289, baseEnd_2436289] using wordTrace_append hprefix tailTrace_2436289
  have hstable : (prefixWord ++ tailWord_2436289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2436289).length < 2 ^ (prefixWord ++ tailWord_2436289).sum := by decide
  have hdescent : baseEnd_2436289 < baseStart_2436289 := by decide
  rcases family_descends (prefixWord ++ tailWord_2436289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2436290 : List Nat := [3, 5, 1, 1, 2, 2, 1, 1, 3, 1, 3]
def baseStart_2436290 : Nat := 118140960795 + 2436290 * 2 ^ 59
def prefixEnd_2436290 : Nat := 4983230072969 + 3 ^ 40 * 2436290 * 2
def baseEnd_2436290 : Nat := 1250987783742378237870713

theorem tailTrace_2436290 : CollatzResearch.WordTrace tailWord_2436290 prefixEnd_2436290 1250987783742378237870713 := by
  unfold tailWord_2436290
  simp only [CollatzResearch.WordTrace]
  refine ⟨22214699085936222512718581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59239197562496593367249549 22214699085936222512718581)
  ·
    refine ⟨2082628039306520860567367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22214699085936222512718581 2082628039306520860567367)
    ·
      refine ⟨3123942058959781290851051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2082628039306520860567367 3123942058959781290851051)
      ·
        refine ⟨4685913088439671936276577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3123942058959781290851051 4685913088439671936276577)
        ·
          refine ⟨3514434816329753952207433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4685913088439671936276577 3514434816329753952207433)
          ·
            refine ⟨2635826112247315464155575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3514434816329753952207433 2635826112247315464155575)
            ·
              refine ⟨3953739168370973196233363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2635826112247315464155575 3953739168370973196233363)
              ·
                refine ⟨5930608752556459794350045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3953739168370973196233363 5930608752556459794350045)
                ·
                  refine ⟨2223978282208672422881267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5930608752556459794350045 2223978282208672422881267)
                  ·
                    refine ⟨3335967423313008634321901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2223978282208672422881267 3335967423313008634321901)
                    ·
                      refine ⟨1250987783742378237870713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3335967423313008634321901 1250987783742378237870713)
                      ·
                        rfl

theorem cell23_2436290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_2436290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2436290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2436290 prefixEnd_2436290 := by exact prefixLift 2436290
  have htrace : WordTrace (prefixWord ++ tailWord_2436290) baseStart_2436290 baseEnd_2436290 := by
    simpa [prefixWord, tailWord_2436290, baseEnd_2436290] using wordTrace_append hprefix tailTrace_2436290
  have hstable : (prefixWord ++ tailWord_2436290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2436290).length < 2 ^ (prefixWord ++ tailWord_2436290).sum := by decide
  have hdescent : baseEnd_2436290 < baseStart_2436290 := by decide
  rcases family_descends (prefixWord ++ tailWord_2436290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2436296 : List Nat := [2, 1, 3, 1, 2, 1, 2, 6, 1, 2, 2]
def baseStart_2436296 : Nat := 118140960795 + 2436296 * 2 ^ 59
def prefixEnd_2436296 : Nat := 4983230072969 + 3 ^ 40 * 2436296 * 2
def baseEnd_2436296 : Nat := 1250990864626305214395685

theorem tailTrace_2436296 : CollatzResearch.WordTrace tailWord_2436296 prefixEnd_2436296 1250990864626305214395685 := by
  unfold tailWord_2436296
  simp only [CollatzResearch.WordTrace]
  refine ⟨44429507590861576537796371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59239343454482102050395161 44429507590861576537796371)
  ·
    refine ⟨66644261386292364806694557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44429507590861576537796371 66644261386292364806694557)
    ·
      refine ⟨24991598019859636802510459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66644261386292364806694557 24991598019859636802510459)
      ·
        refine ⟨37487397029789455203765689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24991598019859636802510459 37487397029789455203765689)
        ·
          refine ⟨28115547772342091402824267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37487397029789455203765689 28115547772342091402824267)
          ·
            refine ⟨42173321658513137104236401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28115547772342091402824267 42173321658513137104236401)
            ·
              refine ⟨31629991243884852828177301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42173321658513137104236401 31629991243884852828177301)
              ·
                refine ⟨1482655839557102476320811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 31629991243884852828177301 1482655839557102476320811)
                ·
                  refine ⟨2223983759335653714481217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1482655839557102476320811 2223983759335653714481217)
                  ·
                    refine ⟨1667987819501740285860913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2223983759335653714481217 1667987819501740285860913)
                    ·
                      refine ⟨1250990864626305214395685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1667987819501740285860913 1250990864626305214395685)
                      ·
                        rfl

theorem cell23_2436296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 6, 1, 2, 2].length) (baseStart_2436296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2436296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2436296 prefixEnd_2436296 := by exact prefixLift 2436296
  have htrace : WordTrace (prefixWord ++ tailWord_2436296) baseStart_2436296 baseEnd_2436296 := by
    simpa [prefixWord, tailWord_2436296, baseEnd_2436296] using wordTrace_append hprefix tailTrace_2436296
  have hstable : (prefixWord ++ tailWord_2436296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2436296).length < 2 ^ (prefixWord ++ tailWord_2436296).sum := by decide
  have hdescent : baseEnd_2436296 < baseStart_2436296 := by decide
  rcases family_descends (prefixWord ++ tailWord_2436296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2436302 : List Nat := [4, 1, 1, 1, 5, 1, 2, 8]
def baseStart_2436302 : Nat := 118140960795 + 2436302 * 2 ^ 59
def prefixEnd_2436302 : Nat := 4983230072969 + 3 ^ 40 * 2436302 * 2
def baseEnd_2436302 : Nat := 46333109092971562626691

theorem tailTrace_2436302 : CollatzResearch.WordTrace tailWord_2436302 prefixEnd_2436302 46333109092971562626691 := by
  unfold tailWord_2436302
  simp only [CollatzResearch.WordTrace]
  refine ⟨11107404252462677012538895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59239489346467610733540773 11107404252462677012538895)
  ·
    refine ⟨16661106378694015518808343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11107404252462677012538895 16661106378694015518808343)
    ·
      refine ⟨24991659568041023278212515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16661106378694015518808343 24991659568041023278212515)
      ·
        refine ⟨37487489352061534917318773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24991659568041023278212515 37487489352061534917318773)
        ·
          refine ⟨3514452126755768898498635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 37487489352061534917318773 3514452126755768898498635)
          ·
            refine ⟨5271678190133653347747953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3514452126755768898498635 5271678190133653347747953)
            ·
              refine ⟨3953758642600240010810965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5271678190133653347747953 3953758642600240010810965)
              ·
                refine ⟨46333109092971562626691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3953758642600240010810965 46333109092971562626691)
                ·
                  rfl

theorem cell23_2436302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 8].length) (baseStart_2436302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2436302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2436302 prefixEnd_2436302 := by exact prefixLift 2436302
  have htrace : WordTrace (prefixWord ++ tailWord_2436302) baseStart_2436302 baseEnd_2436302 := by
    simpa [prefixWord, tailWord_2436302, baseEnd_2436302] using wordTrace_append hprefix tailTrace_2436302
  have hstable : (prefixWord ++ tailWord_2436302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2436302).length < 2 ^ (prefixWord ++ tailWord_2436302).sum := by decide
  have hdescent : baseEnd_2436302 < baseStart_2436302 := by decide
  rcases family_descends (prefixWord ++ tailWord_2436302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2436340 : List Nat := [2, 6, 1, 2, 1, 1, 2, 2, 2, 4]
def baseStart_2436340 : Nat := 118140960795 + 2436340 * 2 ^ 59
def prefixEnd_2436340 : Nat := 4983230072969 + 3 ^ 40 * 2436340 * 2
def baseEnd_2436340 : Nat := 417004485925034347415161

theorem tailTrace_2436340 : CollatzResearch.WordTrace tailWord_2436340 prefixEnd_2436340 417004485925034347415161 := by
  unfold tailWord_2436340
  simp only [CollatzResearch.WordTrace]
  refine ⟨44430309996781874295097237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59240413329042499060129649 44430309996781874295097237)
  ·
    refine ⟨2082670781099150357582683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 44430309996781874295097237 2082670781099150357582683)
    ·
      refine ⟨3124006171648725536374025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2082670781099150357582683 3124006171648725536374025)
      ·
        refine ⟨2343004628736544152280519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3124006171648725536374025 2343004628736544152280519)
        ·
          refine ⟨3514506943104816228420779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2343004628736544152280519 3514506943104816228420779)
          ·
            refine ⟨5271760414657224342631169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3514506943104816228420779 5271760414657224342631169)
            ·
              refine ⟨3953820310992918256973377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5271760414657224342631169 3953820310992918256973377)
              ·
                refine ⟨2965365233244688692730033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3953820310992918256973377 2965365233244688692730033)
                ·
                  refine ⟨2224023924933516519547525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2965365233244688692730033 2224023924933516519547525)
                  ·
                    refine ⟨417004485925034347415161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2224023924933516519547525 417004485925034347415161)
                    ·
                      rfl

theorem cell23_2436340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_2436340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2436340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2436340 prefixEnd_2436340 := by exact prefixLift 2436340
  have htrace : WordTrace (prefixWord ++ tailWord_2436340) baseStart_2436340 baseEnd_2436340 := by
    simpa [prefixWord, tailWord_2436340, baseEnd_2436340] using wordTrace_append hprefix tailTrace_2436340
  have hstable : (prefixWord ++ tailWord_2436340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2436340).length < 2 ^ (prefixWord ++ tailWord_2436340).sum := by decide
  have hdescent : baseEnd_2436340 < baseStart_2436340 := by decide
  rcases family_descends (prefixWord ++ tailWord_2436340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2436345 : List Nat := [1, 2, 1, 3, 1, 1, 4, 2, 2, 6]
def baseStart_2436345 : Nat := 118140960795 + 2436345 * 2 ^ 59
def prefixEnd_2436345 : Nat := 4983230072969 + 3 ^ 40 * 2436345 * 2
def baseEnd_2436345 : Nat := 417005341726125174227653

theorem tailTrace_2436345 : CollatzResearch.WordTrace tailWord_2436345 prefixEnd_2436345 417005341726125174227653 := by
  unfold tailWord_2436345
  simp only [CollatzResearch.WordTrace]
  refine ⟨88860802358545634444126489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59240534905697089629417659 88860802358545634444126489)
  ·
    refine ⟨66645601768909225833094867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88860802358545634444126489 66645601768909225833094867)
    ·
      refine ⟨99968402653363838749642301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66645601768909225833094867 99968402653363838749642301)
      ·
        refine ⟨37488150995011439531115863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99968402653363838749642301 37488150995011439531115863)
        ·
          refine ⟨56232226492517159296673795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37488150995011439531115863 56232226492517159296673795)
          ·
            refine ⟨84348339738775738945010693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56232226492517159296673795 84348339738775738945010693)
            ·
              refine ⟨15815313701020451052189505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 84348339738775738945010693 15815313701020451052189505)
              ·
                refine ⟨11861485275765338289142129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15815313701020451052189505 11861485275765338289142129)
                ·
                  refine ⟨8896113956824003716856597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11861485275765338289142129 8896113956824003716856597)
                  ·
                    refine ⟨417005341726125174227653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8896113956824003716856597 417005341726125174227653)
                    ·
                      rfl

theorem cell23_2436345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 2, 2, 6].length) (baseStart_2436345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2436345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2436345 prefixEnd_2436345 := by exact prefixLift 2436345
  have htrace : WordTrace (prefixWord ++ tailWord_2436345) baseStart_2436345 baseEnd_2436345 := by
    simpa [prefixWord, tailWord_2436345, baseEnd_2436345] using wordTrace_append hprefix tailTrace_2436345
  have hstable : (prefixWord ++ tailWord_2436345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2436345).length < 2 ^ (prefixWord ++ tailWord_2436345).sum := by decide
  have hdescent : baseEnd_2436345 < baseStart_2436345 := by decide
  rcases family_descends (prefixWord ++ tailWord_2436345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2436352 : List Nat := [2, 1, 1, 2, 1, 1, 3, 1, 5, 4, 2]
def baseStart_2436352 : Nat := 118140960795 + 2436352 * 2 ^ 59
def prefixEnd_2436352 : Nat := 4983230072969 + 3 ^ 40 * 2436352 * 2
def baseEnd_2436352 : Nat := 1251019619542956995295427

theorem tailTrace_2436352 : CollatzResearch.WordTrace tailWord_2436352 prefixEnd_2436352 1251019619542956995295427 := by
  unfold tailWord_2436352
  simp only [CollatzResearch.WordTrace]
  refine ⟨44430528834760137319815655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59240705113013516426420873 44430528834760137319815655)
  ·
    refine ⟨66645793252140205979723483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44430528834760137319815655 66645793252140205979723483)
    ·
      refine ⟨99968689878210308969585225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66645793252140205979723483 99968689878210308969585225)
      ·
        refine ⟨74976517408657731727188919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99968689878210308969585225 74976517408657731727188919)
        ·
          refine ⟨112464776112986597590783379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74976517408657731727188919 112464776112986597590783379)
          ·
            refine ⟨168697164169479896386175069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112464776112986597590783379 168697164169479896386175069)
            ·
              refine ⟨63261436563554961144815651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 168697164169479896386175069 63261436563554961144815651)
              ·
                refine ⟨94892154845332441717223477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63261436563554961144815651 94892154845332441717223477)
                ·
                  refine ⟨8896139516749916410989701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 94892154845332441717223477 8896139516749916410989701)
                  ·
                    refine ⟨1668026159390609327060569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8896139516749916410989701 1668026159390609327060569)
                    ·
                      refine ⟨1251019619542956995295427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1668026159390609327060569 1251019619542956995295427)
                      ·
                        rfl

theorem cell23_2436352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 5, 4, 2].length) (baseStart_2436352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2436352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2436352 prefixEnd_2436352 := by exact prefixLift 2436352
  have htrace : WordTrace (prefixWord ++ tailWord_2436352) baseStart_2436352 baseEnd_2436352 := by
    simpa [prefixWord, tailWord_2436352, baseEnd_2436352] using wordTrace_append hprefix tailTrace_2436352
  have hstable : (prefixWord ++ tailWord_2436352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2436352).length < 2 ^ (prefixWord ++ tailWord_2436352).sum := by decide
  have hdescent : baseEnd_2436352 < baseStart_2436352 := by decide
  rcases family_descends (prefixWord ++ tailWord_2436352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2436369 : List Nat := [1, 2, 2, 1, 1, 4, 4, 1, 1, 4, 2]
def baseStart_2436369 : Nat := 118140960795 + 2436369 * 2 ^ 59
def prefixEnd_2436369 : Nat := 4983230072969 + 3 ^ 40 * 2436369 * 2
def baseEnd_2436369 : Nat := 1251028348714083428782849

theorem tailTrace_2436369 : CollatzResearch.WordTrace tailWord_2436369 prefixEnd_2436369 1251028348714083428782849 := by
  unfold tailWord_2436369
  simp only [CollatzResearch.WordTrace]
  refine ⟨88861677710458686543000161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59241118473639124362000107 88861677710458686543000161)
  ·
    refine ⟨66646258282844014907250121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88861677710458686543000161 66646258282844014907250121)
    ·
      refine ⟨49984693712133011180437591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66646258282844014907250121 49984693712133011180437591)
      ·
        refine ⟨74977040568199516770656387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49984693712133011180437591 74977040568199516770656387)
        ·
          refine ⟨112465560852299275155984581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74977040568199516770656387 112465560852299275155984581)
          ·
            refine ⟨21087292659806114091747109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 112465560852299275155984581 21087292659806114091747109)
            ·
              refine ⟨3953867373713646392202583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21087292659806114091747109 3953867373713646392202583)
              ·
                refine ⟨5930801060570469588303875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3953867373713646392202583 5930801060570469588303875)
                ·
                  refine ⟨8896201590855704382455813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5930801060570469588303875 8896201590855704382455813)
                  ·
                    refine ⟨1668037798285444571710465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8896201590855704382455813 1668037798285444571710465)
                    ·
                      refine ⟨1251028348714083428782849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1668037798285444571710465 1251028348714083428782849)
                      ·
                        rfl

theorem cell23_2436369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 4, 2].length) (baseStart_2436369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2436369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2436369 prefixEnd_2436369 := by exact prefixLift 2436369
  have htrace : WordTrace (prefixWord ++ tailWord_2436369) baseStart_2436369 baseEnd_2436369 := by
    simpa [prefixWord, tailWord_2436369, baseEnd_2436369] using wordTrace_append hprefix tailTrace_2436369
  have hstable : (prefixWord ++ tailWord_2436369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2436369).length < 2 ^ (prefixWord ++ tailWord_2436369).sum := by decide
  have hdescent : baseEnd_2436369 < baseStart_2436369 := by decide
  rcases family_descends (prefixWord ++ tailWord_2436369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2436385 : List Nat := [1, 2, 3, 2, 1, 1, 1, 2, 1, 2, 7]
def baseStart_2436385 : Nat := 118140960795 + 2436385 * 2 ^ 59
def prefixEnd_2436385 : Nat := 4983230072969 + 3 ^ 40 * 2436385 * 2
def baseEnd_2436385 : Nat := 1251036564404555366182775

theorem tailTrace_2436385 : CollatzResearch.WordTrace tailWord_2436385 prefixEnd_2436385 1251036564404555366182775 := by
  unfold tailWord_2436385
  simp only [CollatzResearch.WordTrace]
  refine ⟨88862261278400721275582609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59241507518933814183721739 88862261278400721275582609)
  ·
    refine ⟨66646695958800540956686957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88862261278400721275582609 66646695958800540956686957)
    ·
      refine ⟨24992510984550202858757609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66646695958800540956686957 24992510984550202858757609)
      ·
        refine ⟨18744383238412652144068207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24992510984550202858757609 18744383238412652144068207)
        ·
          refine ⟨28116574857618978216102311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18744383238412652144068207 28116574857618978216102311)
          ·
            refine ⟨42174862286428467324153467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28116574857618978216102311 42174862286428467324153467)
            ·
              refine ⟨63262293429642700986230201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42174862286428467324153467 63262293429642700986230201)
              ·
                refine ⟨47446720072232025739672651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63262293429642700986230201 47446720072232025739672651)
                ·
                  refine ⟨71170080108348038609508977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47446720072232025739672651 71170080108348038609508977)
                  ·
                    refine ⟨53377560081261028957131733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 71170080108348038609508977 53377560081261028957131733)
                    ·
                      refine ⟨1251036564404555366182775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 53377560081261028957131733 1251036564404555366182775)
                      ·
                        rfl

theorem cell23_2436385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_2436385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2436385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2436385 prefixEnd_2436385 := by exact prefixLift 2436385
  have htrace : WordTrace (prefixWord ++ tailWord_2436385) baseStart_2436385 baseEnd_2436385 := by
    simpa [prefixWord, tailWord_2436385, baseEnd_2436385] using wordTrace_append hprefix tailTrace_2436385
  have hstable : (prefixWord ++ tailWord_2436385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2436385).length < 2 ^ (prefixWord ++ tailWord_2436385).sum := by decide
  have hdescent : baseEnd_2436385 < baseStart_2436385 := by decide
  rcases family_descends (prefixWord ++ tailWord_2436385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2436403 : List Nat := [1, 1, 1, 2, 5, 4, 1, 2, 2, 2, 2]
def baseStart_2436403 : Nat := 118140960795 + 2436403 * 2 ^ 59
def prefixEnd_2436403 : Nat := 4983230072969 + 3 ^ 40 * 2436403 * 2
def baseEnd_2436403 : Nat := 1251045807056336295757693

theorem tailTrace_2436403 : CollatzResearch.WordTrace tailWord_2436403 prefixEnd_2436403 1251045807056336295757693 := by
  unfold tailWord_2436403
  simp only [CollatzResearch.WordTrace]
  refine ⟨88862917792335510349737863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59241945194890340233158575 88862917792335510349737863)
  ·
    refine ⟨133294376688503265524606795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88862917792335510349737863 133294376688503265524606795)
    ·
      refine ⟨199941565032754898286910193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133294376688503265524606795 199941565032754898286910193)
      ·
        refine ⟨149956173774566173715182645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199941565032754898286910193 149956173774566173715182645)
        ·
          refine ⟨14058391291365578785798373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 149956173774566173715182645 14058391291365578785798373)
          ·
            refine ⟨2635948367131046022337195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14058391291365578785798373 2635948367131046022337195)
            ·
              refine ⟨3953922550696569033505793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2635948367131046022337195 3953922550696569033505793)
              ·
                refine ⟨2965441913022426775129345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3953922550696569033505793 2965441913022426775129345)
                ·
                  refine ⟨2224081434766820081347009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2965441913022426775129345 2224081434766820081347009)
                  ·
                    refine ⟨1668061076075115061010257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2224081434766820081347009 1668061076075115061010257)
                    ·
                      refine ⟨1251045807056336295757693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1668061076075115061010257 1251045807056336295757693)
                      ·
                        rfl

theorem cell23_2436403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 2, 2, 2, 2].length) (baseStart_2436403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2436403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2436403 prefixEnd_2436403 := by exact prefixLift 2436403
  have htrace : WordTrace (prefixWord ++ tailWord_2436403) baseStart_2436403 baseEnd_2436403 := by
    simpa [prefixWord, tailWord_2436403, baseEnd_2436403] using wordTrace_append hprefix tailTrace_2436403
  have hstable : (prefixWord ++ tailWord_2436403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2436403).length < 2 ^ (prefixWord ++ tailWord_2436403).sum := by decide
  have hdescent : baseEnd_2436403 < baseStart_2436403 := by decide
  rcases family_descends (prefixWord ++ tailWord_2436403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2436409 : List Nat := [1, 2, 1, 6, 2, 1, 2, 1, 7]
def baseStart_2436409 : Nat := 118140960795 + 2436409 * 2 ^ 59
def prefixEnd_2436409 : Nat := 4983230072969 + 3 ^ 40 * 2436409 * 2
def baseEnd_2436409 : Nat := 139005431993362585809185

theorem tailTrace_2436409 : CollatzResearch.WordTrace tailWord_2436409 prefixEnd_2436409 139005431993362585809185 := by
  unfold tailWord_2436409
  simp only [CollatzResearch.WordTrace]
  refine ⟨88863136630313773374456281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59242091086875848916304187 88863136630313773374456281)
  ·
    refine ⟨66647352472735330030842211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88863136630313773374456281 66647352472735330030842211)
    ·
      refine ⟨99971028709102995046263317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66647352472735330030842211 99971028709102995046263317)
      ·
        refine ⟨4686141970739202892793593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 99971028709102995046263317 4686141970739202892793593)
        ·
          refine ⟨3514606478054402169595195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4686141970739202892793593 3514606478054402169595195)
          ·
            refine ⟨5271909717081603254392793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3514606478054402169595195 5271909717081603254392793)
            ·
              refine ⟨3953932287811202440794595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5271909717081603254392793 3953932287811202440794595)
              ·
                refine ⟨5930898431716803661191893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3953932287811202440794595 5930898431716803661191893)
                ·
                  refine ⟨139005431993362585809185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5930898431716803661191893 139005431993362585809185)
                  ·
                    rfl

theorem cell23_2436409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 1, 7].length) (baseStart_2436409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2436409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2436409 prefixEnd_2436409 := by exact prefixLift 2436409
  have htrace : WordTrace (prefixWord ++ tailWord_2436409) baseStart_2436409 baseEnd_2436409 := by
    simpa [prefixWord, tailWord_2436409, baseEnd_2436409] using wordTrace_append hprefix tailTrace_2436409
  have hstable : (prefixWord ++ tailWord_2436409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2436409).length < 2 ^ (prefixWord ++ tailWord_2436409).sum := by decide
  have hdescent : baseEnd_2436409 < baseStart_2436409 := by decide
  rcases family_descends (prefixWord ++ tailWord_2436409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2436435 : List Nat := [1, 1, 1, 2, 1, 1, 5, 1, 2, 8]
def baseStart_2436435 : Nat := 118140960795 + 2436435 * 2 ^ 59
def prefixEnd_2436435 : Nat := 4983230072969 + 3 ^ 40 * 2436435 * 2
def baseEnd_2436435 : Nat := 417020746145760056852515

theorem tailTrace_2436435 : CollatzResearch.WordTrace tailWord_2436435 prefixEnd_2436435 417020746145760056852515 := by
  unfold tailWord_2436435
  simp only [CollatzResearch.WordTrace]
  refine ⟨88864084928219579814902759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59242723285479719876601839 88864084928219579814902759)
  ·
    refine ⟨133296127392329369722354139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88864084928219579814902759 133296127392329369722354139)
    ·
      refine ⟨199944191088494054583531209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133296127392329369722354139 199944191088494054583531209)
      ·
        refine ⟨149958143316370540937648407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199944191088494054583531209 149958143316370540937648407)
        ·
          refine ⟨224937214974555811406472611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149958143316370540937648407 224937214974555811406472611)
          ·
            refine ⟨337405822461833717109708917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 224937214974555811406472611 337405822461833717109708917)
            ·
              refine ⟨31631795855796910979035211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 337405822461833717109708917 31631795855796910979035211)
              ·
                refine ⟨47447693783695366468552817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31631795855796910979035211 47447693783695366468552817)
                ·
                  refine ⟨35585770337771524851414613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47447693783695366468552817 35585770337771524851414613)
                  ·
                    refine ⟨417020746145760056852515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 35585770337771524851414613 417020746145760056852515)
                    ·
                      rfl

theorem cell23_2436435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 2, 8].length) (baseStart_2436435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2436435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2436435 prefixEnd_2436435 := by exact prefixLift 2436435
  have htrace : WordTrace (prefixWord ++ tailWord_2436435) baseStart_2436435 baseEnd_2436435 := by
    simpa [prefixWord, tailWord_2436435, baseEnd_2436435] using wordTrace_append hprefix tailTrace_2436435
  have hstable : (prefixWord ++ tailWord_2436435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2436435).length < 2 ^ (prefixWord ++ tailWord_2436435).sum := by decide
  have hdescent : baseEnd_2436435 < baseStart_2436435 := by decide
  rcases family_descends (prefixWord ++ tailWord_2436435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2436442 : List Nat := [3, 1, 1, 2, 1, 2, 4, 1, 1, 3, 4]
def baseStart_2436442 : Nat := 118140960795 + 2436442 * 2 ^ 59
def prefixEnd_2436442 : Nat := 4983230072969 + 3 ^ 40 * 2436442 * 2
def baseEnd_2436442 : Nat := 1251065832801861643170013

theorem tailTrace_2436442 : CollatzResearch.WordTrace tailWord_2436442 prefixEnd_2436442 1251065832801861643170013 := by
  unfold tailWord_2436442
  simp only [CollatzResearch.WordTrace]
  refine ⟨22216085059798555002601895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59242893492796146673605053 22216085059798555002601895)
  ·
    refine ⟨33324127589697832503902843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22216085059798555002601895 33324127589697832503902843)
    ·
      refine ⟨49986191384546748755854265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33324127589697832503902843 49986191384546748755854265)
      ·
        refine ⟨37489643538410061566890699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49986191384546748755854265 37489643538410061566890699)
        ·
          refine ⟨56234465307615092350336049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37489643538410061566890699 56234465307615092350336049)
          ·
            refine ⟨42175848980711319262752037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56234465307615092350336049 42175848980711319262752037)
            ·
              refine ⟨7907971683883372361766007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42175848980711319262752037 7907971683883372361766007)
              ·
                refine ⟨11861957525825058542649011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7907971683883372361766007 11861957525825058542649011)
                ·
                  refine ⟨17792936288737587813973517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11861957525825058542649011 17792936288737587813973517)
                  ·
                    refine ⟨6672351108276595430240069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17792936288737587813973517 6672351108276595430240069)
                    ·
                      refine ⟨1251065832801861643170013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6672351108276595430240069 1251065832801861643170013)
                      ·
                        rfl

theorem cell23_2436442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 1, 1, 3, 4].length) (baseStart_2436442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2436442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2436442 prefixEnd_2436442 := by exact prefixLift 2436442
  have htrace : WordTrace (prefixWord ++ tailWord_2436442) baseStart_2436442 baseEnd_2436442 := by
    simpa [prefixWord, tailWord_2436442, baseEnd_2436442] using wordTrace_append hprefix tailTrace_2436442
  have hstable : (prefixWord ++ tailWord_2436442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2436442).length < 2 ^ (prefixWord ++ tailWord_2436442).sum := by decide
  have hdescent : baseEnd_2436442 < baseStart_2436442 := by decide
  rcases family_descends (prefixWord ++ tailWord_2436442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2436520 : List Nat := [2, 1, 6, 1, 2, 1, 1, 4, 1, 4]
def baseStart_2436520 : Nat := 118140960795 + 2436520 * 2 ^ 59
def prefixEnd_2436520 : Nat := 4983230072969 + 3 ^ 40 * 2436520 * 2
def baseEnd_2436520 : Nat := 417035294764304112664885

theorem tailTrace_2436520 : CollatzResearch.WordTrace tailWord_2436520 prefixEnd_2436520 417035294764304112664885 := by
  unfold tailWord_2436520
  simp only [CollatzResearch.WordTrace]
  refine ⟨44433592566455819665873507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59244790088607759554498009 44433592566455819665873507)
  ·
    refine ⟨66650388849683729498810261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44433592566455819665873507 66650388849683729498810261)
    ·
      refine ⟨3124236977328924820256731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 66650388849683729498810261 3124236977328924820256731)
      ·
        refine ⟨4686355465993387230385097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3124236977328924820256731 4686355465993387230385097)
        ·
          refine ⟨3514766599495040422788823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4686355465993387230385097 3514766599495040422788823)
          ·
            refine ⟨5272149899242560634183235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3514766599495040422788823 5272149899242560634183235)
            ·
              refine ⟨7908224848863840951274853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5272149899242560634183235 7908224848863840951274853)
              ·
                refine ⟨1482792159161970178364035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7908224848863840951274853 1482792159161970178364035)
                ·
                  refine ⟨2224188238742955267546053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1482792159161970178364035 2224188238742955267546053)
                  ·
                    refine ⟨417035294764304112664885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2224188238742955267546053 417035294764304112664885)
                    ·
                      rfl

theorem cell23_2436520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_2436520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2436520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2436520 prefixEnd_2436520 := by exact prefixLift 2436520
  have htrace : WordTrace (prefixWord ++ tailWord_2436520) baseStart_2436520 baseEnd_2436520 := by
    simpa [prefixWord, tailWord_2436520, baseEnd_2436520] using wordTrace_append hprefix tailTrace_2436520
  have hstable : (prefixWord ++ tailWord_2436520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2436520).length < 2 ^ (prefixWord ++ tailWord_2436520).sum := by decide
  have hdescent : baseEnd_2436520 < baseStart_2436520 := by decide
  rcases family_descends (prefixWord ++ tailWord_2436520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2436583 : List Nat := [1, 1, 5, 2, 1, 2, 1, 3, 3, 2, 2]
def baseStart_2436583 : Nat := 118140960795 + 2436583 * 2 ^ 59
def prefixEnd_2436583 : Nat := 4983230072969 + 3 ^ 40 * 2436583 * 2
def baseEnd_2436583 : Nat := 1251138233574145591506865

theorem tailTrace_2436583 : CollatzResearch.WordTrace tailWord_2436583 prefixEnd_2436583 1251138233574145591506865 := by
  unfold tailWord_2436583
  simp only [CollatzResearch.WordTrace]
  refine ⟨88869482931683401091290403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59246321954455600727526935 88869482931683401091290403)
  ·
    refine ⟨133304224397525101636935605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88869482931683401091290403 133304224397525101636935605)
    ·
      refine ⟨12497271037267978278462713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 133304224397525101636935605 12497271037267978278462713)
      ·
        refine ⟨9372953277950983708847035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12497271037267978278462713 9372953277950983708847035)
        ·
          refine ⟨14059429916926475563270553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9372953277950983708847035 14059429916926475563270553)
          ·
            refine ⟨10544572437694856672452915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14059429916926475563270553 10544572437694856672452915)
            ·
              refine ⟨15816858656542285008679373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10544572437694856672452915 15816858656542285008679373)
              ·
                refine ⟨5931321996203356878254765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15816858656542285008679373 5931321996203356878254765)
                ·
                  refine ⟨2224245748576258829345537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5931321996203356878254765 2224245748576258829345537)
                  ·
                    refine ⟨1668184311432194122009153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2224245748576258829345537 1668184311432194122009153)
                    ·
                      refine ⟨1251138233574145591506865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1668184311432194122009153 1251138233574145591506865)
                      ·
                        rfl

theorem cell23_2436583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 3, 3, 2, 2].length) (baseStart_2436583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2436583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2436583 prefixEnd_2436583 := by exact prefixLift 2436583
  have htrace : WordTrace (prefixWord ++ tailWord_2436583) baseStart_2436583 baseEnd_2436583 := by
    simpa [prefixWord, tailWord_2436583, baseEnd_2436583] using wordTrace_append hprefix tailTrace_2436583
  have hstable : (prefixWord ++ tailWord_2436583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2436583).length < 2 ^ (prefixWord ++ tailWord_2436583).sum := by decide
  have hdescent : baseEnd_2436583 < baseStart_2436583 := by decide
  rcases family_descends (prefixWord ++ tailWord_2436583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2436586 : List Nat := [3, 1, 3, 1, 4, 1, 1, 2, 1, 1, 5]
def baseStart_2436586 : Nat := 118140960795 + 2436586 * 2 ^ 59
def prefixEnd_2436586 : Nat := 4983230072969 + 3 ^ 40 * 2436586 * 2
def baseEnd_2436586 : Nat := 1251139774016109079769351

theorem tailTrace_2436586 : CollatzResearch.WordTrace tailWord_2436586 prefixEnd_2436586 1251139774016109079769351 := by
  unfold tailWord_2436586
  simp only [CollatzResearch.WordTrace]
  refine ⟨22217398087668133150912403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59246394900448355069099741 22217398087668133150912403)
  ·
    refine ⟨33326097131502199726368605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22217398087668133150912403 33326097131502199726368605)
    ·
      refine ⟨12497286424313324897388227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33326097131502199726368605 12497286424313324897388227)
      ·
        refine ⟨18745929636469987346082341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12497286424313324897388227 18745929636469987346082341)
        ·
          refine ⟨3514861806838122627390439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18745929636469987346082341 3514861806838122627390439)
          ·
            refine ⟨5272292710257183941085659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3514861806838122627390439 5272292710257183941085659)
            ·
              refine ⟨7908439065385775911628489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5272292710257183941085659 7908439065385775911628489)
              ·
                refine ⟨5931329299039331933721367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7908439065385775911628489 5931329299039331933721367)
                ·
                  refine ⟨8896993948558997900582051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5931329299039331933721367 8896993948558997900582051)
                  ·
                    refine ⟨13345490922838496850873077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8896993948558997900582051 13345490922838496850873077)
                    ·
                      refine ⟨1251139774016109079769351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13345490922838496850873077 1251139774016109079769351)
                      ·
                        rfl

theorem cell23_2436586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 2, 1, 1, 5].length) (baseStart_2436586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2436586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2436586 prefixEnd_2436586 := by exact prefixLift 2436586
  have htrace : WordTrace (prefixWord ++ tailWord_2436586) baseStart_2436586 baseEnd_2436586 := by
    simpa [prefixWord, tailWord_2436586, baseEnd_2436586] using wordTrace_append hprefix tailTrace_2436586
  have hstable : (prefixWord ++ tailWord_2436586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2436586).length < 2 ^ (prefixWord ++ tailWord_2436586).sum := by decide
  have hdescent : baseEnd_2436586 < baseStart_2436586 := by decide
  rcases family_descends (prefixWord ++ tailWord_2436586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2436593 : List Nat := [1, 2, 2, 2, 3, 3, 3, 1, 2, 4]
def baseStart_2436593 : Nat := 118140960795 + 2436593 * 2 ^ 59
def prefixEnd_2436593 : Nat := 4983230072969 + 3 ^ 40 * 2436593 * 2
def baseEnd_2436593 : Nat := 417047789460230184127273

theorem tailTrace_2436593 : CollatzResearch.WordTrace tailWord_2436593 prefixEnd_2436593 417047789460230184127273 := by
  unfold tailWord_2436593
  simp only [CollatzResearch.WordTrace]
  refine ⟨88869847661647172799154433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59246565107764781866102955 88869847661647172799154433)
  ·
    refine ⟨66652385746235379599365825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88869847661647172799154433 66652385746235379599365825)
    ·
      refine ⟨49989289309676534699524369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66652385746235379599365825 49989289309676534699524369)
      ·
        refine ⟨37491966982257401024643277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49989289309676534699524369 37491966982257401024643277)
        ·
          refine ⟨14059487618346525384241229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37491966982257401024643277 14059487618346525384241229)
          ·
            refine ⟨5272307856879947019090461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14059487618346525384241229 5272307856879947019090461)
            ·
              refine ⟨1977115446329980132158923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5272307856879947019090461 1977115446329980132158923)
              ·
                refine ⟨2965673169494970198238385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1977115446329980132158923 2965673169494970198238385)
                ·
                  refine ⟨2224254877121227648678789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2965673169494970198238385 2224254877121227648678789)
                  ·
                    refine ⟨417047789460230184127273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2224254877121227648678789 417047789460230184127273)
                    ·
                      rfl

theorem cell23_2436593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 3, 1, 2, 4].length) (baseStart_2436593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2436593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2436593 prefixEnd_2436593 := by exact prefixLift 2436593
  have htrace : WordTrace (prefixWord ++ tailWord_2436593) baseStart_2436593 baseEnd_2436593 := by
    simpa [prefixWord, tailWord_2436593, baseEnd_2436593] using wordTrace_append hprefix tailTrace_2436593
  have hstable : (prefixWord ++ tailWord_2436593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2436593).length < 2 ^ (prefixWord ++ tailWord_2436593).sum := by decide
  have hdescent : baseEnd_2436593 < baseStart_2436593 := by decide
  rcases family_descends (prefixWord ++ tailWord_2436593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2436599 : List Nat := [1, 1, 3, 1, 1, 1, 1, 7, 1, 3, 3]
def baseStart_2436599 : Nat := 118140960795 + 2436599 * 2 ^ 59
def prefixEnd_2436599 : Nat := 4983230072969 + 3 ^ 40 * 2436599 * 2
def baseEnd_2436599 : Nat := 1251146449264617528906791

theorem tailTrace_2436599 : CollatzResearch.WordTrace tailWord_2436599 prefixEnd_2436599 1251146449264617528906791 := by
  unfold tailWord_2436599
  simp only [CollatzResearch.WordTrace]
  refine ⟨88870066499625435823872851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59246710999750290549248567 88870066499625435823872851)
  ·
    refine ⟨133305099749438153735809277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88870066499625435823872851 133305099749438153735809277)
    ·
      refine ⟨49989412406039307650928479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133305099749438153735809277 49989412406039307650928479)
      ·
        refine ⟨74984118609058961476392719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49989412406039307650928479 74984118609058961476392719)
        ·
          refine ⟨112476177913588442214589079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74984118609058961476392719 112476177913588442214589079)
          ·
            refine ⟨168714266870382663321883619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112476177913588442214589079 168714266870382663321883619)
            ·
              refine ⟨253071400305573994982825429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 168714266870382663321883619 253071400305573994982825429)
              ·
                refine ⟨5931360944661890507409971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 253071400305573994982825429 5931360944661890507409971)
                ·
                  refine ⟨8897041416992835761114957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5931360944661890507409971 8897041416992835761114957)
                  ·
                    refine ⟨3336390531372313410418109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8897041416992835761114957 3336390531372313410418109)
                    ·
                      refine ⟨1251146449264617528906791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3336390531372313410418109 1251146449264617528906791)
                      ·
                        rfl

theorem cell23_2436599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 7, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 7, 1, 3, 3].length) (baseStart_2436599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2436599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2436599 prefixEnd_2436599 := by exact prefixLift 2436599
  have htrace : WordTrace (prefixWord ++ tailWord_2436599) baseStart_2436599 baseEnd_2436599 := by
    simpa [prefixWord, tailWord_2436599, baseEnd_2436599] using wordTrace_append hprefix tailTrace_2436599
  have hstable : (prefixWord ++ tailWord_2436599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2436599).length < 2 ^ (prefixWord ++ tailWord_2436599).sum := by decide
  have hdescent : baseEnd_2436599 < baseStart_2436599 := by decide
  rcases family_descends (prefixWord ++ tailWord_2436599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2436616 : List Nat := [2, 1, 3, 2, 1, 1, 3, 2, 4, 1, 3]
def baseStart_2436616 : Nat := 118140960795 + 2436616 * 2 ^ 59
def prefixEnd_2436616 : Nat := 4983230072969 + 3 ^ 40 * 2436616 * 2
def baseEnd_2436616 : Nat := 1251155178435743962394213

theorem tailTrace_2436616 : CollatzResearch.WordTrace tailWord_2436616 prefixEnd_2436616 1251155178435743962394213 := by
  unfold tailWord_2436616
  simp only [CollatzResearch.WordTrace]
  refine ⟨44435343270281923863620851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59247124360375898484827801 44435343270281923863620851)
  ·
    refine ⟨66653014905422885795431277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44435343270281923863620851 66653014905422885795431277)
    ·
      refine ⟨24994880589533582173286729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66653014905422885795431277 24994880589533582173286729)
      ·
        refine ⟨18746160442150186629965047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24994880589533582173286729 18746160442150186629965047)
        ·
          refine ⟨28119240663225279944947571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18746160442150186629965047 28119240663225279944947571)
          ·
            refine ⟨42178860994837919917421357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28119240663225279944947571 42178860994837919917421357)
            ·
              refine ⟨15817072873064219969033009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42178860994837919917421357 15817072873064219969033009)
              ·
                refine ⟨11862804654798164976774757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15817072873064219969033009 11862804654798164976774757)
                ·
                  refine ⟨2224275872774655933145267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11862804654798164976774757 2224275872774655933145267)
                  ·
                    refine ⟨3336413809161983899717901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2224275872774655933145267 3336413809161983899717901)
                    ·
                      refine ⟨1251155178435743962394213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3336413809161983899717901 1251155178435743962394213)
                      ·
                        rfl

theorem cell23_2436616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 2, 4, 1, 3].length) (baseStart_2436616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2436616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2436616 prefixEnd_2436616 := by exact prefixLift 2436616
  have htrace : WordTrace (prefixWord ++ tailWord_2436616) baseStart_2436616 baseEnd_2436616 := by
    simpa [prefixWord, tailWord_2436616, baseEnd_2436616] using wordTrace_append hprefix tailTrace_2436616
  have hstable : (prefixWord ++ tailWord_2436616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2436616).length < 2 ^ (prefixWord ++ tailWord_2436616).sum := by decide
  have hdescent : baseEnd_2436616 < baseStart_2436616 := by decide
  rcases family_descends (prefixWord ++ tailWord_2436616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2436656 : List Nat := [2, 1, 1, 1, 2, 3, 1, 5, 1, 4, 2]
def baseStart_2436656 : Nat := 118140960795 + 2436656 * 2 ^ 59
def prefixEnd_2436656 : Nat := 4983230072969 + 3 ^ 40 * 2436656 * 2
def baseEnd_2436656 : Nat := 1251175717661923805894029

theorem tailTrace_2436656 : CollatzResearch.WordTrace tailWord_2436656 prefixEnd_2436656 1251175717661923805894029 := by
  unfold tailWord_2436656
  simp only [CollatzResearch.WordTrace]
  refine ⟨44436072730209467279348911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59248096973612623039131881 44436072730209467279348911)
  ·
    refine ⟨66654109095314200919023367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44436072730209467279348911 66654109095314200919023367)
    ·
      refine ⟨99981163642971301378535051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66654109095314200919023367 99981163642971301378535051)
      ·
        refine ⟨149971745464456952067802577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99981163642971301378535051 149971745464456952067802577)
        ·
          refine ⟨112478809098342714050851933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149971745464456952067802577 112478809098342714050851933)
          ·
            refine ⟨42179553411878517769069475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 112478809098342714050851933 42179553411878517769069475)
            ·
              refine ⟨63269330117817776653604213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42179553411878517769069475 63269330117817776653604213)
              ·
                refine ⟨5931499698545416561275395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 63269330117817776653604213 5931499698545416561275395)
                ·
                  refine ⟨8897249547818124841913093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5931499698545416561275395 8897249547818124841913093)
                  ·
                    refine ⟨1668234290215898407858705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8897249547818124841913093 1668234290215898407858705)
                    ·
                      refine ⟨1251175717661923805894029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1668234290215898407858705 1251175717661923805894029)
                      ·
                        rfl

theorem cell23_2436656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 5, 1, 4, 2].length) (baseStart_2436656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2436656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2436656 prefixEnd_2436656 := by exact prefixLift 2436656
  have htrace : WordTrace (prefixWord ++ tailWord_2436656) baseStart_2436656 baseEnd_2436656 := by
    simpa [prefixWord, tailWord_2436656, baseEnd_2436656] using wordTrace_append hprefix tailTrace_2436656
  have hstable : (prefixWord ++ tailWord_2436656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2436656).length < 2 ^ (prefixWord ++ tailWord_2436656).sum := by decide
  have hdescent : baseEnd_2436656 < baseStart_2436656 := by decide
  rcases family_descends (prefixWord ++ tailWord_2436656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2436659 : List Nat := [1, 1, 1, 2, 4, 3, 1, 2, 2, 1, 5]
def baseStart_2436659 : Nat := 118140960795 + 2436659 * 2 ^ 59
def prefixEnd_2436659 : Nat := 4983230072969 + 3 ^ 40 * 2436659 * 2
def baseEnd_2436659 : Nat := 1251177258103887294156515

theorem tailTrace_2436659 : CollatzResearch.WordTrace tailWord_2436659 prefixEnd_2436659 1251177258103887294156515 := by
  unfold tailWord_2436659
  simp only [CollatzResearch.WordTrace]
  refine ⟨88872254879408066071057031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59248169919605377380704687 88872254879408066071057031)
  ·
    refine ⟨133308382319112099106585547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88872254879408066071057031 133308382319112099106585547)
    ·
      refine ⟨199962573478668148659878321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133308382319112099106585547 199962573478668148659878321)
      ·
        refine ⟨149971930109001111494908741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199962573478668148659878321 149971930109001111494908741)
        ·
          refine ⟨28119736895437708405295389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 149971930109001111494908741 28119736895437708405295389)
          ·
            refine ⟨10544901335789140651985771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28119736895437708405295389 10544901335789140651985771)
            ·
              refine ⟨15817352003683710977978657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10544901335789140651985771 15817352003683710977978657)
              ·
                refine ⟨11863014002762783233483993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15817352003683710977978657 11863014002762783233483993)
                ·
                  refine ⟨8897260502072087425112995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11863014002762783233483993 8897260502072087425112995)
                  ·
                    refine ⟨13345890753108131137669493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8897260502072087425112995 13345890753108131137669493)
                    ·
                      refine ⟨1251177258103887294156515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13345890753108131137669493 1251177258103887294156515)
                      ·
                        rfl

theorem cell23_2436659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 2, 2, 1, 5].length) (baseStart_2436659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2436659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2436659 prefixEnd_2436659 := by exact prefixLift 2436659
  have htrace : WordTrace (prefixWord ++ tailWord_2436659) baseStart_2436659 baseEnd_2436659 := by
    simpa [prefixWord, tailWord_2436659, baseEnd_2436659] using wordTrace_append hprefix tailTrace_2436659
  have hstable : (prefixWord ++ tailWord_2436659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2436659).length < 2 ^ (prefixWord ++ tailWord_2436659).sum := by decide
  have hdescent : baseEnd_2436659 < baseStart_2436659 := by decide
  rcases family_descends (prefixWord ++ tailWord_2436659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2436673 : List Nat := [1, 2, 5, 1, 1, 1, 3, 2, 1, 4, 2]
def baseStart_2436673 : Nat := 118140960795 + 2436673 * 2 ^ 59
def prefixEnd_2436673 : Nat := 4983230072969 + 3 ^ 40 * 2436673 * 2
def baseEnd_2436673 : Nat := 1251184446833050239381451

theorem tailTrace_2436673 : CollatzResearch.WordTrace tailWord_2436673 prefixEnd_2436673 1251184446833050239381451 := by
  unfold tailWord_2436673
  simp only [CollatzResearch.WordTrace]
  refine ⟨88872765501357346462066673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59248510334238230974711115 88872765501357346462066673)
  ·
    refine ⟨66654574126018009846550005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88872765501357346462066673 66654574126018009846550005)
    ·
      refine ⟨6248866324314188423114063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 66654574126018009846550005 6248866324314188423114063)
      ·
        refine ⟨9373299486471282634671095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6248866324314188423114063 9373299486471282634671095)
        ·
          refine ⟨14059949229706923952006643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9373299486471282634671095 14059949229706923952006643)
          ·
            refine ⟨21089923844560385928009965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14059949229706923952006643 21089923844560385928009965)
            ·
              refine ⟨7908721441710144723003737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21089923844560385928009965 7908721441710144723003737)
              ·
                refine ⟨5931541081282608542252803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7908721441710144723003737 5931541081282608542252803)
                ·
                  refine ⟨8897311621923912813379205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5931541081282608542252803 8897311621923912813379205)
                  ·
                    refine ⟨1668245929110733652508601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8897311621923912813379205 1668245929110733652508601)
                    ·
                      refine ⟨1251184446833050239381451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1668245929110733652508601 1251184446833050239381451)
                      ·
                        rfl

theorem cell23_2436673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 2, 1, 4, 2].length) (baseStart_2436673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2436673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2436673 prefixEnd_2436673 := by exact prefixLift 2436673
  have htrace : WordTrace (prefixWord ++ tailWord_2436673) baseStart_2436673 baseEnd_2436673 := by
    simpa [prefixWord, tailWord_2436673, baseEnd_2436673] using wordTrace_append hprefix tailTrace_2436673
  have hstable : (prefixWord ++ tailWord_2436673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2436673).length < 2 ^ (prefixWord ++ tailWord_2436673).sum := by decide
  have hdescent : baseEnd_2436673 < baseStart_2436673 := by decide
  rcases family_descends (prefixWord ++ tailWord_2436673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2436690 : List Nat := [3, 2, 2, 1, 2, 2, 1, 4, 2, 2, 2]
def baseStart_2436690 : Nat := 118140960795 + 2436690 * 2 ^ 59
def prefixEnd_2436690 : Nat := 4983230072969 + 3 ^ 40 * 2436690 * 2
def baseEnd_2436690 : Nat := 1251193176004176672868873

theorem tailTrace_2436690 : CollatzResearch.WordTrace tailWord_2436690 prefixEnd_2436690 1251193176004176672868873 := by
  unfold tailWord_2436690
  simp only [CollatzResearch.WordTrace]
  refine ⟨22218346385573939591358881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59248923694863838910290349 22218346385573939591358881)
  ·
    refine ⟨16663759789180454693519161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22218346385573939591358881 16663759789180454693519161)
    ·
      refine ⟨12497819841885341020139371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16663759789180454693519161 12497819841885341020139371)
      ·
        refine ⟨18746729762828011530209057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12497819841885341020139371 18746729762828011530209057)
        ·
          refine ⟨14060047322121008647656793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18746729762828011530209057 14060047322121008647656793)
          ·
            refine ⟨10545035491590756485742595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14060047322121008647656793 10545035491590756485742595)
            ·
              refine ⟨15817553237386134728613893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10545035491590756485742595 15817553237386134728613893)
              ·
                refine ⟨2965791232009900261615105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15817553237386134728613893 2965791232009900261615105)
                ·
                  refine ⟨2224343424007425196211329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2965791232009900261615105 2224343424007425196211329)
                  ·
                    refine ⟨1668257568005568897158497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2224343424007425196211329 1668257568005568897158497)
                    ·
                      refine ⟨1251193176004176672868873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1668257568005568897158497 1251193176004176672868873)
                      ·
                        rfl

theorem cell23_2436690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 4, 2, 2, 2].length) (baseStart_2436690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2436690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2436690 prefixEnd_2436690 := by exact prefixLift 2436690
  have htrace : WordTrace (prefixWord ++ tailWord_2436690) baseStart_2436690 baseEnd_2436690 := by
    simpa [prefixWord, tailWord_2436690, baseEnd_2436690] using wordTrace_append hprefix tailTrace_2436690
  have hstable : (prefixWord ++ tailWord_2436690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2436690).length < 2 ^ (prefixWord ++ tailWord_2436690).sum := by decide
  have hdescent : baseEnd_2436690 < baseStart_2436690 := by decide
  rcases family_descends (prefixWord ++ tailWord_2436690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2436716 : List Nat := [2, 2, 1, 1, 3, 1, 1, 1, 4, 5, 2]
def baseStart_2436716 : Nat := 118140960795 + 2436716 * 2 ^ 59
def prefixEnd_2436716 : Nat := 4983230072969 + 3 ^ 40 * 2436716 * 2
def baseEnd_2436716 : Nat := 1251206526501193571143753

theorem tailTrace_2436716 : CollatzResearch.WordTrace tailWord_2436716 prefixEnd_2436716 1251206526501193571143753 := by
  unfold tailWord_2436716
  simp only [CollatzResearch.WordTrace]
  refine ⟨44437166920100782402941001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59249555893467709870588001 44437166920100782402941001)
  ·
    refine ⟨33327875190075586802205751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44437166920100782402941001 33327875190075586802205751)
    ·
      refine ⟨49991812785113380203308627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33327875190075586802205751 49991812785113380203308627)
      ·
        refine ⟨74987719177670070304962941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49991812785113380203308627 74987719177670070304962941)
        ·
          refine ⟨28120394691626276364361103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74987719177670070304962941 28120394691626276364361103)
          ·
            refine ⟨42180592037439414546541655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28120394691626276364361103 42180592037439414546541655)
            ·
              refine ⟨63270888056159121819812483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42180592037439414546541655 63270888056159121819812483)
              ·
                refine ⟨94906332084238682729718725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63270888056159121819812483 94906332084238682729718725)
                ·
                  refine ⟨17794937265794753011822261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 94906332084238682729718725 17794937265794753011822261)
                  ·
                    refine ⟨1668275368668258094858337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17794937265794753011822261 1668275368668258094858337)
                    ·
                      refine ⟨1251206526501193571143753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1668275368668258094858337 1251206526501193571143753)
                      ·
                        rfl

theorem cell23_2436716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 5, 2].length) (baseStart_2436716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2436716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2436716 prefixEnd_2436716 := by exact prefixLift 2436716
  have htrace : WordTrace (prefixWord ++ tailWord_2436716) baseStart_2436716 baseEnd_2436716 := by
    simpa [prefixWord, tailWord_2436716, baseEnd_2436716] using wordTrace_append hprefix tailTrace_2436716
  have hstable : (prefixWord ++ tailWord_2436716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2436716).length < 2 ^ (prefixWord ++ tailWord_2436716).sum := by decide
  have hdescent : baseEnd_2436716 < baseStart_2436716 := by decide
  rcases family_descends (prefixWord ++ tailWord_2436716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2436820 : List Nat := [2, 4, 1, 3, 1, 1, 4, 1, 6]
def baseStart_2436820 : Nat := 118140960795 + 2436820 * 2 ^ 59
def prefixEnd_2436820 : Nat := 4983230072969 + 3 ^ 40 * 2436820 * 2
def baseEnd_2436820 : Nat := 139028880943251240471475

theorem tailTrace_2436820 : CollatzResearch.WordTrace tailWord_2436820 prefixEnd_2436820 139028880943251240471475 := by
  unfold tailWord_2436820
  simp only [CollatzResearch.WordTrace]
  refine ⟨44439063515912395283833957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59252084687883193711778609 44439063515912395283833957)
  ·
    refine ⟨8332324409233574115718867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44439063515912395283833957 8332324409233574115718867)
    ·
      refine ⟨12498486613850361173578301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8332324409233574115718867 12498486613850361173578301)
      ·
        refine ⟨4686932480193885440091863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12498486613850361173578301 4686932480193885440091863)
        ·
          refine ⟨7030398720290828160137795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4686932480193885440091863 7030398720290828160137795)
          ·
            refine ⟨10545598080436242240206693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7030398720290828160137795 10545598080436242240206693)
            ·
              refine ⟨1977299640081795420038755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10545598080436242240206693 1977299640081795420038755)
              ·
                refine ⟨2965949460122693130058133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1977299640081795420038755 2965949460122693130058133)
                ·
                  refine ⟨139028880943251240471475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2965949460122693130058133 139028880943251240471475)
                  ·
                    rfl

theorem cell23_2436820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 4, 1, 6].length) (baseStart_2436820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2436820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2436820 prefixEnd_2436820 := by exact prefixLift 2436820
  have htrace : WordTrace (prefixWord ++ tailWord_2436820) baseStart_2436820 baseEnd_2436820 := by
    simpa [prefixWord, tailWord_2436820, baseEnd_2436820] using wordTrace_append hprefix tailTrace_2436820
  have hstable : (prefixWord ++ tailWord_2436820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2436820).length < 2 ^ (prefixWord ++ tailWord_2436820).sum := by decide
  have hdescent : baseEnd_2436820 < baseStart_2436820 := by decide
  rcases family_descends (prefixWord ++ tailWord_2436820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2436823 : List Nat := [1, 1, 3, 2, 1, 3, 1, 2, 4, 3, 2]
def baseStart_2436823 : Nat := 118140960795 + 2436823 * 2 ^ 59
def prefixEnd_2436823 : Nat := 4983230072969 + 3 ^ 40 * 2436823 * 2
def baseEnd_2436823 : Nat := 1251261468931224652505761

theorem tailTrace_2436823 : CollatzResearch.WordTrace tailWord_2436823 prefixEnd_2436823 1251261468931224652505761 := by
  unfold tailWord_2436823
  simp only [CollatzResearch.WordTrace]
  refine ⟨88878236450813922080027123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59252157633875948053351415 88878236450813922080027123)
  ·
    refine ⟨133317354676220883120040685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88878236450813922080027123 133317354676220883120040685)
    ·
      refine ⟨49994008003582831170015257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133317354676220883120040685 49994008003582831170015257)
      ·
        refine ⟨37495506002687123377511443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49994008003582831170015257 37495506002687123377511443)
        ·
          refine ⟨56243259004030685066267165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37495506002687123377511443 56243259004030685066267165)
          ·
            refine ⟨21091222126511506899850187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56243259004030685066267165 21091222126511506899850187)
            ·
              refine ⟨31636833189767260349775281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21091222126511506899850187 31636833189767260349775281)
              ·
                refine ⟨23727624892325445262331461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31636833189767260349775281 23727624892325445262331461)
                ·
                  refine ⟨4448929667311020986687149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23727624892325445262331461 4448929667311020986687149)
                  ·
                    refine ⟨1668348625241632870007681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4448929667311020986687149 1668348625241632870007681)
                    ·
                      refine ⟨1251261468931224652505761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1668348625241632870007681 1251261468931224652505761)
                      ·
                        rfl

theorem cell23_2436823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 2, 4, 3, 2].length) (baseStart_2436823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2436823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2436823 prefixEnd_2436823 := by exact prefixLift 2436823
  have htrace : WordTrace (prefixWord ++ tailWord_2436823) baseStart_2436823 baseEnd_2436823 := by
    simpa [prefixWord, tailWord_2436823, baseEnd_2436823] using wordTrace_append hprefix tailTrace_2436823
  have hstable : (prefixWord ++ tailWord_2436823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2436823).length < 2 ^ (prefixWord ++ tailWord_2436823).sum := by decide
  have hdescent : baseEnd_2436823 < baseStart_2436823 := by decide
  rcases family_descends (prefixWord ++ tailWord_2436823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2436833 : List Nat := [1, 2, 3, 1, 5, 1, 1, 1, 3, 5]
def baseStart_2436833 : Nat := 118140960795 + 2436833 * 2 ^ 59
def prefixEnd_2436833 : Nat := 4983230072969 + 3 ^ 40 * 2436833 * 2
def baseEnd_2436833 : Nat := 417088867912589871126905

theorem tailTrace_2436833 : CollatzResearch.WordTrace tailWord_2436833 prefixEnd_2436833 417088867912589871126905 := by
  unfold tailWord_2436833
  simp only [CollatzResearch.WordTrace]
  refine ⟨88878601180777693787891153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59252400787185129191927435 88878601180777693787891153)
  ·
    refine ⟨66658950885583270340918365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88878601180777693787891153 66658950885583270340918365)
    ·
      refine ⟨24997106582093726377844387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66658950885583270340918365 24997106582093726377844387)
      ·
        refine ⟨37495659873140589566766581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24997106582093726377844387 37495659873140589566766581)
        ·
          refine ⟨3515218113106930271884367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 37495659873140589566766581 3515218113106930271884367)
          ·
            refine ⟨5272827169660395407826551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3515218113106930271884367 5272827169660395407826551)
            ·
              refine ⟨7909240754490593111739827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5272827169660395407826551 7909240754490593111739827)
              ·
                refine ⟨11863861131735889667609741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7909240754490593111739827 11863861131735889667609741)
                ·
                  refine ⟨4448947924400958625353653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11863861131735889667609741 4448947924400958625353653)
                  ·
                    refine ⟨417088867912589871126905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4448947924400958625353653 417088867912589871126905)
                    ·
                      rfl

theorem cell23_2436833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 1, 3, 5].length) (baseStart_2436833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2436833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2436833 prefixEnd_2436833 := by exact prefixLift 2436833
  have htrace : WordTrace (prefixWord ++ tailWord_2436833) baseStart_2436833 baseEnd_2436833 := by
    simpa [prefixWord, tailWord_2436833, baseEnd_2436833] using wordTrace_append hprefix tailTrace_2436833
  have hstable : (prefixWord ++ tailWord_2436833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2436833).length < 2 ^ (prefixWord ++ tailWord_2436833).sum := by decide
  have hdescent : baseEnd_2436833 < baseStart_2436833 := by decide
  rcases family_descends (prefixWord ++ tailWord_2436833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2436840 : List Nat := [2, 1, 4, 1, 3, 1, 1, 3, 2, 3, 2]
def baseStart_2436840 : Nat := 118140960795 + 2436840 * 2 ^ 59
def prefixEnd_2436840 : Nat := 4983230072969 + 3 ^ 40 * 2436840 * 2
def baseEnd_2436840 : Nat := 1251270198102351085993183

theorem tailTrace_2436840 : CollatzResearch.WordTrace tailWord_2436840 prefixEnd_2436840 1251270198102351085993183 := by
  unfold tailWord_2436840
  simp only [CollatzResearch.WordTrace]
  refine ⟨44439428245876166991697987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59252570994501555988930649 44439428245876166991697987)
  ·
    refine ⟨66659142368814250487546981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44439428245876166991697987 66659142368814250487546981)
    ·
      refine ⟨12498589194152671966415059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66659142368814250487546981 12498589194152671966415059)
      ·
        refine ⟨18747883791229007949622589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12498589194152671966415059 18747883791229007949622589)
        ·
          refine ⟨7030456421710877981108471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18747883791229007949622589 7030456421710877981108471)
          ·
            refine ⟨10545684632566316971662707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7030456421710877981108471 10545684632566316971662707)
            ·
              refine ⟨15818526948849475457494061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10545684632566316971662707 15818526948849475457494061)
              ·
                refine ⟨5931947605818553296560273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15818526948849475457494061 5931947605818553296560273)
                ·
                  refine ⟨4448960704363914972420205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5931947605818553296560273 4448960704363914972420205)
                  ·
                    refine ⟨1668360264136468114657577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4448960704363914972420205 1668360264136468114657577)
                    ·
                      refine ⟨1251270198102351085993183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1668360264136468114657577 1251270198102351085993183)
                      ·
                        rfl

theorem cell23_2436840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 3, 2, 3, 2].length) (baseStart_2436840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2436840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2436840 prefixEnd_2436840 := by exact prefixLift 2436840
  have htrace : WordTrace (prefixWord ++ tailWord_2436840) baseStart_2436840 baseEnd_2436840 := by
    simpa [prefixWord, tailWord_2436840, baseEnd_2436840] using wordTrace_append hprefix tailTrace_2436840
  have hstable : (prefixWord ++ tailWord_2436840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2436840).length < 2 ^ (prefixWord ++ tailWord_2436840).sum := by decide
  have hdescent : baseEnd_2436840 < baseStart_2436840 := by decide
  rcases family_descends (prefixWord ++ tailWord_2436840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2436850 : List Nat := [3, 2, 1, 3, 1, 1, 5, 1, 1, 5]
def baseStart_2436850 : Nat := 118140960795 + 2436850 * 2 ^ 59
def prefixEnd_2436850 : Nat := 4983230072969 + 3 ^ 40 * 2436850 * 2
def baseEnd_2436850 : Nat := 417091777636298682289379

theorem tailTrace_2436850 : CollatzResearch.WordTrace tailWord_2436850 prefixEnd_2436850 417091777636298682289379 := by
  unfold tailWord_2436850
  simp only [CollatzResearch.WordTrace]
  refine ⟨22219805305429026422815001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59252814147810737127506669 22219805305429026422815001)
  ·
    refine ⟨16664853979071769817111251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22219805305429026422815001 16664853979071769817111251)
    ·
      refine ⟨24997280968607654725666877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16664853979071769817111251 24997280968607654725666877)
      ·
        refine ⟨9373980363227870522125079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24997280968607654725666877 9373980363227870522125079)
        ·
          refine ⟨14060970544841805783187619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9373980363227870522125079 14060970544841805783187619)
          ·
            refine ⟨21091455817262708674781429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14060970544841805783187619 21091455817262708674781429)
            ·
              refine ⟨1977323982868378938260759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21091455817262708674781429 1977323982868378938260759)
              ·
                refine ⟨2965985974302568407391139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1977323982868378938260759 2965985974302568407391139)
                ·
                  refine ⟨4448978961453852611086709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2965985974302568407391139 4448978961453852611086709)
                  ·
                    refine ⟨417091777636298682289379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4448978961453852611086709 417091777636298682289379)
                    ·
                      rfl

theorem cell23_2436850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 5, 1, 1, 5].length) (baseStart_2436850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2436850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2436850 prefixEnd_2436850 := by exact prefixLift 2436850
  have htrace : WordTrace (prefixWord ++ tailWord_2436850) baseStart_2436850 baseEnd_2436850 := by
    simpa [prefixWord, tailWord_2436850, baseEnd_2436850] using wordTrace_append hprefix tailTrace_2436850
  have hstable : (prefixWord ++ tailWord_2436850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2436850).length < 2 ^ (prefixWord ++ tailWord_2436850).sum := by decide
  have hdescent : baseEnd_2436850 < baseStart_2436850 := by decide
  rcases family_descends (prefixWord ++ tailWord_2436850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2436856 : List Nat := [2, 1, 2, 1, 1, 2, 2, 5, 1, 1, 5]
def baseStart_2436856 : Nat := 118140960795 + 2436856 * 2 ^ 59
def prefixEnd_2436856 : Nat := 4983230072969 + 3 ^ 40 * 2436856 * 2
def baseEnd_2436856 : Nat := 1251278413792823023393109

theorem tailTrace_2436856 : CollatzResearch.WordTrace tailWord_2436856 prefixEnd_2436856 1251278413792823023393109 := by
  unfold tailWord_2436856
  simp only [CollatzResearch.WordTrace]
  refine ⟨44439720029847184357989211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59252960039796245810652281 44439720029847184357989211)
  ·
    refine ⟨66659580044770776536983817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44439720029847184357989211 66659580044770776536983817)
    ·
      refine ⟨49994685033578082402737863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66659580044770776536983817 49994685033578082402737863)
      ·
        refine ⟨74992027550367123604106795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49994685033578082402737863 74992027550367123604106795)
        ·
          refine ⟨112488041325550685406160193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74992027550367123604106795 112488041325550685406160193)
          ·
            refine ⟨84366030994163014054620145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112488041325550685406160193 84366030994163014054620145)
            ·
              refine ⟨63274523245622260540965109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84366030994163014054620145 63274523245622260540965109)
              ·
                refine ⟨5931986554277086925715479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 63274523245622260540965109 5931986554277086925715479)
                ·
                  refine ⟨8897979831415630388573219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5931986554277086925715479 8897979831415630388573219)
                  ·
                    refine ⟨13346969747123445582859829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8897979831415630388573219 13346969747123445582859829)
                    ·
                      refine ⟨1251278413792823023393109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13346969747123445582859829 1251278413792823023393109)
                      ·
                        rfl

theorem cell23_2436856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 5, 1, 1, 5].length) (baseStart_2436856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2436856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2436856 prefixEnd_2436856 := by exact prefixLift 2436856
  have htrace : WordTrace (prefixWord ++ tailWord_2436856) baseStart_2436856 baseEnd_2436856 := by
    simpa [prefixWord, tailWord_2436856, baseEnd_2436856] using wordTrace_append hprefix tailTrace_2436856
  have hstable : (prefixWord ++ tailWord_2436856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2436856).length < 2 ^ (prefixWord ++ tailWord_2436856).sum := by decide
  have hdescent : baseEnd_2436856 < baseStart_2436856 := by decide
  rcases family_descends (prefixWord ++ tailWord_2436856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2436863 : List Nat := [1, 1, 2, 2, 1, 3, 3, 4, 2, 4]
def baseStart_2436863 : Nat := 118140960795 + 2436863 * 2 ^ 59
def prefixEnd_2436863 : Nat := 4983230072969 + 3 ^ 40 * 2436863 * 2
def baseEnd_2436863 : Nat := 417094002719134832001859

theorem tailTrace_2436863 : CollatzResearch.WordTrace tailWord_2436863 prefixEnd_2436863 417094002719134832001859 := by
  unfold tailWord_2436863
  simp only [CollatzResearch.WordTrace]
  refine ⟨88879695370669008911483243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59253130247112672607655495 88879695370669008911483243)
  ·
    refine ⟨133319543056003513367224865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88879695370669008911483243 133319543056003513367224865)
    ·
      refine ⟨99989657292002635025418649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133319543056003513367224865 99989657292002635025418649)
      ·
        refine ⟨74992242969001976269063987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99989657292002635025418649 74992242969001976269063987)
        ·
          refine ⟨112488364453502964403595981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74992242969001976269063987 112488364453502964403595981)
          ·
            refine ⟨42183136670063611651348493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 112488364453502964403595981 42183136670063611651348493)
            ·
              refine ⟨15818676251273854369255685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42183136670063611651348493 15818676251273854369255685)
              ·
                refine ⟨2966001797113847694235441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15818676251273854369255685 2966001797113847694235441)
                ·
                  refine ⟨2224501347835385770676581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2966001797113847694235441 2224501347835385770676581)
                  ·
                    refine ⟨417094002719134832001859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2224501347835385770676581 417094002719134832001859)
                    ·
                      rfl

theorem cell23_2436863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 4, 2, 4].length) (baseStart_2436863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2436863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2436863 prefixEnd_2436863 := by exact prefixLift 2436863
  have htrace : WordTrace (prefixWord ++ tailWord_2436863) baseStart_2436863 baseEnd_2436863 := by
    simpa [prefixWord, tailWord_2436863, baseEnd_2436863] using wordTrace_append hprefix tailTrace_2436863
  have hstable : (prefixWord ++ tailWord_2436863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2436863).length < 2 ^ (prefixWord ++ tailWord_2436863).sum := by decide
  have hdescent : baseEnd_2436863 < baseStart_2436863 := by decide
  rcases family_descends (prefixWord ++ tailWord_2436863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2436876 : List Nat := [2, 2, 1, 2, 2, 1, 5, 8]
def baseStart_2436876 : Nat := 118140960795 + 2436876 * 2 ^ 59
def prefixEnd_2436876 : Nat := 4983230072969 + 3 ^ 40 * 2436876 * 2
def baseEnd_2436876 : Nat := 46344025311330109079371

theorem tailTrace_2436876 : CollatzResearch.WordTrace tailWord_2436876 prefixEnd_2436876 46344025311330109079371 := by
  unfold tailWord_2436876
  simp only [CollatzResearch.WordTrace]
  refine ⟨44440084759810956065853241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59253446346414608087804321 44440084759810956065853241)
  ·
    refine ⟨33330063569858217049389931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44440084759810956065853241 33330063569858217049389931)
    ·
      refine ⟨49995095354787325574084897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33330063569858217049389931 49995095354787325574084897)
      ·
        refine ⟨37496321516090494180563673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49995095354787325574084897 37496321516090494180563673)
        ·
          refine ⟨28122241137067870635422755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37496321516090494180563673 28122241137067870635422755)
          ·
            refine ⟨42183361705601805953134133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28122241137067870635422755 42183361705601805953134133)
            ·
              refine ⟨3954690159900169308106325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42183361705601805953134133 3954690159900169308106325)
              ·
                refine ⟨46344025311330109079371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3954690159900169308106325 46344025311330109079371)
                ·
                  rfl

theorem cell23_2436876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 8].length) (baseStart_2436876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2436876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2436876 prefixEnd_2436876 := by exact prefixLift 2436876
  have htrace : WordTrace (prefixWord ++ tailWord_2436876) baseStart_2436876 baseEnd_2436876 := by
    simpa [prefixWord, tailWord_2436876, baseEnd_2436876] using wordTrace_append hprefix tailTrace_2436876
  have hstable : (prefixWord ++ tailWord_2436876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2436876).length < 2 ^ (prefixWord ++ tailWord_2436876).sum := by decide
  have hdescent : baseEnd_2436876 < baseStart_2436876 := by decide
  rcases family_descends (prefixWord ++ tailWord_2436876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2436887 : List Nat := [1, 1, 3, 4, 2, 2, 1, 2, 3, 2, 2]
def baseStart_2436887 : Nat := 118140960795 + 2436887 * 2 ^ 59
def prefixEnd_2436887 : Nat := 4983230072969 + 3 ^ 40 * 2436887 * 2
def baseEnd_2436887 : Nat := 1251294331693112402105467

theorem tailTrace_2436887 : CollatzResearch.WordTrace tailWord_2436887 prefixEnd_2436887 1251294331693112402105467 := by
  unfold tailWord_2436887
  simp only [CollatzResearch.WordTrace]
  refine ⟨88880570722582061010356915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59253713815054707340237943 88880570722582061010356915)
  ·
    refine ⟨133320856083873091515535373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88880570722582061010356915 133320856083873091515535373)
    ·
      refine ⟨49995321031452409318325765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133320856083873091515535373 49995321031452409318325765)
      ·
        refine ⟨9374122693397326747186081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49995321031452409318325765 9374122693397326747186081)
        ·
          refine ⟨7030592020047995060389561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9374122693397326747186081 7030592020047995060389561)
          ·
            refine ⟨5272944015035996295292171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7030592020047995060389561 5272944015035996295292171)
            ·
              refine ⟨7909416022553994442938257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5272944015035996295292171 7909416022553994442938257)
              ·
                refine ⟨5932062016915495832203693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7909416022553994442938257 5932062016915495832203693)
                ·
                  refine ⟨2224523256343310937076385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5932062016915495832203693 2224523256343310937076385)
                  ·
                    refine ⟨1668392442257483202807289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2224523256343310937076385 1668392442257483202807289)
                    ·
                      refine ⟨1251294331693112402105467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1668392442257483202807289 1251294331693112402105467)
                      ·
                        rfl

theorem cell23_2436887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 2, 3, 2, 2].length) (baseStart_2436887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2436887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2436887 prefixEnd_2436887 := by exact prefixLift 2436887
  have htrace : WordTrace (prefixWord ++ tailWord_2436887) baseStart_2436887 baseEnd_2436887 := by
    simpa [prefixWord, tailWord_2436887, baseEnd_2436887] using wordTrace_append hprefix tailTrace_2436887
  have hstable : (prefixWord ++ tailWord_2436887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2436887).length < 2 ^ (prefixWord ++ tailWord_2436887).sum := by decide
  have hdescent : baseEnd_2436887 < baseStart_2436887 := by decide
  rcases family_descends (prefixWord ++ tailWord_2436887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2436904 : List Nat := [2, 1, 5, 1, 1, 2, 1, 5, 1, 2, 2]
def baseStart_2436904 : Nat := 118140960795 + 2436904 * 2 ^ 59
def prefixEnd_2436904 : Nat := 4983230072969 + 3 ^ 40 * 2436904 * 2
def baseEnd_2436904 : Nat := 1251303060864238835592889

theorem tailTrace_2436904 : CollatzResearch.WordTrace tailWord_2436904 prefixEnd_2436904 1251303060864238835592889 := by
  unfold tailWord_2436904
  simp only [CollatzResearch.WordTrace]
  refine ⟨44440595381760236456862883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59254127175680315275817177 44440595381760236456862883)
  ·
    refine ⟨66660893072640354685294325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44440595381760236456862883 66660893072640354685294325)
    ·
      refine ⟨6249458725560033251746343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 66660893072640354685294325 6249458725560033251746343)
      ·
        refine ⟨9374188088340049877619515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6249458725560033251746343 9374188088340049877619515)
        ·
          refine ⟨14061282132510074816429273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9374188088340049877619515 14061282132510074816429273)
          ·
            refine ⟨10545961599382556112321955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14061282132510074816429273 10545961599382556112321955)
            ·
              refine ⟨15818942399073834168482933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10545961599382556112321955 15818942399073834168482933)
              ·
                refine ⟨1483025849913171953295275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15818942399073834168482933 1483025849913171953295275)
                ·
                  refine ⟨2224538774869757929942913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1483025849913171953295275 2224538774869757929942913)
                  ·
                    refine ⟨1668404081152318447457185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2224538774869757929942913 1668404081152318447457185)
                    ·
                      refine ⟨1251303060864238835592889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1668404081152318447457185 1251303060864238835592889)
                      ·
                        rfl

theorem cell23_2436904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 5, 1, 2, 2].length) (baseStart_2436904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2436904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2436904 prefixEnd_2436904 := by exact prefixLift 2436904
  have htrace : WordTrace (prefixWord ++ tailWord_2436904) baseStart_2436904 baseEnd_2436904 := by
    simpa [prefixWord, tailWord_2436904, baseEnd_2436904] using wordTrace_append hprefix tailTrace_2436904
  have hstable : (prefixWord ++ tailWord_2436904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2436904).length < 2 ^ (prefixWord ++ tailWord_2436904).sum := by decide
  have hdescent : baseEnd_2436904 < baseStart_2436904 := by decide
  rcases family_descends (prefixWord ++ tailWord_2436904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2436920 : List Nat := [2, 1, 2, 1, 3, 4, 1, 1, 4, 1, 3]
def baseStart_2436920 : Nat := 118140960795 + 2436920 * 2 ^ 59
def prefixEnd_2436920 : Nat := 4983230072969 + 3 ^ 40 * 2436920 * 2
def baseEnd_2436920 : Nat := 1251311276554710772992815

theorem tailTrace_2436920 : CollatzResearch.WordTrace tailWord_2436920 prefixEnd_2436920 1251311276554710772992815 := by
  unfold tailWord_2436920
  simp only [CollatzResearch.WordTrace]
  refine ⟨44440887165731253823154107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59254516220975005097538809 44440887165731253823154107)
  ·
    refine ⟨66661330748596880734731161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44440887165731253823154107 66661330748596880734731161)
    ·
      refine ⟨49995998061447660551048371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66661330748596880734731161 49995998061447660551048371)
      ·
        refine ⟨74993997092171490826572557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49995998061447660551048371 74993997092171490826572557)
        ·
          refine ⟨28122748909564309059964709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74993997092171490826572557 28122748909564309059964709)
          ·
            refine ⟨5273015420543307948743383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28122748909564309059964709 5273015420543307948743383)
            ·
              refine ⟨7909523130814961923115075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5273015420543307948743383 7909523130814961923115075)
              ·
                refine ⟨11864284696222442884672613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7909523130814961923115075 11864284696222442884672613)
                ·
                  refine ⟨2224553380541708040876115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11864284696222442884672613 2224553380541708040876115)
                  ·
                    refine ⟨3336830070812562061314173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2224553380541708040876115 3336830070812562061314173)
                    ·
                      refine ⟨1251311276554710772992815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3336830070812562061314173 1251311276554710772992815)
                      ·
                        rfl

theorem cell23_2436920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 1, 4, 1, 3].length) (baseStart_2436920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2436920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2436920 prefixEnd_2436920 := by exact prefixLift 2436920
  have htrace : WordTrace (prefixWord ++ tailWord_2436920) baseStart_2436920 baseEnd_2436920 := by
    simpa [prefixWord, tailWord_2436920, baseEnd_2436920] using wordTrace_append hprefix tailTrace_2436920
  have hstable : (prefixWord ++ tailWord_2436920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2436920).length < 2 ^ (prefixWord ++ tailWord_2436920).sum := by decide
  have hdescent : baseEnd_2436920 < baseStart_2436920 := by decide
  rcases family_descends (prefixWord ++ tailWord_2436920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2436934 : List Nat := [6, 1, 1, 2, 1, 3, 1, 1, 1, 2, 4]
def baseStart_2436934 : Nat := 118140960795 + 2436934 * 2 ^ 59
def prefixEnd_2436934 : Nat := 4983230072969 + 3 ^ 40 * 2436934 * 2
def baseEnd_2436934 : Nat := 1251318465283873718217751

theorem tailTrace_2436934 : CollatzResearch.WordTrace tailWord_2436934 prefixEnd_2436934 1251318465283873718217751 := by
  unfold tailWord_2436934
  simp only [CollatzResearch.WordTrace]
  refine ⟨2777571404794118376166183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 59254856635607858691545237 2777571404794118376166183)
  ·
    refine ⟨4166357107191177564249275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2777571404794118376166183 4166357107191177564249275)
    ·
      refine ⟨6249535660786766346373913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4166357107191177564249275 6249535660786766346373913)
      ·
        refine ⟨4687151745590074759780435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6249535660786766346373913 4687151745590074759780435)
        ·
          refine ⟨7030727618385112139670653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4687151745590074759780435 7030727618385112139670653)
          ·
            refine ⟨2636522856894417052376495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7030727618385112139670653 2636522856894417052376495)
            ·
              refine ⟨3954784285341625578564743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2636522856894417052376495 3954784285341625578564743)
              ·
                refine ⟨5932176428012438367847115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3954784285341625578564743 5932176428012438367847115)
                ·
                  refine ⟨8898264642018657551770673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5932176428012438367847115 8898264642018657551770673)
                  ·
                    refine ⟨6673698481513993163828005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8898264642018657551770673 6673698481513993163828005)
                    ·
                      refine ⟨1251318465283873718217751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6673698481513993163828005 1251318465283873718217751)
                      ·
                        rfl

theorem cell23_2436934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_2436934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2436934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2436934 prefixEnd_2436934 := by exact prefixLift 2436934
  have htrace : WordTrace (prefixWord ++ tailWord_2436934) baseStart_2436934 baseEnd_2436934 := by
    simpa [prefixWord, tailWord_2436934, baseEnd_2436934] using wordTrace_append hprefix tailTrace_2436934
  have hstable : (prefixWord ++ tailWord_2436934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2436934).length < 2 ^ (prefixWord ++ tailWord_2436934).sum := by decide
  have hdescent : baseEnd_2436934 < baseStart_2436934 := by decide
  rcases family_descends (prefixWord ++ tailWord_2436934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2436937 : List Nat := [1, 2, 1, 1, 2, 4, 5, 1, 2, 1, 3]
def baseStart_2436937 : Nat := 118140960795 + 2436937 * 2 ^ 59
def prefixEnd_2436937 : Nat := 4983230072969 + 3 ^ 40 * 2436937 * 2
def baseEnd_2436937 : Nat := 1251320005725837206480237

theorem tailTrace_2436937 : CollatzResearch.WordTrace tailWord_2436937 prefixEnd_2436937 1251320005725837206480237 := by
  unfold tailWord_2436937
  simp only [CollatzResearch.WordTrace]
  refine ⟨88882394372400919549677065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59254929581600613033118043 88882394372400919549677065)
  ·
    refine ⟨66661795779300689662257799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88882394372400919549677065 66661795779300689662257799)
    ·
      refine ⟨99992693668951034493386699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66661795779300689662257799 99992693668951034493386699)
      ·
        refine ⟨149989040503426551740080049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99992693668951034493386699 149989040503426551740080049)
        ·
          refine ⟨112491780377569913805060037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149989040503426551740080049 112491780377569913805060037)
          ·
            refine ⟨21092208820794358838448757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 112491780377569913805060037 21092208820794358838448757)
            ·
              refine ⟨1977394576949471141104571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21092208820794358838448757 1977394576949471141104571)
              ·
                refine ⟨2966091865424206711656857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1977394576949471141104571 2966091865424206711656857)
                ·
                  refine ⟨2224568899068155033742643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2966091865424206711656857 2224568899068155033742643)
                  ·
                    refine ⟨3336853348602232550613965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2224568899068155033742643 3336853348602232550613965)
                    ·
                      refine ⟨1251320005725837206480237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3336853348602232550613965 1251320005725837206480237)
                      ·
                        rfl

theorem cell23_2436937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 5, 1, 2, 1, 3].length) (baseStart_2436937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2436937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2436937 prefixEnd_2436937 := by exact prefixLift 2436937
  have htrace : WordTrace (prefixWord ++ tailWord_2436937) baseStart_2436937 baseEnd_2436937 := by
    simpa [prefixWord, tailWord_2436937, baseEnd_2436937] using wordTrace_append hprefix tailTrace_2436937
  have hstable : (prefixWord ++ tailWord_2436937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2436937).length < 2 ^ (prefixWord ++ tailWord_2436937).sum := by decide
  have hdescent : baseEnd_2436937 < baseStart_2436937 := by decide
  rcases family_descends (prefixWord ++ tailWord_2436937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2436973 : List Nat := [1, 5, 1, 1, 1, 1, 2, 1, 4, 2, 4]
def baseStart_2436973 : Nat := 118140960795 + 2436973 * 2 ^ 59
def prefixEnd_2436973 : Nat := 4983230072969 + 3 ^ 40 * 2436973 * 2
def baseEnd_2436973 : Nat := 1251338491029399065630071

theorem tailTrace_2436973 : CollatzResearch.WordTrace tailWord_2436973 prefixEnd_2436973 1251338491029399065630071 := by
  unfold tailWord_2436973
  simp only [CollatzResearch.WordTrace]
  refine ⟨88883707400270497697987573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59255804933513665131991715 88883707400270497697987573)
  ·
    refine ⟨8332847568775359159186335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 88883707400270497697987573 8332847568775359159186335)
    ·
      refine ⟨12499271353163038738779503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8332847568775359159186335 12499271353163038738779503)
      ·
        refine ⟨18748907029744558108169255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12499271353163038738779503 18748907029744558108169255)
        ·
          refine ⟨28123360544616837162253883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18748907029744558108169255 28123360544616837162253883)
          ·
            refine ⟨42185040816925255743380825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28123360544616837162253883 42185040816925255743380825)
            ·
              refine ⟨31638780612693941807535619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42185040816925255743380825 31638780612693941807535619)
              ·
                refine ⟨47458170919040912711303429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31638780612693941807535619 47458170919040912711303429)
                ·
                  refine ⟨8898407047320171133369393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47458170919040912711303429 8898407047320171133369393)
                  ·
                    refine ⟨6673805285490128350027045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8898407047320171133369393 6673805285490128350027045)
                    ·
                      refine ⟨1251338491029399065630071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6673805285490128350027045 1251338491029399065630071)
                      ·
                        rfl

theorem cell23_2436973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 4, 2, 4].length) (baseStart_2436973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2436973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2436973 prefixEnd_2436973 := by exact prefixLift 2436973
  have htrace : WordTrace (prefixWord ++ tailWord_2436973) baseStart_2436973 baseEnd_2436973 := by
    simpa [prefixWord, tailWord_2436973, baseEnd_2436973] using wordTrace_append hprefix tailTrace_2436973
  have hstable : (prefixWord ++ tailWord_2436973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2436973).length < 2 ^ (prefixWord ++ tailWord_2436973).sum := by decide
  have hdescent : baseEnd_2436973 < baseStart_2436973 := by decide
  rcases family_descends (prefixWord ++ tailWord_2436973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2436976 : List Nat := [2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 9]
def baseStart_2436976 : Nat := 118140960795 + 2436976 * 2 ^ 59
def prefixEnd_2436976 : Nat := 4983230072969 + 3 ^ 40 * 2436976 * 2
def baseEnd_2436976 : Nat := 1251340031471362553892557

theorem tailTrace_2436976 : CollatzResearch.WordTrace tailWord_2436976 prefixEnd_2436976 1251340031471362553892557 := by
  unfold tailWord_2436976
  simp only [CollatzResearch.WordTrace]
  refine ⟨44441908409629814605173391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59255877879506419473564521 44441908409629814605173391)
  ·
    refine ⟨66662862614444721907760087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44441908409629814605173391 66662862614444721907760087)
    ·
      refine ⟨99994293921667082861640131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66662862614444721907760087 99994293921667082861640131)
      ·
        refine ⟨149991440882500624292460197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99994293921667082861640131 149991440882500624292460197)
        ·
          refine ⟨28123395165468867054836287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 149991440882500624292460197 28123395165468867054836287)
          ·
            refine ⟨42185092748203300582254431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28123395165468867054836287 42185092748203300582254431)
            ·
              refine ⟨63277639122304950873381647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42185092748203300582254431 63277639122304950873381647)
              ·
                refine ⟨94916458683457426310072471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63277639122304950873381647 94916458683457426310072471)
                ·
                  refine ⟨142374688025186139465108707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 94916458683457426310072471 142374688025186139465108707)
                  ·
                    refine ⟨213562032037779209197663061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 142374688025186139465108707 213562032037779209197663061)
                    ·
                      refine ⟨1251340031471362553892557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 213562032037779209197663061 1251340031471362553892557)
                      ·
                        rfl

theorem cell23_2436976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 9].length) (baseStart_2436976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2436976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2436976 prefixEnd_2436976 := by exact prefixLift 2436976
  have htrace : WordTrace (prefixWord ++ tailWord_2436976) baseStart_2436976 baseEnd_2436976 := by
    simpa [prefixWord, tailWord_2436976, baseEnd_2436976] using wordTrace_append hprefix tailTrace_2436976
  have hstable : (prefixWord ++ tailWord_2436976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2436976).length < 2 ^ (prefixWord ++ tailWord_2436976).sum := by decide
  have hdescent : baseEnd_2436976 < baseStart_2436976 := by decide
  rcases family_descends (prefixWord ++ tailWord_2436976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2436977 : List Nat := [1, 2, 2, 2, 1, 3, 2, 4, 2, 2, 2]
def baseStart_2436977 : Nat := 118140960795 + 2436977 * 2 ^ 59
def prefixEnd_2436977 : Nat := 4983230072969 + 3 ^ 40 * 2436977 * 2
def baseEnd_2436977 : Nat := 1251340544952017049980053

theorem tailTrace_2436977 : CollatzResearch.WordTrace tailWord_2436977 prefixEnd_2436977 1251340544952017049980053 := by
  unfold tailWord_2436977
  simp only [CollatzResearch.WordTrace]
  refine ⟨88883853292256006381133185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59255902194837337587422123 88883853292256006381133185)
  ·
    refine ⟨66662889969192004785849889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88883853292256006381133185 66662889969192004785849889)
    ·
      refine ⟨49997167476894003589387417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66662889969192004785849889 49997167476894003589387417)
      ·
        refine ⟨37497875607670502692040563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49997167476894003589387417 37497875607670502692040563)
        ·
          refine ⟨56246813411505754038060845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37497875607670502692040563 56246813411505754038060845)
          ·
            refine ⟨21092555029314657764272817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56246813411505754038060845 21092555029314657764272817)
            ·
              refine ⟨15819416271985993323204613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21092555029314657764272817 15819416271985993323204613)
              ·
                refine ⟨2966140550997373748100865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15819416271985993323204613 2966140550997373748100865)
                ·
                  refine ⟨2224605413248030311075649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2966140550997373748100865 2224605413248030311075649)
                  ·
                    refine ⟨1668454059936022733306737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2224605413248030311075649 1668454059936022733306737)
                    ·
                      refine ⟨1251340544952017049980053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1668454059936022733306737 1251340544952017049980053)
                      ·
                        rfl

theorem cell23_2436977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 4, 2, 2, 2].length) (baseStart_2436977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2436977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2436977 prefixEnd_2436977 := by exact prefixLift 2436977
  have htrace : WordTrace (prefixWord ++ tailWord_2436977) baseStart_2436977 baseEnd_2436977 := by
    simpa [prefixWord, tailWord_2436977, baseEnd_2436977] using wordTrace_append hprefix tailTrace_2436977
  have hstable : (prefixWord ++ tailWord_2436977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2436977).length < 2 ^ (prefixWord ++ tailWord_2436977).sum := by decide
  have hdescent : baseEnd_2436977 < baseStart_2436977 := by decide
  rcases family_descends (prefixWord ++ tailWord_2436977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2437033 : List Nat := [1, 2, 1, 1, 1, 1, 4, 3, 4, 1, 4]
def baseStart_2437033 : Nat := 118140960795 + 2437033 * 2 ^ 59
def prefixEnd_2437033 : Nat := 4983230072969 + 3 ^ 40 * 2437033 * 2
def baseEnd_2437033 : Nat := 1251369299868668830879795

theorem tailTrace_2437033 : CollatzResearch.WordTrace tailWord_2437033 prefixEnd_2437033 1251369299868668830879795 := by
  unfold tailWord_2437033
  simp only [CollatzResearch.WordTrace]
  refine ⟨88885895780053127945171753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59257263853368751963447835 88885895780053127945171753)
  ·
    refine ⟨66664421835039845958878815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88885895780053127945171753 66664421835039845958878815)
    ·
      refine ⟨99996632752559768938318223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66664421835039845958878815 99996632752559768938318223)
      ·
        refine ⟨149994949128839653407477335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99996632752559768938318223 149994949128839653407477335)
        ·
          refine ⟨224992423693259480111216003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149994949128839653407477335 224992423693259480111216003)
          ·
            refine ⟨337488635539889220166824005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 224992423693259480111216003 337488635539889220166824005)
            ·
              refine ⟨63279119163729228781279501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 337488635539889220166824005 63279119163729228781279501)
              ·
                refine ⟨23729669686398460792979813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63279119163729228781279501 23729669686398460792979813)
                ·
                  refine ⟨4449313066199711398683715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23729669686398460792979813 4449313066199711398683715)
                  ·
                    refine ⟨6673969599299567098025573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4449313066199711398683715 6673969599299567098025573)
                    ·
                      refine ⟨1251369299868668830879795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6673969599299567098025573 1251369299868668830879795)
                      ·
                        rfl

theorem cell23_2437033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 3, 4, 1, 4].length) (baseStart_2437033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2437033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2437033 prefixEnd_2437033 := by exact prefixLift 2437033
  have htrace : WordTrace (prefixWord ++ tailWord_2437033) baseStart_2437033 baseEnd_2437033 := by
    simpa [prefixWord, tailWord_2437033, baseEnd_2437033] using wordTrace_append hprefix tailTrace_2437033
  have hstable : (prefixWord ++ tailWord_2437033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2437033).length < 2 ^ (prefixWord ++ tailWord_2437033).sum := by decide
  have hdescent : baseEnd_2437033 < baseStart_2437033 := by decide
  rcases family_descends (prefixWord ++ tailWord_2437033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2437044 : List Nat := [2, 5, 2, 1, 2, 1, 1, 1, 2, 3, 3]
def baseStart_2437044 : Nat := 118140960795 + 2437044 * 2 ^ 59
def prefixEnd_2437044 : Nat := 4983230072969 + 3 ^ 40 * 2437044 * 2
def baseEnd_2437044 : Nat := 1251374948155868287842245

theorem tailTrace_2437044 : CollatzResearch.WordTrace tailWord_2437044 prefixEnd_2437044 1251374948155868287842245 := by
  unfold tailWord_2437044
  simp only [CollatzResearch.WordTrace]
  refine ⟨44443148491506638411911093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59257531322008851215881457 44443148491506638411911093)
  ·
    refine ⟨4166545171078747351116665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 44443148491506638411911093 4166545171078747351116665)
    ·
      refine ⟨3124908878309060513337499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4166545171078747351116665 3124908878309060513337499)
      ·
        refine ⟨4687363317463590770006249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3124908878309060513337499 4687363317463590770006249)
        ·
          refine ⟨3515522488097693077504687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4687363317463590770006249 3515522488097693077504687)
          ·
            refine ⟨5273283732146539616257031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3515522488097693077504687 5273283732146539616257031)
            ·
              refine ⟨7909925598219809424385547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5273283732146539616257031 7909925598219809424385547)
              ·
                refine ⟨11864888397329714136578321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7909925598219809424385547 11864888397329714136578321)
                ·
                  refine ⟨8898666297997285602433741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11864888397329714136578321 8898666297997285602433741)
                  ·
                    refine ⟨3336999861748982100912653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8898666297997285602433741 3336999861748982100912653)
                    ·
                      refine ⟨1251374948155868287842245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3336999861748982100912653 1251374948155868287842245)
                      ·
                        rfl

theorem cell23_2437044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_2437044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2437044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2437044 prefixEnd_2437044 := by exact prefixLift 2437044
  have htrace : WordTrace (prefixWord ++ tailWord_2437044) baseStart_2437044 baseEnd_2437044 := by
    simpa [prefixWord, tailWord_2437044, baseEnd_2437044] using wordTrace_append hprefix tailTrace_2437044
  have hstable : (prefixWord ++ tailWord_2437044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2437044).length < 2 ^ (prefixWord ++ tailWord_2437044).sum := by decide
  have hdescent : baseEnd_2437044 < baseStart_2437044 := by decide
  rcases family_descends (prefixWord ++ tailWord_2437044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2437070 : List Nat := [4, 1, 1, 1, 2, 2, 3, 1, 1, 4, 3]
def baseStart_2437070 : Nat := 118140960795 + 2437070 * 2 ^ 59
def prefixEnd_2437070 : Nat := 4983230072969 + 3 ^ 40 * 2437070 * 2
def baseEnd_2437070 : Nat := 1251388298652885186117125

theorem tailTrace_2437070 : CollatzResearch.WordTrace tailWord_2437070 prefixEnd_2437070 1251388298652885186117125 := by
  unfold tailWord_2437070
  simp only [CollatzResearch.WordTrace]
  refine ⟨11110905660114885408033583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59258163520612722176179109 11110905660114885408033583)
  ·
    refine ⟨16666358490172328112050375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11110905660114885408033583 16666358490172328112050375)
    ·
      refine ⟨24999537735258492168075563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16666358490172328112050375 24999537735258492168075563)
      ·
        refine ⟨37499306602887738252113345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24999537735258492168075563 37499306602887738252113345)
        ·
          refine ⟨28124479952165803689085009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37499306602887738252113345 28124479952165803689085009)
          ·
            refine ⟨21093359964124352766813757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28124479952165803689085009 21093359964124352766813757)
            ·
              refine ⟨7910009986546632287555159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21093359964124352766813757 7910009986546632287555159)
              ·
                refine ⟨11865014979819948431332739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7910009986546632287555159 11865014979819948431332739)
                ·
                  refine ⟨17797522469729922646999109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11865014979819948431332739 17797522469729922646999109)
                  ·
                    refine ⟨3337035463074360496312333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17797522469729922646999109 3337035463074360496312333)
                    ·
                      refine ⟨1251388298652885186117125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3337035463074360496312333 1251388298652885186117125)
                      ·
                        rfl

theorem cell23_2437070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 1, 1, 4, 3].length) (baseStart_2437070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2437070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2437070 prefixEnd_2437070 := by exact prefixLift 2437070
  have htrace : WordTrace (prefixWord ++ tailWord_2437070) baseStart_2437070 baseEnd_2437070 := by
    simpa [prefixWord, tailWord_2437070, baseEnd_2437070] using wordTrace_append hprefix tailTrace_2437070
  have hstable : (prefixWord ++ tailWord_2437070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2437070).length < 2 ^ (prefixWord ++ tailWord_2437070).sum := by decide
  have hdescent : baseEnd_2437070 < baseStart_2437070 := by decide
  rcases family_descends (prefixWord ++ tailWord_2437070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2437117 : List Nat := [1, 4, 1, 1, 1, 2, 4, 2, 3, 1, 3]
def baseStart_2437117 : Nat := 118140960795 + 2437117 * 2 ^ 59
def prefixEnd_2437117 : Nat := 4983230072969 + 3 ^ 40 * 2437117 * 2
def baseEnd_2437117 : Nat := 1251412432243646502229409

theorem tailTrace_2437117 : CollatzResearch.WordTrace tailWord_2437117 prefixEnd_2437117 1251412432243646502229409 := by
  unfold tailWord_2437117
  simp only [CollatzResearch.WordTrace]
  refine ⟨88888959511748810291229605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59259306341165873527486403 88888959511748810291229605)
  ·
    refine ⟨16666679908452901929605551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88888959511748810291229605 16666679908452901929605551)
    ·
      refine ⟨25000019862679352894408327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16666679908452901929605551 25000019862679352894408327)
      ·
        refine ⟨37500029794019029341612491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25000019862679352894408327 37500029794019029341612491)
        ·
          refine ⟨56250044691028544012418737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37500029794019029341612491 56250044691028544012418737)
          ·
            refine ⟨42187533518271408009314053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56250044691028544012418737 42187533518271408009314053)
            ·
              refine ⟨7910162534675889001746385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42187533518271408009314053 7910162534675889001746385)
              ·
                refine ⟨5932621901006916751309789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7910162534675889001746385 5932621901006916751309789)
                ·
                  refine ⟨2224733212877593781741171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5932621901006916751309789 2224733212877593781741171)
                  ·
                    refine ⟨3337099819316390672611757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2224733212877593781741171 3337099819316390672611757)
                    ·
                      refine ⟨1251412432243646502229409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3337099819316390672611757 1251412432243646502229409)
                      ·
                        rfl

theorem cell23_2437117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 2, 3, 1, 3].length) (baseStart_2437117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2437117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2437117 prefixEnd_2437117 := by exact prefixLift 2437117
  have htrace : WordTrace (prefixWord ++ tailWord_2437117) baseStart_2437117 baseEnd_2437117 := by
    simpa [prefixWord, tailWord_2437117, baseEnd_2437117] using wordTrace_append hprefix tailTrace_2437117
  have hstable : (prefixWord ++ tailWord_2437117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2437117).length < 2 ^ (prefixWord ++ tailWord_2437117).sum := by decide
  have hdescent : baseEnd_2437117 < baseStart_2437117 := by decide
  rcases family_descends (prefixWord ++ tailWord_2437117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2437123 : List Nat := [1, 1, 1, 3, 2, 1, 1, 2, 2, 5, 4]
def baseStart_2437123 : Nat := 118140960795 + 2437123 * 2 ^ 59
def prefixEnd_2437123 : Nat := 4983230072969 + 3 ^ 40 * 2437123 * 2
def baseEnd_2437123 : Nat := 1251415513127573478754381

theorem tailTrace_2437123 : CollatzResearch.WordTrace tailWord_2437123 prefixEnd_2437123 1251415513127573478754381 := by
  unfold tailWord_2437123
  simp only [CollatzResearch.WordTrace]
  refine ⟨88889178349727073315948023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59259452233151382210632015 88889178349727073315948023)
  ·
    refine ⟨133333767524590609973922035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88889178349727073315948023 133333767524590609973922035)
    ·
      refine ⟨200000651286885914960883053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133333767524590609973922035 200000651286885914960883053)
      ·
        refine ⟨75000244232582218110331145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 200000651286885914960883053 75000244232582218110331145)
        ·
          refine ⟨56250183174436663582748359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75000244232582218110331145 56250183174436663582748359)
          ·
            refine ⟨84375274761654995374122539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56250183174436663582748359 84375274761654995374122539)
            ·
              refine ⟨126562912142482493061183809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84375274761654995374122539 126562912142482493061183809)
              ·
                refine ⟨94922184106861869795887857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 126562912142482493061183809 94922184106861869795887857)
                ·
                  refine ⟨71191638080146402346915893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 94922184106861869795887857 71191638080146402346915893)
                  ·
                    refine ⟨6674216070013725220023365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 71191638080146402346915893 6674216070013725220023365)
                    ·
                      refine ⟨1251415513127573478754381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6674216070013725220023365 1251415513127573478754381)
                      ·
                        rfl

theorem cell23_2437123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 5, 4].length) (baseStart_2437123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2437123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2437123 prefixEnd_2437123 := by exact prefixLift 2437123
  have htrace : WordTrace (prefixWord ++ tailWord_2437123) baseStart_2437123 baseEnd_2437123 := by
    simpa [prefixWord, tailWord_2437123, baseEnd_2437123] using wordTrace_append hprefix tailTrace_2437123
  have hstable : (prefixWord ++ tailWord_2437123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2437123).length < 2 ^ (prefixWord ++ tailWord_2437123).sum := by decide
  have hdescent : baseEnd_2437123 < baseStart_2437123 := by decide
  rcases family_descends (prefixWord ++ tailWord_2437123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2437127 : List Nat := [1, 1, 4, 3, 1, 2, 2, 1, 1, 5, 2]
def baseStart_2437127 : Nat := 118140960795 + 2437127 * 2 ^ 59
def prefixEnd_2437127 : Nat := 4983230072969 + 3 ^ 40 * 2437127 * 2
def baseEnd_2437127 : Nat := 1251417567050191463104363

theorem tailTrace_2437127 : CollatzResearch.WordTrace tailWord_2437127 prefixEnd_2437127 1251417567050191463104363 := by
  unfold tailWord_2437127
  simp only [CollatzResearch.WordTrace]
  refine ⟨88889324241712581999093635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59259549494475054666062423 88889324241712581999093635)
  ·
    refine ⟨133333986362568872998640453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88889324241712581999093635 133333986362568872998640453)
    ·
      refine ⟨25000122442981663687245085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 133333986362568872998640453 25000122442981663687245085)
      ·
        refine ⟨9375045916118123882716907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25000122442981663687245085 9375045916118123882716907)
        ·
          refine ⟨14062568874177185824075361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9375045916118123882716907 14062568874177185824075361)
          ·
            refine ⟨10546926655632889368056521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14062568874177185824075361 10546926655632889368056521)
            ·
              refine ⟨7910194991724667026042391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10546926655632889368056521 7910194991724667026042391)
              ·
                refine ⟨11865292487587000539063587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7910194991724667026042391 11865292487587000539063587)
                ·
                  refine ⟨17797938731380500808595381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11865292487587000539063587 17797938731380500808595381)
                  ·
                    refine ⟨1668556756066921950805817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17797938731380500808595381 1668556756066921950805817)
                    ·
                      refine ⟨1251417567050191463104363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1668556756066921950805817 1251417567050191463104363)
                      ·
                        rfl

theorem cell23_2437127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 1, 1, 5, 2].length) (baseStart_2437127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2437127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2437127 prefixEnd_2437127 := by exact prefixLift 2437127
  have htrace : WordTrace (prefixWord ++ tailWord_2437127) baseStart_2437127 baseEnd_2437127 := by
    simpa [prefixWord, tailWord_2437127, baseEnd_2437127] using wordTrace_append hprefix tailTrace_2437127
  have hstable : (prefixWord ++ tailWord_2437127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2437127).length < 2 ^ (prefixWord ++ tailWord_2437127).sum := by decide
  have hdescent : baseEnd_2437127 < baseStart_2437127 := by decide
  rcases family_descends (prefixWord ++ tailWord_2437127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2437151 : List Nat := [1, 1, 2, 4, 1, 2, 5, 2, 1, 1, 3]
def baseStart_2437151 : Nat := 118140960795 + 2437151 * 2 ^ 59
def prefixEnd_2437151 : Nat := 4983230072969 + 3 ^ 40 * 2437151 * 2
def baseEnd_2437151 : Nat := 1251429890585899369204253

theorem tailTrace_2437151 : CollatzResearch.WordTrace tailWord_2437151 prefixEnd_2437151 1251429890585899369204253 := by
  unfold tailWord_2437151
  simp only [CollatzResearch.WordTrace]
  refine ⟨88890199593625634097967307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59260133062417089398644871 88890199593625634097967307)
  ·
    refine ⟨133335299390438451146950961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88890199593625634097967307 133335299390438451146950961)
    ·
      refine ⟨100001474542828838360213221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133335299390438451146950961 100001474542828838360213221)
      ·
        refine ⟨18750276476780407192539979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 100001474542828838360213221 18750276476780407192539979)
        ·
          refine ⟨28125414715170610788809969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18750276476780407192539979 28125414715170610788809969)
          ·
            refine ⟨21094061036377958091607477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28125414715170610788809969 21094061036377958091607477)
            ·
              refine ⟨1977568222160433571088201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21094061036377958091607477 1977568222160433571088201)
              ·
                refine ⟨1483176166620325178316151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1977568222160433571088201 1483176166620325178316151)
                ·
                  refine ⟨2224764249930487767474227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1483176166620325178316151 2224764249930487767474227)
                  ·
                    refine ⟨3337146374895731651211341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2224764249930487767474227 3337146374895731651211341)
                    ·
                      refine ⟨1251429890585899369204253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3337146374895731651211341 1251429890585899369204253)
                      ·
                        rfl

theorem cell23_2437151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 5, 2, 1, 1, 3].length) (baseStart_2437151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2437151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2437151 prefixEnd_2437151 := by exact prefixLift 2437151
  have htrace : WordTrace (prefixWord ++ tailWord_2437151) baseStart_2437151 baseEnd_2437151 := by
    simpa [prefixWord, tailWord_2437151, baseEnd_2437151] using wordTrace_append hprefix tailTrace_2437151
  have hstable : (prefixWord ++ tailWord_2437151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2437151).length < 2 ^ (prefixWord ++ tailWord_2437151).sum := by decide
  have hdescent : baseEnd_2437151 < baseStart_2437151 := by decide
  rcases family_descends (prefixWord ++ tailWord_2437151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2437170 : List Nat := [3, 2, 1, 1, 2, 3, 2, 1, 1, 1, 6]
def baseStart_2437170 : Nat := 118140960795 + 2437170 * 2 ^ 59
def prefixEnd_2437170 : Nat := 4983230072969 + 3 ^ 40 * 2437170 * 2
def baseEnd_2437170 : Nat := 1251439646718334794866665

theorem tailTrace_2437170 : CollatzResearch.WordTrace tailWord_2437170 prefixEnd_2437170 1251439646718334794866665 := by
  unfold tailWord_2437170
  simp only [CollatzResearch.WordTrace]
  refine ⟨22222723145139200085727241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59260595053704533561939309 22222723145139200085727241)
  ·
    refine ⟨16667042358854400064295431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22222723145139200085727241 16667042358854400064295431)
    ·
      refine ⟨25000563538281600096443147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16667042358854400064295431 25000563538281600096443147)
      ·
        refine ⟨37500845307422400144664721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25000563538281600096443147 37500845307422400144664721)
        ·
          refine ⟨28125633980566800108498541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37500845307422400144664721 28125633980566800108498541)
          ·
            refine ⟨10547112742712550040686953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28125633980566800108498541 10547112742712550040686953)
            ·
              refine ⟨7910334557034412530515215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10547112742712550040686953 7910334557034412530515215)
              ·
                refine ⟨11865501835551618795772823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7910334557034412530515215 11865501835551618795772823)
                ·
                  refine ⟨17798252753327428193659235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11865501835551618795772823 17798252753327428193659235)
                  ·
                    refine ⟨26697379129991142290488853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17798252753327428193659235 26697379129991142290488853)
                    ·
                      refine ⟨1251439646718334794866665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26697379129991142290488853 1251439646718334794866665)
                      ·
                        rfl

theorem cell23_2437170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 1, 1, 1, 6].length) (baseStart_2437170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2437170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2437170 prefixEnd_2437170 := by exact prefixLift 2437170
  have htrace : WordTrace (prefixWord ++ tailWord_2437170) baseStart_2437170 baseEnd_2437170 := by
    simpa [prefixWord, tailWord_2437170, baseEnd_2437170] using wordTrace_append hprefix tailTrace_2437170
  have hstable : (prefixWord ++ tailWord_2437170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2437170).length < 2 ^ (prefixWord ++ tailWord_2437170).sum := by decide
  have hdescent : baseEnd_2437170 < baseStart_2437170 := by decide
  rcases family_descends (prefixWord ++ tailWord_2437170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2437191 : List Nat := [1, 1, 4, 1, 3, 1, 2, 5, 1, 2, 2]
def baseStart_2437191 : Nat := 118140960795 + 2437191 * 2 ^ 59
def prefixEnd_2437191 : Nat := 4983230072969 + 3 ^ 40 * 2437191 * 2
def baseEnd_2437191 : Nat := 1251450429812079212704069

theorem tailTrace_2437191 : CollatzResearch.WordTrace tailWord_2437191 prefixEnd_2437191 1251450429812079212704069 := by
  unfold tailWord_2437191
  simp only [CollatzResearch.WordTrace]
  refine ⟨88891658513480720929423427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59261105675653813952948951 88891658513480720929423427)
  ·
    refine ⟨133337487770221081394135141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88891658513480720929423427 133337487770221081394135141)
    ·
      refine ⟨25000778956916452761400339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 133337487770221081394135141 25000778956916452761400339)
      ·
        refine ⟨37501168435374679142100509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25000778956916452761400339 37501168435374679142100509)
        ·
          refine ⟨14062938163265504678287691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37501168435374679142100509 14062938163265504678287691)
          ·
            refine ⟨21094407244898257017431537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14062938163265504678287691 21094407244898257017431537)
            ·
              refine ⟨15820805433673692763073653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21094407244898257017431537 15820805433673692763073653)
              ·
                refine ⟨1483200509406908696538155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15820805433673692763073653 1483200509406908696538155)
                ·
                  refine ⟨2224800764110363044807233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1483200509406908696538155 2224800764110363044807233)
                  ·
                    refine ⟨1668600573082772283605425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2224800764110363044807233 1668600573082772283605425)
                    ·
                      refine ⟨1251450429812079212704069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1668600573082772283605425 1251450429812079212704069)
                      ·
                        rfl

theorem cell23_2437191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 5, 1, 2, 2].length) (baseStart_2437191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2437191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2437191 prefixEnd_2437191 := by exact prefixLift 2437191
  have htrace : WordTrace (prefixWord ++ tailWord_2437191) baseStart_2437191 baseEnd_2437191 := by
    simpa [prefixWord, tailWord_2437191, baseEnd_2437191] using wordTrace_append hprefix tailTrace_2437191
  have hstable : (prefixWord ++ tailWord_2437191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2437191).length < 2 ^ (prefixWord ++ tailWord_2437191).sum := by decide
  have hdescent : baseEnd_2437191 < baseStart_2437191 := by decide
  rcases family_descends (prefixWord ++ tailWord_2437191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2437207 : List Nat := [1, 1, 3, 2, 2, 1, 2, 3, 4, 1, 3]
def baseStart_2437207 : Nat := 118140960795 + 2437207 * 2 ^ 59
def prefixEnd_2437207 : Nat := 4983230072969 + 3 ^ 40 * 2437207 * 2
def baseEnd_2437207 : Nat := 1251458645502551150103995

theorem tailTrace_2437207 : CollatzResearch.WordTrace tailWord_2437207 prefixEnd_2437207 1251458645502551150103995 := by
  unfold tailWord_2437207
  simp only [CollatzResearch.WordTrace]
  refine ⟨88892242081422755662005875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59261494720948503774670583 88892242081422755662005875)
  ·
    refine ⟨133338363122134133493008813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88892242081422755662005875 133338363122134133493008813)
    ·
      refine ⟨50001886170800300059878305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133338363122134133493008813 50001886170800300059878305)
      ·
        refine ⟨37501414628100225044908729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50001886170800300059878305 37501414628100225044908729)
        ·
          refine ⟨28126060971075168783681547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37501414628100225044908729 28126060971075168783681547)
          ·
            refine ⟨42189091456612753175522321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28126060971075168783681547 42189091456612753175522321)
            ·
              refine ⟨31641818592459564881641741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42189091456612753175522321 31641818592459564881641741)
              ·
                refine ⟨11865681972172336830615653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31641818592459564881641741 11865681972172336830615653)
                ·
                  refine ⟨2224815369782313155740435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11865681972172336830615653 2224815369782313155740435)
                  ·
                    refine ⟨3337223054673469733610653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2224815369782313155740435 3337223054673469733610653)
                    ·
                      refine ⟨1251458645502551150103995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3337223054673469733610653 1251458645502551150103995)
                      ·
                        rfl

theorem cell23_2437207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 3, 4, 1, 3].length) (baseStart_2437207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2437207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2437207 prefixEnd_2437207 := by exact prefixLift 2437207
  have htrace : WordTrace (prefixWord ++ tailWord_2437207) baseStart_2437207 baseEnd_2437207 := by
    simpa [prefixWord, tailWord_2437207, baseEnd_2437207] using wordTrace_append hprefix tailTrace_2437207
  have hstable : (prefixWord ++ tailWord_2437207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2437207).length < 2 ^ (prefixWord ++ tailWord_2437207).sum := by decide
  have hdescent : baseEnd_2437207 < baseStart_2437207 := by decide
  rcases family_descends (prefixWord ++ tailWord_2437207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2437208 : List Nat := [2, 1, 2, 2, 1, 4, 4, 2, 1, 2, 2]
def baseStart_2437208 : Nat := 118140960795 + 2437208 * 2 ^ 59
def prefixEnd_2437208 : Nat := 4983230072969 + 3 ^ 40 * 2437208 * 2
def baseEnd_2437208 : Nat := 1251459158983205646191491

theorem tailTrace_2437208 : CollatzResearch.WordTrace tailWord_2437208 prefixEnd_2437208 1251459158983205646191491 := by
  unfold tailWord_2437208
  simp only [CollatzResearch.WordTrace]
  refine ⟨44446139277209566416396139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59261519036279421888528185 44446139277209566416396139)
  ·
    refine ⟨66669208915814349624594209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44446139277209566416396139 66669208915814349624594209)
    ·
      refine ⟨50001906686860762218445657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66669208915814349624594209 50001906686860762218445657)
      ·
        refine ⟨37501430015145571663834243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50001906686860762218445657 37501430015145571663834243)
        ·
          refine ⟨56252145022718357495751365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37501430015145571663834243 56252145022718357495751365)
          ·
            refine ⟨10547277191759692030453381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56252145022718357495751365 10547277191759692030453381)
            ·
              refine ⟨1977614473454942255710009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10547277191759692030453381 1977614473454942255710009)
              ·
                refine ⟨1483210855091206691782507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1977614473454942255710009 1483210855091206691782507)
                ·
                  refine ⟨2224816282636810037673761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1483210855091206691782507 2224816282636810037673761)
                  ·
                    refine ⟨1668612211977607528255321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2224816282636810037673761 1668612211977607528255321)
                    ·
                      refine ⟨1251459158983205646191491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1668612211977607528255321 1251459158983205646191491)
                      ·
                        rfl

theorem cell23_2437208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 4, 2, 1, 2, 2].length) (baseStart_2437208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2437208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2437208 prefixEnd_2437208 := by exact prefixLift 2437208
  have htrace : WordTrace (prefixWord ++ tailWord_2437208) baseStart_2437208 baseEnd_2437208 := by
    simpa [prefixWord, tailWord_2437208, baseEnd_2437208] using wordTrace_append hprefix tailTrace_2437208
  have hstable : (prefixWord ++ tailWord_2437208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2437208).length < 2 ^ (prefixWord ++ tailWord_2437208).sum := by decide
  have hdescent : baseEnd_2437208 < baseStart_2437208 := by decide
  rcases family_descends (prefixWord ++ tailWord_2437208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2437234 : List Nat := [3, 2, 1, 2, 2, 2, 2, 1, 3, 3, 2]
def baseStart_2437234 : Nat := 118140960795 + 2437234 * 2 ^ 59
def prefixEnd_2437234 : Nat := 4983230072969 + 3 ^ 40 * 2437234 * 2
def baseEnd_2437234 : Nat := 1251472509480222544466371

theorem tailTrace_2437234 : CollatzResearch.WordTrace tailWord_2437234 prefixEnd_2437234 1251472509480222544466371 := by
  unfold tailWord_2437234
  simp only [CollatzResearch.WordTrace]
  refine ⟨22223306713081234818309689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59262151234883292848825837 22223306713081234818309689)
  ·
    refine ⟨16667480034810926113732267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22223306713081234818309689 16667480034810926113732267)
    ·
      refine ⟨25001220052216389170598401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16667480034810926113732267 25001220052216389170598401)
      ·
        refine ⟨18750915039162291877948801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25001220052216389170598401 18750915039162291877948801)
        ·
          refine ⟨14063186279371718908461601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18750915039162291877948801 14063186279371718908461601)
          ·
            refine ⟨10547389709528789181346201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14063186279371718908461601 10547389709528789181346201)
            ·
              refine ⟨7910542282146591886009651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10547389709528789181346201 7910542282146591886009651)
              ·
                refine ⟨11865813423219887829014477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7910542282146591886009651 11865813423219887829014477)
                ·
                  refine ⟨4449680033707457935880429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11865813423219887829014477 4449680033707457935880429)
                  ·
                    refine ⟨1668630012640296725955161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4449680033707457935880429 1668630012640296725955161)
                    ·
                      refine ⟨1251472509480222544466371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1668630012640296725955161 1251472509480222544466371)
                      ·
                        rfl

theorem cell23_2437234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 1, 3, 3, 2].length) (baseStart_2437234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2437234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2437234 prefixEnd_2437234 := by exact prefixLift 2437234
  have htrace : WordTrace (prefixWord ++ tailWord_2437234) baseStart_2437234 baseEnd_2437234 := by
    simpa [prefixWord, tailWord_2437234, baseEnd_2437234] using wordTrace_append hprefix tailTrace_2437234
  have hstable : (prefixWord ++ tailWord_2437234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2437234).length < 2 ^ (prefixWord ++ tailWord_2437234).sum := by decide
  have hdescent : baseEnd_2437234 < baseStart_2437234 := by decide
  rcases family_descends (prefixWord ++ tailWord_2437234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2437251 : List Nat := [1, 1, 1, 3, 3, 3, 4, 1, 1, 3, 2]
def baseStart_2437251 : Nat := 118140960795 + 2437251 * 2 ^ 59
def prefixEnd_2437251 : Nat := 4983230072969 + 3 ^ 40 * 2437251 * 2
def baseEnd_2437251 : Nat := 1251481238651348977953793

theorem tailTrace_2437251 : CollatzResearch.WordTrace tailWord_2437251 prefixEnd_2437251 1251481238651348977953793 := by
  unfold tailWord_2437251
  simp only [CollatzResearch.WordTrace]
  refine ⟨88893846893263351176607607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59262564595508900784405071 88893846893263351176607607)
  ·
    refine ⟨133340770339895026764911411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88893846893263351176607607 133340770339895026764911411)
    ·
      refine ⟨200011155509842540147367117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133340770339895026764911411 200011155509842540147367117)
      ·
        refine ⟨75004183316190952555262669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 200011155509842540147367117 75004183316190952555262669)
        ·
          refine ⟨28126568743571607208223501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75004183316190952555262669 28126568743571607208223501)
          ·
            refine ⟨10547463278839352703083813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28126568743571607208223501 10547463278839352703083813)
            ·
              refine ⟨1977649364782378631828215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10547463278839352703083813 1977649364782378631828215)
              ·
                refine ⟨2966474047173567947742323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1977649364782378631828215 2966474047173567947742323)
                ·
                  refine ⟨4449711070760351921613485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2966474047173567947742323 4449711070760351921613485)
                  ·
                    refine ⟨1668641651535131970605057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4449711070760351921613485 1668641651535131970605057)
                    ·
                      refine ⟨1251481238651348977953793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1668641651535131970605057 1251481238651348977953793)
                      ·
                        rfl

theorem cell23_2437251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 4, 1, 1, 3, 2].length) (baseStart_2437251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2437251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2437251 prefixEnd_2437251 := by exact prefixLift 2437251
  have htrace : WordTrace (prefixWord ++ tailWord_2437251) baseStart_2437251 baseEnd_2437251 := by
    simpa [prefixWord, tailWord_2437251, baseEnd_2437251] using wordTrace_append hprefix tailTrace_2437251
  have hstable : (prefixWord ++ tailWord_2437251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2437251).length < 2 ^ (prefixWord ++ tailWord_2437251).sum := by decide
  have hdescent : baseEnd_2437251 < baseStart_2437251 := by decide
  rcases family_descends (prefixWord ++ tailWord_2437251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2437264 : List Nat := [2, 1, 1, 1, 1, 1, 7, 1, 4, 2, 2]
def baseStart_2437264 : Nat := 118140960795 + 2437264 * 2 ^ 59
def prefixEnd_2437264 : Nat := 4983230072969 + 3 ^ 40 * 2437264 * 2
def baseEnd_2437264 : Nat := 1251487913899857427091233

theorem tailTrace_2437264 : CollatzResearch.WordTrace tailWord_2437264 prefixEnd_2437264 1251487913899857427091233 := by
  unfold tailWord_2437264
  simp only [CollatzResearch.WordTrace]
  refine ⟨44447160521108127198415423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59262880694810836264553897 44447160521108127198415423)
  ·
    refine ⟨66670740781662190797623135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44447160521108127198415423 66670740781662190797623135)
    ·
      refine ⟨100006111172493286196434703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66670740781662190797623135 100006111172493286196434703)
      ·
        refine ⟨150009166758739929294652055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100006111172493286196434703 150009166758739929294652055)
        ·
          refine ⟨225013750138109893941978083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150009166758739929294652055 225013750138109893941978083)
          ·
            refine ⟨337520625207164840912967125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 225013750138109893941978083 337520625207164840912967125)
            ·
              refine ⟨7910639653292925958897667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 337520625207164840912967125 7910639653292925958897667)
              ·
                refine ⟨11865959479939388938346501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7910639653292925958897667 11865959479939388938346501)
                ·
                  refine ⟨2224867402488635425939969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11865959479939388938346501 2224867402488635425939969)
                  ·
                    refine ⟨1668650551866476569454977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2224867402488635425939969 1668650551866476569454977)
                    ·
                      refine ⟨1251487913899857427091233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1668650551866476569454977 1251487913899857427091233)
                      ·
                        rfl

theorem cell23_2437264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 1, 4, 2, 2].length) (baseStart_2437264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2437264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2437264 prefixEnd_2437264 := by exact prefixLift 2437264
  have htrace : WordTrace (prefixWord ++ tailWord_2437264) baseStart_2437264 baseEnd_2437264 := by
    simpa [prefixWord, tailWord_2437264, baseEnd_2437264] using wordTrace_append hprefix tailTrace_2437264
  have hstable : (prefixWord ++ tailWord_2437264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2437264).length < 2 ^ (prefixWord ++ tailWord_2437264).sum := by decide
  have hdescent : baseEnd_2437264 < baseStart_2437264 := by decide
  rcases family_descends (prefixWord ++ tailWord_2437264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2437277 : List Nat := [1, 4, 2, 1, 1, 3, 2, 1, 2, 2, 4]
def baseStart_2437277 : Nat := 118140960795 + 2437277 * 2 ^ 59
def prefixEnd_2437277 : Nat := 4983230072969 + 3 ^ 40 * 2437277 * 2
def baseEnd_2437277 : Nat := 1251494589148365876228673

theorem tailTrace_2437277 : CollatzResearch.WordTrace tailWord_2437277 prefixEnd_2437277 1251494589148365876228673 := by
  unfold tailWord_2437277
  simp only [CollatzResearch.WordTrace]
  refine ⟨88894795191169157617054085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59263196794112771744702723 88894795191169157617054085)
  ·
    refine ⟨16667774098344217053197641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88894795191169157617054085 16667774098344217053197641)
    ·
      refine ⟨12500830573758162789898231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16667774098344217053197641 12500830573758162789898231)
      ·
        refine ⟨18751245860637244184847347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12500830573758162789898231 18751245860637244184847347)
        ·
          refine ⟨28126868790955866277271021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18751245860637244184847347 28126868790955866277271021)
          ·
            refine ⟨10547575796608449853976633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28126868790955866277271021 10547575796608449853976633)
            ·
              refine ⟨7910681847456337390482475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10547575796608449853976633 7910681847456337390482475)
              ·
                refine ⟨11866022771184506085723713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7910681847456337390482475 11866022771184506085723713)
                ·
                  refine ⟨8899517078388379564292785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11866022771184506085723713 8899517078388379564292785)
                  ·
                    refine ⟨6674637808791284673219589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8899517078388379564292785 6674637808791284673219589)
                    ·
                      refine ⟨1251494589148365876228673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6674637808791284673219589 1251494589148365876228673)
                      ·
                        rfl

theorem cell23_2437277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 1, 2, 2, 4].length) (baseStart_2437277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2437277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2437277 prefixEnd_2437277 := by exact prefixLift 2437277
  have htrace : WordTrace (prefixWord ++ tailWord_2437277) baseStart_2437277 baseEnd_2437277 := by
    simpa [prefixWord, tailWord_2437277, baseEnd_2437277] using wordTrace_append hprefix tailTrace_2437277
  have hstable : (prefixWord ++ tailWord_2437277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2437277).length < 2 ^ (prefixWord ++ tailWord_2437277).sum := by decide
  have hdescent : baseEnd_2437277 < baseStart_2437277 := by decide
  rcases family_descends (prefixWord ++ tailWord_2437277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2437281 : List Nat := [1, 2, 3, 3, 1, 4, 1, 1, 1, 4, 2]
def baseStart_2437281 : Nat := 118140960795 + 2437281 * 2 ^ 59
def prefixEnd_2437281 : Nat := 4983230072969 + 3 ^ 40 * 2437281 * 2
def baseEnd_2437281 : Nat := 1251496643070983860578655

theorem tailTrace_2437281 : CollatzResearch.WordTrace tailWord_2437281 prefixEnd_2437281 1251496643070983860578655 := by
  unfold tailWord_2437281
  simp only [CollatzResearch.WordTrace]
  refine ⟨88894941083154666300199697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59263294055436444200133131 88894941083154666300199697)
  ·
    refine ⟨66671205812365999725149773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88894941083154666300199697 66671205812365999725149773)
    ·
      refine ⟨25001702179637249896931165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66671205812365999725149773 25001702179637249896931165)
      ·
        refine ⟨9375638317363968711349187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25001702179637249896931165 9375638317363968711349187)
        ·
          refine ⟨14063457476045953067023781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9375638317363968711349187 14063457476045953067023781)
          ·
            refine ⟨2636898276758616200066959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14063457476045953067023781 2636898276758616200066959)
            ·
              refine ⟨3955347415137924300100439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2636898276758616200066959 3955347415137924300100439)
              ·
                refine ⟨5933021122706886450150659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3955347415137924300100439 5933021122706886450150659)
                ·
                  refine ⟨8899531684060329675225989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5933021122706886450150659 8899531684060329675225989)
                  ·
                    refine ⟨1668662190761311814104873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8899531684060329675225989 1668662190761311814104873)
                    ·
                      refine ⟨1251496643070983860578655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1668662190761311814104873 1251496643070983860578655)
                      ·
                        rfl

theorem cell23_2437281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 1, 1, 4, 2].length) (baseStart_2437281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2437281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2437281 prefixEnd_2437281 := by exact prefixLift 2437281
  have htrace : WordTrace (prefixWord ++ tailWord_2437281) baseStart_2437281 baseEnd_2437281 := by
    simpa [prefixWord, tailWord_2437281, baseEnd_2437281] using wordTrace_append hprefix tailTrace_2437281
  have hstable : (prefixWord ++ tailWord_2437281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2437281).length < 2 ^ (prefixWord ++ tailWord_2437281).sum := by decide
  have hdescent : baseEnd_2437281 < baseStart_2437281 := by decide
  rcases family_descends (prefixWord ++ tailWord_2437281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2437354 : List Nat := [3, 1, 3, 1, 1, 2, 4, 1, 2, 1, 4]
def baseStart_2437354 : Nat := 118140960795 + 2437354 * 2 ^ 59
def prefixEnd_2437354 : Nat := 4983230072969 + 3 ^ 40 * 2437354 * 2
def baseEnd_2437354 : Nat := 1251534127158762074965819

theorem tailTrace_2437354 : CollatzResearch.WordTrace tailWord_2437354 prefixEnd_2437354 1251534127158762074965819 := by
  unfold tailWord_2437354
  simp only [CollatzResearch.WordTrace]
  refine ⟨22224400902972549941901779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59265069074593466511738077 22224400902972549941901779)
  ·
    refine ⟨33336601354458824912852669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22224400902972549941901779 33336601354458824912852669)
    ·
      refine ⟨12501225507922059342319751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33336601354458824912852669 12501225507922059342319751)
      ·
        refine ⟨18751838261883089013479627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12501225507922059342319751 18751838261883089013479627)
        ·
          refine ⟨28127757392824633520219441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18751838261883089013479627 28127757392824633520219441)
          ·
            refine ⟨21095818044618475140164581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28127757392824633520219441 21095818044618475140164581)
            ·
              refine ⟨3955465883365964088780859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21095818044618475140164581 3955465883365964088780859)
              ·
                refine ⟨5933198825048946133171289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3955465883365964088780859 5933198825048946133171289)
                ·
                  refine ⟨4449899118786709599878467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5933198825048946133171289 4449899118786709599878467)
                  ·
                    refine ⟨6674848678180064399817701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4449899118786709599878467 6674848678180064399817701)
                    ·
                      refine ⟨1251534127158762074965819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6674848678180064399817701 1251534127158762074965819)
                      ·
                        rfl

theorem cell23_2437354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 1, 2, 1, 4].length) (baseStart_2437354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2437354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2437354 prefixEnd_2437354 := by exact prefixLift 2437354
  have htrace : WordTrace (prefixWord ++ tailWord_2437354) baseStart_2437354 baseEnd_2437354 := by
    simpa [prefixWord, tailWord_2437354, baseEnd_2437354] using wordTrace_append hprefix tailTrace_2437354
  have hstable : (prefixWord ++ tailWord_2437354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2437354).length < 2 ^ (prefixWord ++ tailWord_2437354).sum := by decide
  have hdescent : baseEnd_2437354 < baseStart_2437354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2437354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2437360 : List Nat := [2, 1, 1, 1, 3, 1, 1, 3, 10]
def baseStart_2437360 : Nat := 118140960795 + 2437360 * 2 ^ 59
def prefixEnd_2437360 : Nat := 4983230072969 + 3 ^ 40 * 2437360 * 2
def baseEnd_2437360 : Nat := 139059689782521005721199

theorem tailTrace_2437360 : CollatzResearch.WordTrace tailWord_2437360 prefixEnd_2437360 139059689782521005721199 := by
  unfold tailWord_2437360
  simp only [CollatzResearch.WordTrace]
  refine ⟨44448911224934231396162767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59265214966578975194883689 44448911224934231396162767)
  ·
    refine ⟨66673366837401347094244151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44448911224934231396162767 66673366837401347094244151)
    ·
      refine ⟨100010050256102020641366227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66673366837401347094244151 100010050256102020641366227)
      ·
        refine ⟨150015075384153030962049341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100010050256102020641366227 150015075384153030962049341)
        ·
          refine ⟨56255653269057386610768503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 150015075384153030962049341 56255653269057386610768503)
          ·
            refine ⟨84383479903586079916152755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56255653269057386610768503 84383479903586079916152755)
            ·
              refine ⟨126575219855379119874229133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84383479903586079916152755 126575219855379119874229133)
              ·
                refine ⟨47465707445767169952835925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 126575219855379119874229133 47465707445767169952835925)
                ·
                  refine ⟨139059689782521005721199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 47465707445767169952835925 139059689782521005721199)
                  ·
                    rfl

theorem cell23_2437360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 10].length) (baseStart_2437360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2437360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2437360 prefixEnd_2437360 := by exact prefixLift 2437360
  have htrace : WordTrace (prefixWord ++ tailWord_2437360) baseStart_2437360 baseEnd_2437360 := by
    simpa [prefixWord, tailWord_2437360, baseEnd_2437360] using wordTrace_append hprefix tailTrace_2437360
  have hstable : (prefixWord ++ tailWord_2437360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2437360).length < 2 ^ (prefixWord ++ tailWord_2437360).sum := by decide
  have hdescent : baseEnd_2437360 < baseStart_2437360 := by decide
  rcases family_descends (prefixWord ++ tailWord_2437360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2437438 : List Nat := [4, 2, 1, 2, 1, 3, 2, 1, 3, 1, 3]
def baseStart_2437438 : Nat := 118140960795 + 2437438 * 2 ^ 59
def prefixEnd_2437438 : Nat := 4983230072969 + 3 ^ 40 * 2437438 * 2
def baseEnd_2437438 : Nat := 1251577259533739746315433

theorem tailTrace_2437438 : CollatzResearch.WordTrace tailWord_2437438 prefixEnd_2437438 1251577259533739746315433 := by
  unfold tailWord_2437438
  simp only [CollatzResearch.WordTrace]
  refine ⟨11112583417948235264208121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59267111562390588075776645 11112583417948235264208121)
  ·
    refine ⟨8334437563461176448156091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11112583417948235264208121 8334437563461176448156091)
    ·
      refine ⟨12501656345191764672234137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8334437563461176448156091 12501656345191764672234137)
      ·
        refine ⟨9376242258893823504175603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12501656345191764672234137 9376242258893823504175603)
        ·
          refine ⟨14064363388340735256263405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9376242258893823504175603 14064363388340735256263405)
          ·
            refine ⟨5274136270627775721098777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14064363388340735256263405 5274136270627775721098777)
            ·
              refine ⟨3955602202970831790824083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5274136270627775721098777 3955602202970831790824083)
              ·
                refine ⟨5933403304456247686236125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3955602202970831790824083 5933403304456247686236125)
                ·
                  refine ⟨2225026239171092882338547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5933403304456247686236125 2225026239171092882338547)
                  ·
                    refine ⟨3337539358756639323507821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2225026239171092882338547 3337539358756639323507821)
                    ·
                      refine ⟨1251577259533739746315433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3337539358756639323507821 1251577259533739746315433)
                      ·
                        rfl

theorem cell23_2437438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 1, 3, 1, 3].length) (baseStart_2437438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2437438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2437438 prefixEnd_2437438 := by exact prefixLift 2437438
  have htrace : WordTrace (prefixWord ++ tailWord_2437438) baseStart_2437438 baseEnd_2437438 := by
    simpa [prefixWord, tailWord_2437438, baseEnd_2437438] using wordTrace_append hprefix tailTrace_2437438
  have hstable : (prefixWord ++ tailWord_2437438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2437438).length < 2 ^ (prefixWord ++ tailWord_2437438).sum := by decide
  have hdescent : baseEnd_2437438 < baseStart_2437438 := by decide
  rcases family_descends (prefixWord ++ tailWord_2437438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2437472 : List Nat := [2, 1, 1, 3, 6, 1, 1, 3, 1, 1, 3]
def baseStart_2437472 : Nat := 118140960795 + 2437472 * 2 ^ 59
def prefixEnd_2437472 : Nat := 4983230072969 + 3 ^ 40 * 2437472 * 2
def baseEnd_2437472 : Nat := 1251594717875992613290277

theorem tailTrace_2437472 : CollatzResearch.WordTrace tailWord_2437472 prefixEnd_2437472 1251594717875992613290277 := by
  unfold tailWord_2437472
  simp only [CollatzResearch.WordTrace]
  refine ⟨44450953712731352960201335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59267938283641803946935113 44450953712731352960201335)
  ·
    refine ⟨66676430569097029440302003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44450953712731352960201335 66676430569097029440302003)
    ·
      refine ⟨100014645853645544160453005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66676430569097029440302003 100014645853645544160453005)
      ·
        refine ⟨37505492195117079060169877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100014645853645544160453005 37505492195117079060169877)
        ·
          refine ⟨1758069946646113080945463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 37505492195117079060169877 1758069946646113080945463)
          ·
            refine ⟨2637104919969169621418195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1758069946646113080945463 2637104919969169621418195)
            ·
              refine ⟨3955657379953754432127293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2637104919969169621418195 3955657379953754432127293)
              ·
                refine ⟨1483371517482657912047735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3955657379953754432127293 1483371517482657912047735)
                ·
                  refine ⟨2225057276223986868071603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1483371517482657912047735 2225057276223986868071603)
                  ·
                    refine ⟨3337585914335980302107405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2225057276223986868071603 3337585914335980302107405)
                    ·
                      refine ⟨1251594717875992613290277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3337585914335980302107405 1251594717875992613290277)
                      ·
                        rfl

theorem cell23_2437472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 3, 1, 1, 3].length) (baseStart_2437472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2437472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2437472 prefixEnd_2437472 := by exact prefixLift 2437472
  have htrace : WordTrace (prefixWord ++ tailWord_2437472) baseStart_2437472 baseEnd_2437472 := by
    simpa [prefixWord, tailWord_2437472, baseEnd_2437472] using wordTrace_append hprefix tailTrace_2437472
  have hstable : (prefixWord ++ tailWord_2437472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2437472).length < 2 ^ (prefixWord ++ tailWord_2437472).sum := by decide
  have hdescent : baseEnd_2437472 < baseStart_2437472 := by decide
  rcases family_descends (prefixWord ++ tailWord_2437472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2437484 : List Nat := [2, 2, 1, 1, 6, 2, 9]
def baseStart_2437484 : Nat := 118140960795 + 2437484 * 2 ^ 59
def prefixEnd_2437484 : Nat := 4983230072969 + 3 ^ 40 * 2437484 * 2
def baseEnd_2437484 : Nat := 15451862711652426744941

theorem tailTrace_2437484 : CollatzResearch.WordTrace tailWord_2437484 prefixEnd_2437484 15451862711652426744941 := by
  unfold tailWord_2437484
  simp only [CollatzResearch.WordTrace]
  refine ⟨44451172550709615984919753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59268230067612821313226337 44451172550709615984919753)
  ·
    refine ⟨33338379413032211988689815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44451172550709615984919753 33338379413032211988689815)
    ·
      refine ⟨50007569119548317983034723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33338379413032211988689815 50007569119548317983034723)
      ·
        refine ⟨75011353679322476974552085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50007569119548317983034723 75011353679322476974552085)
        ·
          refine ⟨3516157203718241108182129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 75011353679322476974552085 3516157203718241108182129)
          ·
            refine ⟨2637117902788680831136597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3516157203718241108182129 2637117902788680831136597)
            ·
              refine ⟨15451862711652426744941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2637117902788680831136597 15451862711652426744941)
              ·
                rfl

theorem cell23_2437484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 9].length) (baseStart_2437484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2437484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2437484 prefixEnd_2437484 := by exact prefixLift 2437484
  have htrace : WordTrace (prefixWord ++ tailWord_2437484) baseStart_2437484 baseEnd_2437484 := by
    simpa [prefixWord, tailWord_2437484, baseEnd_2437484] using wordTrace_append hprefix tailTrace_2437484
  have hstable : (prefixWord ++ tailWord_2437484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2437484).length < 2 ^ (prefixWord ++ tailWord_2437484).sum := by decide
  have hdescent : baseEnd_2437484 < baseStart_2437484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2437484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2437497 : List Nat := [1, 2, 1, 3, 2, 1, 1, 3, 2, 7]
def baseStart_2437497 : Nat := 118140960795 + 2437497 * 2 ^ 59
def prefixEnd_2437497 : Nat := 4983230072969 + 3 ^ 40 * 2437497 * 2
def baseEnd_2437497 : Nat := 417202518297451671825887

theorem tailTrace_2437497 : CollatzResearch.WordTrace tailWord_2437497 prefixEnd_2437497 417202518297451671825887 := by
  unfold tailWord_2437497
  simp only [CollatzResearch.WordTrace]
  refine ⟨88902819250372135190062745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59268546166914756793375163 88902819250372135190062745)
  ·
    refine ⟨66677114437779101392547059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88902819250372135190062745 66677114437779101392547059)
    ·
      refine ⟨100015671656668652088820589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66677114437779101392547059 100015671656668652088820589)
      ·
        refine ⟨37505876871250744533307721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100015671656668652088820589 37505876871250744533307721)
        ·
          refine ⟨28129407653438058399980791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37505876871250744533307721 28129407653438058399980791)
          ·
            refine ⟨42194111480157087599971187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28129407653438058399980791 42194111480157087599971187)
            ·
              refine ⟨63291167220235631399956781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42194111480157087599971187 63291167220235631399956781)
              ·
                refine ⟨23734187707588361774983793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63291167220235631399956781 23734187707588361774983793)
                ·
                  refine ⟨17800640780691271331237845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23734187707588361774983793 17800640780691271331237845)
                  ·
                    refine ⟨417202518297451671825887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17800640780691271331237845 417202518297451671825887)
                    ·
                      rfl

theorem cell23_2437497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 3, 2, 7].length) (baseStart_2437497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2437497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2437497 prefixEnd_2437497 := by exact prefixLift 2437497
  have htrace : WordTrace (prefixWord ++ tailWord_2437497) baseStart_2437497 baseEnd_2437497 := by
    simpa [prefixWord, tailWord_2437497, baseEnd_2437497] using wordTrace_append hprefix tailTrace_2437497
  have hstable : (prefixWord ++ tailWord_2437497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2437497).length < 2 ^ (prefixWord ++ tailWord_2437497).sum := by decide
  have hdescent : baseEnd_2437497 < baseStart_2437497 := by decide
  rcases family_descends (prefixWord ++ tailWord_2437497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2437504 : List Nat := [2, 1, 1, 2, 1, 2, 1, 1, 1, 9, 2]
def baseStart_2437504 : Nat := 118140960795 + 2437504 * 2 ^ 59
def prefixEnd_2437504 : Nat := 4983230072969 + 3 ^ 40 * 2437504 * 2
def baseEnd_2437504 : Nat := 1251611149256936488090129

theorem tailTrace_2437504 : CollatzResearch.WordTrace tailWord_2437504 prefixEnd_2437504 1251611149256936488090129 := by
  unfold tailWord_2437504
  simp only [CollatzResearch.WordTrace]
  refine ⟨44451537280673387692783783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59268716374231183590378377 44451537280673387692783783)
  ·
    refine ⟨66677305921010081539175675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44451537280673387692783783 66677305921010081539175675)
    ·
      refine ⟨100015958881515122308763513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66677305921010081539175675 100015958881515122308763513)
      ·
        refine ⟨75011969161136341731572635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100015958881515122308763513 75011969161136341731572635)
        ·
          refine ⟨112517953741704512597358953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75011969161136341731572635 112517953741704512597358953)
          ·
            refine ⟨84388465306278384448019215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112517953741704512597358953 84388465306278384448019215)
            ·
              refine ⟨126582697959417576672028823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84388465306278384448019215 126582697959417576672028823)
              ·
                refine ⟨189874046939126365008043235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126582697959417576672028823 189874046939126365008043235)
                ·
                  refine ⟨284811070408689547512064853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 189874046939126365008043235 284811070408689547512064853)
                  ·
                    refine ⟨1668814865675915317453505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 284811070408689547512064853 1668814865675915317453505)
                    ·
                      refine ⟨1251611149256936488090129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1668814865675915317453505 1251611149256936488090129)
                      ·
                        rfl

theorem cell23_2437504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 1, 9, 2].length) (baseStart_2437504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2437504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2437504 prefixEnd_2437504 := by exact prefixLift 2437504
  have htrace : WordTrace (prefixWord ++ tailWord_2437504) baseStart_2437504 baseEnd_2437504 := by
    simpa [prefixWord, tailWord_2437504, baseEnd_2437504] using wordTrace_append hprefix tailTrace_2437504
  have hstable : (prefixWord ++ tailWord_2437504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2437504).length < 2 ^ (prefixWord ++ tailWord_2437504).sum := by decide
  have hdescent : baseEnd_2437504 < baseStart_2437504 := by decide
  rcases family_descends (prefixWord ++ tailWord_2437504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2437505 : List Nat := [1, 2, 4, 3, 1, 3, 2, 1, 2, 4]
def baseStart_2437505 : Nat := 118140960795 + 2437505 * 2 ^ 59
def prefixEnd_2437505 : Nat := 4983230072969 + 3 ^ 40 * 2437505 * 2
def baseEnd_2437505 : Nat := 417203887579196994725875

theorem tailTrace_2437505 : CollatzResearch.WordTrace tailWord_2437505 prefixEnd_2437505 417203887579196994725875 := by
  unfold tailWord_2437505
  simp only [CollatzResearch.WordTrace]
  refine ⟨88903111034343152556353969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59268740689562101704235979 88903111034343152556353969)
  ·
    refine ⟨66677333275757364417265477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88903111034343152556353969 66677333275757364417265477)
    ·
      refine ⟨12501999989204505828237277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66677333275757364417265477 12501999989204505828237277)
      ·
        refine ⟨4688249995951689685588979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12501999989204505828237277 4688249995951689685588979)
        ·
          refine ⟨7032374993927534528383469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4688249995951689685588979 7032374993927534528383469)
          ·
            refine ⟨2637140622722825448143801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7032374993927534528383469 2637140622722825448143801)
            ·
              refine ⟨1977855467042119086107851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2637140622722825448143801 1977855467042119086107851)
              ·
                refine ⟨2966783200563178629161777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1977855467042119086107851 2966783200563178629161777)
                ·
                  refine ⟨2225087400422383971871333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2966783200563178629161777 2225087400422383971871333)
                  ·
                    refine ⟨417203887579196994725875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2225087400422383971871333 417203887579196994725875)
                    ·
                      rfl

theorem cell23_2437505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 2, 1, 2, 4].length) (baseStart_2437505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2437505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2437505 prefixEnd_2437505 := by exact prefixLift 2437505
  have htrace : WordTrace (prefixWord ++ tailWord_2437505) baseStart_2437505 baseEnd_2437505 := by
    simpa [prefixWord, tailWord_2437505, baseEnd_2437505] using wordTrace_append hprefix tailTrace_2437505
  have hstable : (prefixWord ++ tailWord_2437505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2437505).length < 2 ^ (prefixWord ++ tailWord_2437505).sum := by decide
  have hdescent : baseEnd_2437505 < baseStart_2437505 := by decide
  rcases family_descends (prefixWord ++ tailWord_2437505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2437546 : List Nat := [3, 1, 6, 1, 1, 1, 1, 4, 1, 2, 2]
def baseStart_2437546 : Nat := 118140960795 + 2437546 * 2 ^ 59
def prefixEnd_2437546 : Nat := 4983230072969 + 3 ^ 40 * 2437546 * 2
def baseEnd_2437546 : Nat := 1251632715444425323764937

theorem tailTrace_2437546 : CollatzResearch.WordTrace tailWord_2437546 prefixEnd_2437546 1251632715444425323764937 := by
  unfold tailWord_2437546
  simp only [CollatzResearch.WordTrace]
  refine ⟨22226151606798654139649123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59269737618129744372397661 22226151606798654139649123)
  ·
    refine ⟨33339227410197981209473685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22226151606798654139649123 33339227410197981209473685)
    ·
      refine ⟨1562776284853030369194079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 33339227410197981209473685 1562776284853030369194079)
      ·
        refine ⟨2344164427279545553791119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1562776284853030369194079 2344164427279545553791119)
        ·
          refine ⟨3516246640919318330686679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2344164427279545553791119 3516246640919318330686679)
          ·
            refine ⟨5274369961378977496030019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3516246640919318330686679 5274369961378977496030019)
            ·
              refine ⟨7911554942068466244045029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5274369961378977496030019 7911554942068466244045029)
              ·
                refine ⟨1483416551637837420758443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7911554942068466244045029 1483416551637837420758443)
                ·
                  refine ⟨2225124827456756131137665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1483416551637837420758443 2225124827456756131137665)
                  ·
                    refine ⟨1668843620592567098353249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2225124827456756131137665 1668843620592567098353249)
                    ·
                      refine ⟨1251632715444425323764937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1668843620592567098353249 1251632715444425323764937)
                      ·
                        rfl

theorem cell23_2437546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_2437546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2437546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2437546 prefixEnd_2437546 := by exact prefixLift 2437546
  have htrace : WordTrace (prefixWord ++ tailWord_2437546) baseStart_2437546 baseEnd_2437546 := by
    simpa [prefixWord, tailWord_2437546, baseEnd_2437546] using wordTrace_append hprefix tailTrace_2437546
  have hstable : (prefixWord ++ tailWord_2437546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2437546).length < 2 ^ (prefixWord ++ tailWord_2437546).sum := by decide
  have hdescent : baseEnd_2437546 < baseStart_2437546 := by decide
  rcases family_descends (prefixWord ++ tailWord_2437546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2437554 : List Nat := [3, 2, 1, 1, 1, 1, 3, 1, 1, 6, 3]
def baseStart_2437554 : Nat := 118140960795 + 2437554 * 2 ^ 59
def prefixEnd_2437554 : Nat := 4983230072969 + 3 ^ 40 * 2437554 * 2
def baseEnd_2437554 : Nat := 1251636823289661292464899

theorem tailTrace_2437554 : CollatzResearch.WordTrace tailWord_2437554 prefixEnd_2437554 1251636823289661292464899 := by
  unfold tailWord_2437554
  simp only [CollatzResearch.WordTrace]
  refine ⟨22226224552791408481221929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59269932140777089283258477 22226224552791408481221929)
  ·
    refine ⟨16669668414593556360916447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22226224552791408481221929 16669668414593556360916447)
    ·
      refine ⟨25004502621890334541374671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16669668414593556360916447 25004502621890334541374671)
      ·
        refine ⟨37506753932835501812062007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25004502621890334541374671 37506753932835501812062007)
        ·
          refine ⟨56260130899253252718093011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37506753932835501812062007 56260130899253252718093011)
          ·
            refine ⟨84390196348879879077139517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56260130899253252718093011 84390196348879879077139517)
            ·
              refine ⟨31646323630829954653927319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84390196348879879077139517 31646323630829954653927319)
              ·
                refine ⟨47469485446244931980890979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31646323630829954653927319 47469485446244931980890979)
                ·
                  refine ⟨71204228169367397971336469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47469485446244931980890979 71204228169367397971336469)
                  ·
                    refine ⟨3337698195439096779906397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 71204228169367397971336469 3337698195439096779906397)
                    ·
                      refine ⟨1251636823289661292464899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3337698195439096779906397 1251636823289661292464899)
                      ·
                        rfl

theorem cell23_2437554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 1, 6, 3].length) (baseStart_2437554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2437554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2437554 prefixEnd_2437554 := by exact prefixLift 2437554
  have htrace : WordTrace (prefixWord ++ tailWord_2437554) baseStart_2437554 baseEnd_2437554 := by
    simpa [prefixWord, tailWord_2437554, baseEnd_2437554] using wordTrace_append hprefix tailTrace_2437554
  have hstable : (prefixWord ++ tailWord_2437554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2437554).length < 2 ^ (prefixWord ++ tailWord_2437554).sum := by decide
  have hdescent : baseEnd_2437554 < baseStart_2437554 := by decide
  rcases family_descends (prefixWord ++ tailWord_2437554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2437584 : List Nat := [2, 1, 1, 1, 1, 2, 2, 1, 6, 3, 3]
def baseStart_2437584 : Nat := 118140960795 + 2437584 * 2 ^ 59
def prefixEnd_2437584 : Nat := 4983230072969 + 3 ^ 40 * 2437584 * 2
def baseEnd_2437584 : Nat := 1251652227709296175089761

theorem tailTrace_2437584 : CollatzResearch.WordTrace tailWord_2437584 prefixEnd_2437584 1251652227709296175089761 := by
  unfold tailWord_2437584
  simp only [CollatzResearch.WordTrace]
  refine ⟨44452996200528474524239903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59270661600704632698986537 44452996200528474524239903)
  ·
    refine ⟨66679494300792711786359855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44452996200528474524239903 66679494300792711786359855)
    ·
      refine ⟨100019241451189067679539783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66679494300792711786359855 100019241451189067679539783)
      ·
        refine ⟨150028862176783601519309675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100019241451189067679539783 150028862176783601519309675)
        ·
          refine ⟨225043293265175402278964513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150028862176783601519309675 225043293265175402278964513)
          ·
            refine ⟨168782469948881551709223385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 225043293265175402278964513 168782469948881551709223385)
            ·
              refine ⟨126586852461661163781917539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 168782469948881551709223385 126586852461661163781917539)
              ·
                refine ⟨189880278692491745672876309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126586852461661163781917539 189880278692491745672876309)
                ·
                  refine ⟨8900638063710550578416077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 189880278692491745672876309 8900638063710550578416077)
                  ·
                    refine ⟨3337739273891456466906029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8900638063710550578416077 3337739273891456466906029)
                    ·
                      refine ⟨1251652227709296175089761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3337739273891456466906029 1251652227709296175089761)
                      ·
                        rfl

theorem cell23_2437584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 6, 3, 3].length) (baseStart_2437584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2437584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2437584 prefixEnd_2437584 := by exact prefixLift 2437584
  have htrace : WordTrace (prefixWord ++ tailWord_2437584) baseStart_2437584 baseEnd_2437584 := by
    simpa [prefixWord, tailWord_2437584, baseEnd_2437584] using wordTrace_append hprefix tailTrace_2437584
  have hstable : (prefixWord ++ tailWord_2437584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2437584).length < 2 ^ (prefixWord ++ tailWord_2437584).sum := by decide
  have hdescent : baseEnd_2437584 < baseStart_2437584 := by decide
  rcases family_descends (prefixWord ++ tailWord_2437584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2437624 : List Nat := [2, 1, 2, 1, 1, 4, 1, 1, 3, 3, 4]
def baseStart_2437624 : Nat := 118140960795 + 2437624 * 2 ^ 59
def prefixEnd_2437624 : Nat := 4983230072969 + 3 ^ 40 * 2437624 * 2
def baseEnd_2437624 : Nat := 1251672766935476018589577

theorem tailTrace_2437624 : CollatzResearch.WordTrace tailWord_2437624 prefixEnd_2437624 1251672766935476018589577 := by
  unfold tailWord_2437624
  simp only [CollatzResearch.WordTrace]
  refine ⟨44453725660456017939967963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59271634213941357253290617 44453725660456017939967963)
  ·
    refine ⟨66680588490684026909951945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44453725660456017939967963 66680588490684026909951945)
    ·
      refine ⟨50010441368013020182463959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66680588490684026909951945 50010441368013020182463959)
      ·
        refine ⟨75015662052019530273695939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50010441368013020182463959 75015662052019530273695939)
        ·
          refine ⟨112523493078029295410543909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75015662052019530273695939 112523493078029295410543909)
          ·
            refine ⟨21098154952130492889476983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 112523493078029295410543909 21098154952130492889476983)
            ·
              refine ⟨31647232428195739334215475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21098154952130492889476983 31647232428195739334215475)
              ·
                refine ⟨47470848642293609001323213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31647232428195739334215475 47470848642293609001323213)
                ·
                  refine ⟨17801568240860103375496205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47470848642293609001323213 17801568240860103375496205)
                  ·
                    refine ⟨6675588090322538765811077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17801568240860103375496205 6675588090322538765811077)
                    ·
                      refine ⟨1251672766935476018589577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6675588090322538765811077 1251672766935476018589577)
                      ·
                        rfl

theorem cell23_2437624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 3, 3, 4].length) (baseStart_2437624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2437624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2437624 prefixEnd_2437624 := by exact prefixLift 2437624
  have htrace : WordTrace (prefixWord ++ tailWord_2437624) baseStart_2437624 baseEnd_2437624 := by
    simpa [prefixWord, tailWord_2437624, baseEnd_2437624] using wordTrace_append hprefix tailTrace_2437624
  have hstable : (prefixWord ++ tailWord_2437624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2437624).length < 2 ^ (prefixWord ++ tailWord_2437624).sum := by decide
  have hdescent : baseEnd_2437624 < baseStart_2437624 := by decide
  rcases family_descends (prefixWord ++ tailWord_2437624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2437641 : List Nat := [1, 2, 1, 1, 3, 1, 2, 2, 4, 4, 2]
def baseStart_2437641 : Nat := 118140960795 + 2437641 * 2 ^ 59
def prefixEnd_2437641 : Nat := 4983230072969 + 3 ^ 40 * 2437641 * 2
def baseEnd_2437641 : Nat := 1251681496106602452076999

theorem tailTrace_2437641 : CollatzResearch.WordTrace tailWord_2437641 prefixEnd_2437641 1251681496106602452076999 := by
  unfold tailWord_2437641
  simp only [CollatzResearch.WordTrace]
  refine ⟨88908071361850447783304777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59272047574566965188869851 88908071361850447783304777)
  ·
    refine ⟨66681053521387835837478583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88908071361850447783304777 66681053521387835837478583)
    ·
      refine ⟨100021580282081753756217875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66681053521387835837478583 100021580282081753756217875)
      ·
        refine ⟨150032370423122630634326813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100021580282081753756217875 150032370423122630634326813)
        ·
          refine ⟨56262138908670986487872555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 150032370423122630634326813 56262138908670986487872555)
          ·
            refine ⟨84393208363006479731808833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56262138908670986487872555 84393208363006479731808833)
            ·
              refine ⟨63294906272254859798856625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84393208363006479731808833 63294906272254859798856625)
              ·
                refine ⟨47471179704191144849142469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63294906272254859798856625 47471179704191144849142469)
                ·
                  refine ⟨8900846194535839659214213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47471179704191144849142469 8900846194535839659214213)
                  ·
                    refine ⟨1668908661475469936102665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8900846194535839659214213 1668908661475469936102665)
                    ·
                      refine ⟨1251681496106602452076999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1668908661475469936102665 1251681496106602452076999)
                      ·
                        rfl

theorem cell23_2437641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 4, 4, 2].length) (baseStart_2437641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2437641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2437641 prefixEnd_2437641 := by exact prefixLift 2437641
  have htrace : WordTrace (prefixWord ++ tailWord_2437641) baseStart_2437641 baseEnd_2437641 := by
    simpa [prefixWord, tailWord_2437641, baseEnd_2437641] using wordTrace_append hprefix tailTrace_2437641
  have hstable : (prefixWord ++ tailWord_2437641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2437641).length < 2 ^ (prefixWord ++ tailWord_2437641).sum := by decide
  have hdescent : baseEnd_2437641 < baseStart_2437641 := by decide
  rcases family_descends (prefixWord ++ tailWord_2437641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2437704 : List Nat := [2, 1, 3, 1, 1, 1, 1, 2, 1, 3, 7]
def baseStart_2437704 : Nat := 118140960795 + 2437704 * 2 ^ 59
def prefixEnd_2437704 : Nat := 4983230072969 + 3 ^ 40 * 2437704 * 2
def baseEnd_2437704 : Nat := 1251713845387835705589209

theorem tailTrace_2437704 : CollatzResearch.WordTrace tailWord_2437704 prefixEnd_2437704 1251713845387835705589209 := by
  unfold tailWord_2437704
  simp only [CollatzResearch.WordTrace]
  refine ⟨44455184580311104771424083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59273579440414806361898777 44455184580311104771424083)
  ·
    refine ⟨66682776870466657157136125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44455184580311104771424083 66682776870466657157136125)
    ·
      refine ⟨25006041326424996433926047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66682776870466657157136125 25006041326424996433926047)
      ·
        refine ⟨37509061989637494650889071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25006041326424996433926047 37509061989637494650889071)
        ·
          refine ⟨56263592984456241976333607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37509061989637494650889071 56263592984456241976333607)
          ·
            refine ⟨84395389476684362964500411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56263592984456241976333607 84395389476684362964500411)
            ·
              refine ⟨126593084215026544446750617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84395389476684362964500411 126593084215026544446750617)
              ·
                refine ⟨94944813161269908335062963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 126593084215026544446750617 94944813161269908335062963)
                ·
                  refine ⟨142417219741904862502594445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 94944813161269908335062963 142417219741904862502594445)
                  ·
                    refine ⟨53406457403214323438472917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 142417219741904862502594445 53406457403214323438472917)
                    ·
                      refine ⟨1251713845387835705589209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 53406457403214323438472917 1251713845387835705589209)
                      ·
                        rfl

theorem cell23_2437704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 1, 3, 7].length) (baseStart_2437704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2437704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2437704 prefixEnd_2437704 := by exact prefixLift 2437704
  have htrace : WordTrace (prefixWord ++ tailWord_2437704) baseStart_2437704 baseEnd_2437704 := by
    simpa [prefixWord, tailWord_2437704, baseEnd_2437704] using wordTrace_append hprefix tailTrace_2437704
  have hstable : (prefixWord ++ tailWord_2437704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2437704).length < 2 ^ (prefixWord ++ tailWord_2437704).sum := by decide
  have hdescent : baseEnd_2437704 < baseStart_2437704 := by decide
  rcases family_descends (prefixWord ++ tailWord_2437704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2437711 : List Nat := [1, 1, 2, 1, 1, 2, 4, 5, 1, 5]
def baseStart_2437711 : Nat := 118140960795 + 2437711 * 2 ^ 59
def prefixEnd_2437711 : Nat := 4983230072969 + 3 ^ 40 * 2437711 * 2
def baseEnd_2437711 : Nat := 417239146584139059400559

theorem tailTrace_2437711 : CollatzResearch.WordTrace tailWord_2437711 prefixEnd_2437711 417239146584139059400559 := by
  unfold tailWord_2437711
  simp only [CollatzResearch.WordTrace]
  refine ⟨88910624471596849738352987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59273749647731233158901991 88910624471596849738352987)
  ·
    refine ⟨133365936707395274607529481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88910624471596849738352987 133365936707395274607529481)
    ·
      refine ⟨100024452530546455955647111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133365936707395274607529481 100024452530546455955647111)
      ·
        refine ⟨150036678795819683933470667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100024452530546455955647111 150036678795819683933470667)
        ·
          refine ⟨225055018193729525900206001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150036678795819683933470667 225055018193729525900206001)
          ·
            refine ⟨168791263645297144425154501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 225055018193729525900206001 168791263645297144425154501)
            ·
              refine ⟨31648361933493214579716469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 168791263645297144425154501 31648361933493214579716469)
              ·
                refine ⟨2967033931264988866848419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31648361933493214579716469 2967033931264988866848419)
                ·
                  refine ⟨4450550896897483300272629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2967033931264988866848419 4450550896897483300272629)
                  ·
                    refine ⟨417239146584139059400559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4450550896897483300272629 417239146584139059400559)
                    ·
                      rfl

theorem cell23_2437711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 5, 1, 5].length) (baseStart_2437711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2437711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2437711 prefixEnd_2437711 := by exact prefixLift 2437711
  have htrace : WordTrace (prefixWord ++ tailWord_2437711) baseStart_2437711 baseEnd_2437711 := by
    simpa [prefixWord, tailWord_2437711, baseEnd_2437711] using wordTrace_append hprefix tailTrace_2437711
  have hstable : (prefixWord ++ tailWord_2437711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2437711).length < 2 ^ (prefixWord ++ tailWord_2437711).sum := by decide
  have hdescent : baseEnd_2437711 < baseStart_2437711 := by decide
  rcases family_descends (prefixWord ++ tailWord_2437711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2437731 : List Nat := [1, 1, 1, 5, 1, 2, 1, 1, 5, 1, 4]
def baseStart_2437731 : Nat := 118140960795 + 2437731 * 2 ^ 59
def prefixEnd_2437731 : Nat := 4983230072969 + 3 ^ 40 * 2437731 * 2
def baseEnd_2437731 : Nat := 1251727709365507099951585

theorem tailTrace_2437731 : CollatzResearch.WordTrace tailWord_2437731 prefixEnd_2437731 1251727709365507099951585 := by
  unfold tailWord_2437731
  simp only [CollatzResearch.WordTrace]
  refine ⟨88911353931524393154081047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59274235954349595436054031 88911353931524393154081047)
  ·
    refine ⟨133367030897286589731121571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88911353931524393154081047 133367030897286589731121571)
    ·
      refine ⟨200050546345929884596682357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133367030897286589731121571 200050546345929884596682357)
      ·
        refine ⟨18754738719930926680938971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 200050546345929884596682357 18754738719930926680938971)
        ·
          refine ⟨28132108079896390021408457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18754738719930926680938971 28132108079896390021408457)
          ·
            refine ⟨21099081059922292516056343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28132108079896390021408457 21099081059922292516056343)
            ·
              refine ⟨31648621589883438774084515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21099081059922292516056343 31648621589883438774084515)
              ·
                refine ⟨47472932384825158161126773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31648621589883438774084515 47472932384825158161126773)
                ·
                  refine ⟨4450587411077358577605635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47472932384825158161126773 4450587411077358577605635)
                  ·
                    refine ⟨6675881116616037866408453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4450587411077358577605635 6675881116616037866408453)
                    ·
                      refine ⟨1251727709365507099951585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6675881116616037866408453 1251727709365507099951585)
                      ·
                        rfl

theorem cell23_2437731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 5, 1, 4].length) (baseStart_2437731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2437731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2437731 prefixEnd_2437731 := by exact prefixLift 2437731
  have htrace : WordTrace (prefixWord ++ tailWord_2437731) baseStart_2437731 baseEnd_2437731 := by
    simpa [prefixWord, tailWord_2437731, baseEnd_2437731] using wordTrace_append hprefix tailTrace_2437731
  have hstable : (prefixWord ++ tailWord_2437731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2437731).length < 2 ^ (prefixWord ++ tailWord_2437731).sum := by decide
  have hdescent : baseEnd_2437731 < baseStart_2437731 := by decide
  rcases family_descends (prefixWord ++ tailWord_2437731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2437765 : List Nat := [1, 3, 1, 1, 4, 2, 4, 1, 1, 1, 4]
def baseStart_2437765 : Nat := 118140960795 + 2437765 * 2 ^ 59
def prefixEnd_2437765 : Nat := 4983230072969 + 3 ^ 40 * 2437765 * 2
def baseEnd_2437765 : Nat := 1251745167707759966926429

theorem tailTrace_2437765 : CollatzResearch.WordTrace tailWord_2437765 prefixEnd_2437765 1251745167707759966926429 := by
  unfold tailWord_2437765
  simp only [CollatzResearch.WordTrace]
  refine ⟨88912594013401216960818749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59275062675600811307212499 88912594013401216960818749)
  ·
    refine ⟨33342222755025456360307031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88912594013401216960818749 33342222755025456360307031)
    ·
      refine ⟨50013334132538184540460547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33342222755025456360307031 50013334132538184540460547)
      ·
        refine ⟨75020001198807276810690821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50013334132538184540460547 75020001198807276810690821)
        ·
          refine ⟨14066250224776364402004529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75020001198807276810690821 14066250224776364402004529)
          ·
            refine ⟨10549687668582273301503397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14066250224776364402004529 10549687668582273301503397)
            ·
              refine ⟨1978066437859176244031887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10549687668582273301503397 1978066437859176244031887)
              ·
                refine ⟨2967099656788764366047831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1978066437859176244031887 2967099656788764366047831)
                ·
                  refine ⟨4450649485183146549071747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2967099656788764366047831 4450649485183146549071747)
                  ·
                    refine ⟨6675974227774719823607621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4450649485183146549071747 6675974227774719823607621)
                    ·
                      refine ⟨1251745167707759966926429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6675974227774719823607621 1251745167707759966926429)
                      ·
                        rfl

theorem cell23_2437765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 4, 1, 1, 1, 4].length) (baseStart_2437765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2437765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2437765 prefixEnd_2437765 := by exact prefixLift 2437765
  have htrace : WordTrace (prefixWord ++ tailWord_2437765) baseStart_2437765 baseEnd_2437765 := by
    simpa [prefixWord, tailWord_2437765, baseEnd_2437765] using wordTrace_append hprefix tailTrace_2437765
  have hstable : (prefixWord ++ tailWord_2437765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2437765).length < 2 ^ (prefixWord ++ tailWord_2437765).sum := by decide
  have hdescent : baseEnd_2437765 < baseStart_2437765 := by decide
  rcases family_descends (prefixWord ++ tailWord_2437765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2437781 : List Nat := [1, 3, 2, 1, 1, 1, 1, 1, 2, 7, 3]
def baseStart_2437781 : Nat := 118140960795 + 2437781 * 2 ^ 59
def prefixEnd_2437781 : Nat := 4983230072969 + 3 ^ 40 * 2437781 * 2
def baseEnd_2437781 : Nat := 1251753383398231904326355

theorem tailTrace_2437781 : CollatzResearch.WordTrace tailWord_2437781 prefixEnd_2437781 1251753383398231904326355 := by
  unfold tailWord_2437781
  simp only [CollatzResearch.WordTrace]
  refine ⟨88913177581343251693401197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59275451720895501128934131 88913177581343251693401197)
  ·
    refine ⟨33342441593003719385025449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88913177581343251693401197 33342441593003719385025449)
    ·
      refine ⟨25006831194752789538769087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33342441593003719385025449 25006831194752789538769087)
      ·
        refine ⟨37510246792129184308153631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25006831194752789538769087 37510246792129184308153631)
        ·
          refine ⟨56265370188193776462230447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37510246792129184308153631 56265370188193776462230447)
          ·
            refine ⟨84398055282290664693345671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56265370188193776462230447 84398055282290664693345671)
            ·
              refine ⟨126597082923435997040018507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84398055282290664693345671 126597082923435997040018507)
              ·
                refine ⟨189895624385153995560027761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126597082923435997040018507 189895624385153995560027761)
                ·
                  refine ⟨142421718288865496670020821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 189895624385153995560027761 142421718288865496670020821)
                  ·
                    refine ⟨3338009022395285078203613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 142421718288865496670020821 3338009022395285078203613)
                    ·
                      refine ⟨1251753383398231904326355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3338009022395285078203613 1251753383398231904326355)
                      ·
                        rfl

theorem cell23_2437781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 7, 3].length) (baseStart_2437781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2437781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2437781 prefixEnd_2437781 := by exact prefixLift 2437781
  have htrace : WordTrace (prefixWord ++ tailWord_2437781) baseStart_2437781 baseEnd_2437781 := by
    simpa [prefixWord, tailWord_2437781, baseEnd_2437781] using wordTrace_append hprefix tailTrace_2437781
  have hstable : (prefixWord ++ tailWord_2437781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2437781).length < 2 ^ (prefixWord ++ tailWord_2437781).sum := by decide
  have hdescent : baseEnd_2437781 < baseStart_2437781 := by decide
  rcases family_descends (prefixWord ++ tailWord_2437781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2437792 : List Nat := [2, 1, 1, 4, 4, 1, 3, 1, 2, 4]
def baseStart_2437792 : Nat := 118140960795 + 2437792 * 2 ^ 59
def prefixEnd_2437792 : Nat := 4983230072969 + 3 ^ 40 * 2437792 * 2
def baseEnd_2437792 : Nat := 417253010561810453762935

theorem tailTrace_2437792 : CollatzResearch.WordTrace tailWord_2437792 prefixEnd_2437792 417253010561810453762935 := by
  unfold tailWord_2437792
  simp only [CollatzResearch.WordTrace]
  refine ⟨44456789392151700286025815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59275719189535600381367753 44456789392151700286025815)
  ·
    refine ⟨66685184088227550429038723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44456789392151700286025815 66685184088227550429038723)
    ·
      refine ⟨100027776132341325643558085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66685184088227550429038723 100027776132341325643558085)
      ·
        refine ⟨18755208024813998558167141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 100027776132341325643558085 18755208024813998558167141)
        ·
          refine ⟨3516601504652624729656339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18755208024813998558167141 3516601504652624729656339)
          ·
            refine ⟨5274902256978937094484509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3516601504652624729656339 5274902256978937094484509)
            ·
              refine ⟨1978088346367101410431691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5274902256978937094484509 1978088346367101410431691)
              ·
                refine ⟨2967132519550652115647537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1978088346367101410431691 2967132519550652115647537)
                ·
                  refine ⟨2225349389662989086735653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2967132519550652115647537 2225349389662989086735653)
                  ·
                    refine ⟨417253010561810453762935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2225349389662989086735653 417253010561810453762935)
                    ·
                      rfl

theorem cell23_2437792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 3, 1, 2, 4].length) (baseStart_2437792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2437792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2437792 prefixEnd_2437792 := by exact prefixLift 2437792
  have htrace : WordTrace (prefixWord ++ tailWord_2437792) baseStart_2437792 baseEnd_2437792 := by
    simpa [prefixWord, tailWord_2437792, baseEnd_2437792] using wordTrace_append hprefix tailTrace_2437792
  have hstable : (prefixWord ++ tailWord_2437792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2437792).length < 2 ^ (prefixWord ++ tailWord_2437792).sum := by decide
  have hdescent : baseEnd_2437792 < baseStart_2437792 := by decide
  rcases family_descends (prefixWord ++ tailWord_2437792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2437805 : List Nat := [1, 5, 2, 1, 1, 4, 2, 7]
def baseStart_2437805 : Nat := 118140960795 + 2437805 * 2 ^ 59
def prefixEnd_2437805 : Nat := 4983230072969 + 3 ^ 40 * 2437805 * 2
def baseEnd_2437805 : Nat := 46361692849405178163935

theorem tailTrace_2437805 : CollatzResearch.WordTrace tailWord_2437805 prefixEnd_2437805 46361692849405178163935 := by
  unfold tailWord_2437805
  simp only [CollatzResearch.WordTrace]
  refine ⟨88914052933256303792274869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59276035288837535861516579 88914052933256303792274869)
  ·
    refine ⟨8335692462492778480525769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 88914052933256303792274869 8335692462492778480525769)
    ·
      refine ⟨6251769346869583860394327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8335692462492778480525769 6251769346869583860394327)
      ·
        refine ⟨9377654020304375790591491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6251769346869583860394327 9377654020304375790591491)
        ·
          refine ⟨14066481030456563685887237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9377654020304375790591491 14066481030456563685887237)
          ·
            refine ⟨2637465193210605691103857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14066481030456563685887237 2637465193210605691103857)
            ·
              refine ⟨1978098894907954268327893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2637465193210605691103857 1978098894907954268327893)
              ·
                refine ⟨46361692849405178163935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1978098894907954268327893 46361692849405178163935)
                ·
                  rfl

theorem cell23_2437805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 2, 7].length) (baseStart_2437805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2437805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2437805 prefixEnd_2437805 := by exact prefixLift 2437805
  have htrace : WordTrace (prefixWord ++ tailWord_2437805) baseStart_2437805 baseEnd_2437805 := by
    simpa [prefixWord, tailWord_2437805, baseEnd_2437805] using wordTrace_append hprefix tailTrace_2437805
  have hstable : (prefixWord ++ tailWord_2437805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2437805).length < 2 ^ (prefixWord ++ tailWord_2437805).sum := by decide
  have hdescent : baseEnd_2437805 < baseStart_2437805 := by decide
  rcases family_descends (prefixWord ++ tailWord_2437805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2437811 : List Nat := [1, 1, 1, 2, 3, 4, 1, 1, 2, 2, 5]
def baseStart_2437811 : Nat := 118140960795 + 2437811 * 2 ^ 59
def prefixEnd_2437811 : Nat := 4983230072969 + 3 ^ 40 * 2437811 * 2
def baseEnd_2437811 : Nat := 1251768787817866786951217

theorem tailTrace_2437811 : CollatzResearch.WordTrace tailWord_2437811 prefixEnd_2437811 1251768787817866786951217 := by
  unfold tailWord_2437811
  simp only [CollatzResearch.WordTrace]
  refine ⟨88914271771234566816993287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59276181180823044544662191 88914271771234566816993287)
  ·
    refine ⟨133371407656851850225489931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88914271771234566816993287 133371407656851850225489931)
    ·
      refine ⟨200057111485277775338234897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133371407656851850225489931 200057111485277775338234897)
      ·
        refine ⟨150042833613958331503676173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 200057111485277775338234897 150042833613958331503676173)
        ·
          refine ⟨56266062605234374313878565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 150042833613958331503676173 56266062605234374313878565)
          ·
            refine ⟨10549886738481445183852231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56266062605234374313878565 10549886738481445183852231)
            ·
              refine ⟨15824830107722167775778347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10549886738481445183852231 15824830107722167775778347)
              ·
                refine ⟨23737245161583251663667521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15824830107722167775778347 23737245161583251663667521)
                ·
                  refine ⟨17802933871187438747750641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23737245161583251663667521 17802933871187438747750641)
                  ·
                    refine ⟨13352200403390579060812981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17802933871187438747750641 13352200403390579060812981)
                    ·
                      refine ⟨1251768787817866786951217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13352200403390579060812981 1251768787817866786951217)
                      ·
                        rfl

theorem cell23_2437811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 2, 2, 5].length) (baseStart_2437811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2437811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2437811 prefixEnd_2437811 := by exact prefixLift 2437811
  have htrace : WordTrace (prefixWord ++ tailWord_2437811) baseStart_2437811 baseEnd_2437811 := by
    simpa [prefixWord, tailWord_2437811, baseEnd_2437811] using wordTrace_append hprefix tailTrace_2437811
  have hstable : (prefixWord ++ tailWord_2437811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2437811).length < 2 ^ (prefixWord ++ tailWord_2437811).sum := by decide
  have hdescent : baseEnd_2437811 < baseStart_2437811 := by decide
  rcases family_descends (prefixWord ++ tailWord_2437811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2437831 : List Nat := [1, 1, 4, 1, 1, 1, 2, 4, 2, 6]
def baseStart_2437831 : Nat := 118140960795 + 2437831 * 2 ^ 59
def prefixEnd_2437831 : Nat := 4983230072969 + 3 ^ 40 * 2437831 * 2
def baseEnd_2437831 : Nat := 417259685810318902900375

theorem tailTrace_2437831 : CollatzResearch.WordTrace tailWord_2437831 prefixEnd_2437831 417259685810318902900375 := by
  unfold tailWord_2437831
  simp only [CollatzResearch.WordTrace]
  refine ⟨88915001231162110232721347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59276667487441406821814231 88915001231162110232721347)
  ·
    refine ⟨133372501846743165349082021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88915001231162110232721347 133372501846743165349082021)
    ·
      refine ⟨25007344096264343502952879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 133372501846743165349082021 25007344096264343502952879)
      ·
        refine ⟨37511016144396515254429319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25007344096264343502952879 37511016144396515254429319)
        ·
          refine ⟨56266524216594772881643979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37511016144396515254429319 56266524216594772881643979)
          ·
            refine ⟨84399786324892159322465969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56266524216594772881643979 84399786324892159322465969)
            ·
              refine ⟨63299839743669119491849477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84399786324892159322465969 63299839743669119491849477)
              ·
                refine ⟨11868719951937959904721777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63299839743669119491849477 11868719951937959904721777)
                ·
                  refine ⟨8901539963953469928541333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11868719951937959904721777 8901539963953469928541333)
                  ·
                    refine ⟨417259685810318902900375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8901539963953469928541333 417259685810318902900375)
                    ·
                      rfl

theorem cell23_2437831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 4, 2, 6].length) (baseStart_2437831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2437831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2437831 prefixEnd_2437831 := by exact prefixLift 2437831
  have htrace : WordTrace (prefixWord ++ tailWord_2437831) baseStart_2437831 baseEnd_2437831 := by
    simpa [prefixWord, tailWord_2437831, baseEnd_2437831] using wordTrace_append hprefix tailTrace_2437831
  have hstable : (prefixWord ++ tailWord_2437831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2437831).length < 2 ^ (prefixWord ++ tailWord_2437831).sum := by decide
  have hdescent : baseEnd_2437831 < baseStart_2437831 := by decide
  rcases family_descends (prefixWord ++ tailWord_2437831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2437841 : List Nat := [1, 2, 2, 1, 2, 3, 1, 2, 1, 3, 5]
def baseStart_2437841 : Nat := 118140960795 + 2437841 * 2 ^ 59
def prefixEnd_2437841 : Nat := 4983230072969 + 3 ^ 40 * 2437841 * 2
def baseEnd_2437841 : Nat := 1251784192237501669576079

theorem tailTrace_2437841 : CollatzResearch.WordTrace tailWord_2437841 prefixEnd_2437841 1251784192237501669576079 := by
  unfold tailWord_2437841
  simp only [CollatzResearch.WordTrace]
  refine ⟨88915365961125881940585377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59276910640750587960390251 88915365961125881940585377)
  ·
    refine ⟨66686524470844411455439033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88915365961125881940585377 66686524470844411455439033)
    ·
      refine ⟨50014893353133308591579275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66686524470844411455439033 50014893353133308591579275)
      ·
        refine ⟨75022340029699962887368913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50014893353133308591579275 75022340029699962887368913)
        ·
          refine ⟨56266755022274972165526685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75022340029699962887368913 56266755022274972165526685)
          ·
            refine ⟨21100033133353114562072507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56266755022274972165526685 21100033133353114562072507)
            ·
              refine ⟨31650049700029671843108761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21100033133353114562072507 31650049700029671843108761)
              ·
                refine ⟨23737537275022253882331571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31650049700029671843108761 23737537275022253882331571)
                ·
                  refine ⟨35606305912533380823497357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23737537275022253882331571 35606305912533380823497357)
                  ·
                    refine ⟨13352364717200017808811509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35606305912533380823497357 13352364717200017808811509)
                    ·
                      refine ⟨1251784192237501669576079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13352364717200017808811509 1251784192237501669576079)
                      ·
                        rfl

theorem cell23_2437841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 2, 1, 3, 5].length) (baseStart_2437841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2437841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2437841 prefixEnd_2437841 := by exact prefixLift 2437841
  have htrace : WordTrace (prefixWord ++ tailWord_2437841) baseStart_2437841 baseEnd_2437841 := by
    simpa [prefixWord, tailWord_2437841, baseEnd_2437841] using wordTrace_append hprefix tailTrace_2437841
  have hstable : (prefixWord ++ tailWord_2437841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2437841).length < 2 ^ (prefixWord ++ tailWord_2437841).sum := by decide
  have hdescent : baseEnd_2437841 < baseStart_2437841 := by decide
  rcases family_descends (prefixWord ++ tailWord_2437841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2437859 : List Nat := [1, 1, 1, 7, 1, 3, 1, 2, 1, 3, 2]
def baseStart_2437859 : Nat := 118140960795 + 2437859 * 2 ^ 59
def prefixEnd_2437859 : Nat := 4983230072969 + 3 ^ 40 * 2437859 * 2
def baseEnd_2437859 : Nat := 1251793434889282599150997

theorem tailTrace_2437859 : CollatzResearch.WordTrace tailWord_2437859 prefixEnd_2437859 1251793434889282599150997 := by
  unfold tailWord_2437859
  simp only [CollatzResearch.WordTrace]
  refine ⟨88916022475060671014740631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59277348316707114009827087 88916022475060671014740631)
  ·
    refine ⟨133374033712591006522110947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88916022475060671014740631 133374033712591006522110947)
    ·
      refine ⟨200061050568886509783166421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133374033712591006522110947 200061050568886509783166421)
      ·
        refine ⟨4688930872708277573042963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 200061050568886509783166421 4688930872708277573042963)
        ·
          refine ⟨7033396309062416359564445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4688930872708277573042963 7033396309062416359564445)
          ·
            refine ⟨2637523615898406134836667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7033396309062416359564445 2637523615898406134836667)
            ·
              refine ⟨3956285423847609202255001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2637523615898406134836667 3956285423847609202255001)
              ·
                refine ⟨2967214067885706901691251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3956285423847609202255001 2967214067885706901691251)
                ·
                  refine ⟨4450821101828560352536877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2967214067885706901691251 4450821101828560352536877)
                  ·
                    refine ⟨1669057913185710132201329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4450821101828560352536877 1669057913185710132201329)
                    ·
                      refine ⟨1251793434889282599150997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1669057913185710132201329 1251793434889282599150997)
                      ·
                        rfl

theorem cell23_2437859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 2, 1, 3, 2].length) (baseStart_2437859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2437859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2437859 prefixEnd_2437859 := by exact prefixLift 2437859
  have htrace : WordTrace (prefixWord ++ tailWord_2437859) baseStart_2437859 baseEnd_2437859 := by
    simpa [prefixWord, tailWord_2437859, baseEnd_2437859] using wordTrace_append hprefix tailTrace_2437859
  have hstable : (prefixWord ++ tailWord_2437859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2437859).length < 2 ^ (prefixWord ++ tailWord_2437859).sum := by decide
  have hdescent : baseEnd_2437859 < baseStart_2437859 := by decide
  rcases family_descends (prefixWord ++ tailWord_2437859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2437891 : List Nat := [1, 1, 1, 3, 2, 2, 1, 2, 3, 7]
def baseStart_2437891 : Nat := 118140960795 + 2437891 * 2 ^ 59
def prefixEnd_2437891 : Nat := 4983230072969 + 3 ^ 40 * 2437891 * 2
def baseEnd_2437891 : Nat := 417269955423408824650283

theorem tailTrace_2437891 : CollatzResearch.WordTrace tailWord_2437891 prefixEnd_2437891 417269955423408824650283 := by
  unfold tailWord_2437891
  simp only [CollatzResearch.WordTrace]
  refine ⟨88917189610944740479905527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59278126407296493653270351 88917189610944740479905527)
  ·
    refine ⟨133375784416417110719858291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88917189610944740479905527 133375784416417110719858291)
    ·
      refine ⟨200063676624625666079787437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133375784416417110719858291 200063676624625666079787437)
      ·
        refine ⟨75023878734234624779920289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 200063676624625666079787437 75023878734234624779920289)
        ·
          refine ⟨56267909050675968584940217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75023878734234624779920289 56267909050675968584940217)
          ·
            refine ⟨42200931788006976438705163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56267909050675968584940217 42200931788006976438705163)
            ·
              refine ⟨63301397682010464658057745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42200931788006976438705163 63301397682010464658057745)
              ·
                refine ⟨47476048261507848493543309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63301397682010464658057745 47476048261507848493543309)
                ·
                  refine ⟨17803518098065443185078741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47476048261507848493543309 17803518098065443185078741)
                  ·
                    refine ⟨417269955423408824650283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17803518098065443185078741 417269955423408824650283)
                    ·
                      rfl

theorem cell23_2437891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 3, 7].length) (baseStart_2437891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2437891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2437891 prefixEnd_2437891 := by exact prefixLift 2437891
  have htrace : WordTrace (prefixWord ++ tailWord_2437891) baseStart_2437891 baseEnd_2437891 := by
    simpa [prefixWord, tailWord_2437891, baseEnd_2437891] using wordTrace_append hprefix tailTrace_2437891
  have hstable : (prefixWord ++ tailWord_2437891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2437891).length < 2 ^ (prefixWord ++ tailWord_2437891).sum := by decide
  have hdescent : baseEnd_2437891 < baseStart_2437891 := by decide
  rcases family_descends (prefixWord ++ tailWord_2437891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2437955 : List Nat := [1, 1, 1, 3, 1, 4, 4, 1, 3, 4]
def baseStart_2437955 : Nat := 118140960795 + 2437955 * 2 ^ 59
def prefixEnd_2437955 : Nat := 4983230072969 + 3 ^ 40 * 2437955 * 2
def baseEnd_2437955 : Nat := 417280909677371407850185

theorem tailTrace_2437955 : CollatzResearch.WordTrace tailWord_2437955 prefixEnd_2437955 417280909677371407850185 := by
  unfold tailWord_2437955
  simp only [CollatzResearch.WordTrace]
  refine ⟨88919523882712879410235319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59279682588475252940156879 88919523882712879410235319)
  ·
    refine ⟨133379285824069319115352979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88919523882712879410235319 133379285824069319115352979)
    ·
      refine ⟨200068928736103978673029469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133379285824069319115352979 200068928736103978673029469)
      ·
        refine ⟨75025848276038992002386051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 200068928736103978673029469 75025848276038992002386051)
        ·
          refine ⟨112538772414058488003579077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75025848276038992002386051 112538772414058488003579077)
          ·
            refine ⟨21101019827635966500671077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 112538772414058488003579077 21101019827635966500671077)
            ·
              refine ⟨3956441217681743718875827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21101019827635966500671077 3956441217681743718875827)
              ·
                refine ⟨5934661826522615578313741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3956441217681743718875827 5934661826522615578313741)
                ·
                  refine ⟨2225498184945980841867653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5934661826522615578313741 2225498184945980841867653)
                  ·
                    refine ⟨417280909677371407850185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2225498184945980841867653 417280909677371407850185)
                    ·
                      rfl

theorem cell23_2437955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 1, 3, 4].length) (baseStart_2437955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2437955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2437955 prefixEnd_2437955 := by exact prefixLift 2437955
  have htrace : WordTrace (prefixWord ++ tailWord_2437955) baseStart_2437955 baseEnd_2437955 := by
    simpa [prefixWord, tailWord_2437955, baseEnd_2437955] using wordTrace_append hprefix tailTrace_2437955
  have hstable : (prefixWord ++ tailWord_2437955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2437955).length < 2 ^ (prefixWord ++ tailWord_2437955).sum := by decide
  have hdescent : baseEnd_2437955 < baseStart_2437955 := by decide
  rcases family_descends (prefixWord ++ tailWord_2437955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2437968 : List Nat := [2, 1, 1, 1, 1, 4, 2, 5, 6]
def baseStart_2437968 : Nat := 118140960795 + 2437968 * 2 ^ 59
def prefixEnd_2437968 : Nat := 4983230072969 + 3 ^ 40 * 2437968 * 2
def baseEnd_2437968 : Nat := 139094378253402519187555

theorem tailTrace_2437968 : CollatzResearch.WordTrace tailWord_2437968 prefixEnd_2437968 139094378253402519187555 := by
  unfold tailWord_2437968
  simp only [CollatzResearch.WordTrace]
  refine ⟨44459999015832891315229279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59279998687777188420305705 44459999015832891315229279)
  ·
    refine ⟨66689998523749336972843919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44459999015832891315229279 66689998523749336972843919)
    ·
      refine ⟨100034997785624005459265879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66689998523749336972843919 100034997785624005459265879)
      ·
        refine ⟨150052496678436008188898819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100034997785624005459265879 150052496678436008188898819)
        ·
          refine ⟨225078745017654012283348229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150052496678436008188898819 225078745017654012283348229)
          ·
            refine ⟨42202264690810127303127793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 225078745017654012283348229 42202264690810127303127793)
            ·
              refine ⟨31651698518107595477345845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42202264690810127303127793 31651698518107595477345845)
              ·
                refine ⟨2967346736072587076001173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31651698518107595477345845 2967346736072587076001173)
                ·
                  refine ⟨139094378253402519187555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2967346736072587076001173 139094378253402519187555)
                  ·
                    rfl

theorem cell23_2437968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 5, 6].length) (baseStart_2437968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2437968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2437968 prefixEnd_2437968 := by exact prefixLift 2437968
  have htrace : WordTrace (prefixWord ++ tailWord_2437968) baseStart_2437968 baseEnd_2437968 := by
    simpa [prefixWord, tailWord_2437968, baseEnd_2437968] using wordTrace_append hprefix tailTrace_2437968
  have hstable : (prefixWord ++ tailWord_2437968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2437968).length < 2 ^ (prefixWord ++ tailWord_2437968).sum := by decide
  have hdescent : baseEnd_2437968 < baseStart_2437968 := by decide
  rcases family_descends (prefixWord ++ tailWord_2437968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2437995 : List Nat := [1, 1, 1, 1, 2, 2, 4, 2, 5, 1, 3]
def baseStart_2437995 : Nat := 118140960795 + 2437995 * 2 ^ 59
def prefixEnd_2437995 : Nat := 4983230072969 + 3 ^ 40 * 2437995 * 2
def baseEnd_2437995 : Nat := 1251863268258294067050371

theorem tailTrace_2437995 : CollatzResearch.WordTrace tailWord_2437995 prefixEnd_2437995 1251863268258294067050371 := by
  unfold tailWord_2437995
  simp only [CollatzResearch.WordTrace]
  refine ⟨88920982802567966241691439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59280655201711977494460959 88920982802567966241691439)
  ·
    refine ⟨133381474203851949362537159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88920982802567966241691439 133381474203851949362537159)
    ·
      refine ⟨200072211305777924043805739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133381474203851949362537159 200072211305777924043805739)
      ·
        refine ⟨300108316958666886065708609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200072211305777924043805739 300108316958666886065708609)
        ·
          refine ⟨225081237719000164549281457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 300108316958666886065708609 225081237719000164549281457)
          ·
            refine ⟨168810928289250123411961093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 225081237719000164549281457 168810928289250123411961093)
            ·
              refine ⟨31652049054234398139742705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 168810928289250123411961093 31652049054234398139742705)
              ·
                refine ⟨23739036790675798604807029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31652049054234398139742705 23739036790675798604807029)
                ·
                  refine ⟨2225534699125856119200659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23739036790675798604807029 2225534699125856119200659)
                  ·
                    refine ⟨3338302048688784178800989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2225534699125856119200659 3338302048688784178800989)
                    ·
                      refine ⟨1251863268258294067050371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3338302048688784178800989 1251863268258294067050371)
                      ·
                        rfl

theorem cell23_2437995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 2, 5, 1, 3].length) (baseStart_2437995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2437995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2437995 prefixEnd_2437995 := by exact prefixLift 2437995
  have htrace : WordTrace (prefixWord ++ tailWord_2437995) baseStart_2437995 baseEnd_2437995 := by
    simpa [prefixWord, tailWord_2437995, baseEnd_2437995] using wordTrace_append hprefix tailTrace_2437995
  have hstable : (prefixWord ++ tailWord_2437995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2437995).length < 2 ^ (prefixWord ++ tailWord_2437995).sum := by decide
  have hdescent : baseEnd_2437995 < baseStart_2437995 := by decide
  rcases family_descends (prefixWord ++ tailWord_2437995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2438035 : List Nat := [1, 1, 1, 2, 1, 2, 1, 8, 1, 1, 4]
def baseStart_2438035 : Nat := 118140960795 + 2438035 * 2 ^ 59
def prefixEnd_2438035 : Nat := 4983230072969 + 3 ^ 40 * 2438035 * 2
def baseEnd_2438035 : Nat := 1251883807484473910550187

theorem tailTrace_2438035 : CollatzResearch.WordTrace tailWord_2438035 prefixEnd_2438035 1251883807484473910550187 := by
  unfold tailWord_2438035
  simp only [CollatzResearch.WordTrace]
  refine ⟨88922441722423053073147559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59281627814948702048765039 88922441722423053073147559)
  ·
    refine ⟨133383662583634579609721339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88922441722423053073147559 133383662583634579609721339)
    ·
      refine ⟨200075493875451869414582009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133383662583634579609721339 200075493875451869414582009)
      ·
        refine ⟨150056620406588902060936507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 200075493875451869414582009 150056620406588902060936507)
        ·
          refine ⟨225084930609883353091404761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150056620406588902060936507 225084930609883353091404761)
          ·
            refine ⟨168813697957412514818553571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 225084930609883353091404761 168813697957412514818553571)
            ·
              refine ⟨253220546936118772227830357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 168813697957412514818553571 253220546936118772227830357)
              ·
                refine ⟨2967428284407641862044887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 253220546936118772227830357 2967428284407641862044887)
                ·
                  refine ⟨4451142426611462793067331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2967428284407641862044887 4451142426611462793067331)
                  ·
                    refine ⟨6676713639917194189600997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4451142426611462793067331 6676713639917194189600997)
                    ·
                      refine ⟨1251883807484473910550187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6676713639917194189600997 1251883807484473910550187)
                      ·
                        rfl

theorem cell23_2438035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 8, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 8, 1, 1, 4].length) (baseStart_2438035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2438035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2438035 prefixEnd_2438035 := by exact prefixLift 2438035
  have htrace : WordTrace (prefixWord ++ tailWord_2438035) baseStart_2438035 baseEnd_2438035 := by
    simpa [prefixWord, tailWord_2438035, baseEnd_2438035] using wordTrace_append hprefix tailTrace_2438035
  have hstable : (prefixWord ++ tailWord_2438035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2438035).length < 2 ^ (prefixWord ++ tailWord_2438035).sum := by decide
  have hdescent : baseEnd_2438035 < baseStart_2438035 := by decide
  rcases family_descends (prefixWord ++ tailWord_2438035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2438045 : List Nat := [1, 4, 2, 1, 2, 1, 3, 2, 1, 6]
def baseStart_2438045 : Nat := 118140960795 + 2438045 * 2 ^ 59
def prefixEnd_2438045 : Nat := 4983230072969 + 3 ^ 40 * 2438045 * 2
def baseEnd_2438045 : Nat := 417296314097006290475047

theorem tailTrace_2438045 : CollatzResearch.WordTrace tailWord_2438045 prefixEnd_2438045 417296314097006290475047 := by
  unfold tailWord_2438045
  simp only [CollatzResearch.WordTrace]
  refine ⟨88922806452386824781011589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59281870968257883187341059 88922806452386824781011589)
  ·
    refine ⟨16673026209822529646439673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88922806452386824781011589 16673026209822529646439673)
    ·
      refine ⟨12504769657366897234829755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16673026209822529646439673 12504769657366897234829755)
      ·
        refine ⟨18757154486050345852244633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12504769657366897234829755 18757154486050345852244633)
        ·
          refine ⟨14067865864537759389183475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18757154486050345852244633 14067865864537759389183475)
          ·
            refine ⟨21101798796806639083775213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14067865864537759389183475 21101798796806639083775213)
            ·
              refine ⟨7913174548802489656415705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21101798796806639083775213 7913174548802489656415705)
              ·
                refine ⟨5934880911601867242311779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7913174548802489656415705 5934880911601867242311779)
                ·
                  refine ⟨8902321367402800863467669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5934880911601867242311779 8902321367402800863467669)
                  ·
                    refine ⟨417296314097006290475047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8902321367402800863467669 417296314097006290475047)
                    ·
                      rfl

theorem cell23_2438045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 2, 1, 6].length) (baseStart_2438045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2438045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2438045 prefixEnd_2438045 := by exact prefixLift 2438045
  have htrace : WordTrace (prefixWord ++ tailWord_2438045) baseStart_2438045 baseEnd_2438045 := by
    simpa [prefixWord, tailWord_2438045, baseEnd_2438045] using wordTrace_append hprefix tailTrace_2438045
  have hstable : (prefixWord ++ tailWord_2438045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2438045).length < 2 ^ (prefixWord ++ tailWord_2438045).sum := by decide
  have hdescent : baseEnd_2438045 < baseStart_2438045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2438045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2438049 : List Nat := [1, 2, 3, 4, 1, 2, 3, 1, 1, 5]
def baseStart_2438049 : Nat := 118140960795 + 2438049 * 2 ^ 59
def prefixEnd_2438049 : Nat := 4983230072969 + 3 ^ 40 * 2438049 * 2
def baseEnd_2438049 : Nat := 417296998737878951925041

theorem tailTrace_2438049 : CollatzResearch.WordTrace tailWord_2438049 prefixEnd_2438049 417296998737878951925041 := by
  unfold tailWord_2438049
  simp only [CollatzResearch.WordTrace]
  refine ⟨88922952344372333464157201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59281968229581555642771467 88922952344372333464157201)
  ·
    refine ⟨66692214258279250098117901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88922952344372333464157201 66692214258279250098117901)
    ·
      refine ⟨25009580346854718786794213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66692214258279250098117901 25009580346854718786794213)
      ·
        refine ⟨4689296315035259772523915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25009580346854718786794213 4689296315035259772523915)
        ·
          refine ⟨7033944472552889658785873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4689296315035259772523915 7033944472552889658785873)
          ·
            refine ⟨5275458354414667244089405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7033944472552889658785873 5275458354414667244089405)
            ·
              refine ⟨1978296882905500216533527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5275458354414667244089405 1978296882905500216533527)
              ·
                refine ⟨2967445324358250324800291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1978296882905500216533527 2967445324358250324800291)
                ·
                  refine ⟨4451167986537375487200437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2967445324358250324800291 4451167986537375487200437)
                  ·
                    refine ⟨417296998737878951925041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4451167986537375487200437 417296998737878951925041)
                    ·
                      rfl

theorem cell23_2438049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 3, 1, 1, 5].length) (baseStart_2438049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2438049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2438049 prefixEnd_2438049 := by exact prefixLift 2438049
  have htrace : WordTrace (prefixWord ++ tailWord_2438049) baseStart_2438049 baseEnd_2438049 := by
    simpa [prefixWord, tailWord_2438049, baseEnd_2438049] using wordTrace_append hprefix tailTrace_2438049
  have hstable : (prefixWord ++ tailWord_2438049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2438049).length < 2 ^ (prefixWord ++ tailWord_2438049).sum := by decide
  have hdescent : baseEnd_2438049 < baseStart_2438049 := by decide
  rcases family_descends (prefixWord ++ tailWord_2438049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2438069 : List Nat := [1, 3, 3, 2, 1, 1, 2, 3, 3, 2, 2]
def baseStart_2438069 : Nat := 118140960795 + 2438069 * 2 ^ 59
def prefixEnd_2438069 : Nat := 4983230072969 + 3 ^ 40 * 2438069 * 2
def baseEnd_2438069 : Nat := 1251901265826726777525031

theorem tailTrace_2438069 : CollatzResearch.WordTrace tailWord_2438069 prefixEnd_2438069 1251901265826726777525031 := by
  unfold tailWord_2438069
  simp only [CollatzResearch.WordTrace]
  refine ⟨88923681804299876879885261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59282454536199917919923507 88923681804299876879885261)
  ·
    refine ⟨33346380676612453829956973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88923681804299876879885261 33346380676612453829956973)
    ·
      refine ⟨12504892753729670186233865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33346380676612453829956973 12504892753729670186233865)
      ·
        refine ⟨9378669565297252639675399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12504892753729670186233865 9378669565297252639675399)
        ·
          refine ⟨14068004347945878959513099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9378669565297252639675399 14068004347945878959513099)
          ·
            refine ⟨21102006521918818439269649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14068004347945878959513099 21102006521918818439269649)
            ·
              refine ⟨15826504891439113829452237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21102006521918818439269649 15826504891439113829452237)
              ·
                refine ⟨5934939334289667686044589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15826504891439113829452237 5934939334289667686044589)
                ·
                  refine ⟨2225602250358625382266721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5934939334289667686044589 2225602250358625382266721)
                  ·
                    refine ⟨1669201687768969036700041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2225602250358625382266721 1669201687768969036700041)
                    ·
                      refine ⟨1251901265826726777525031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1669201687768969036700041 1251901265826726777525031)
                      ·
                        rfl

theorem cell23_2438069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 3, 3, 2, 2].length) (baseStart_2438069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2438069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2438069 prefixEnd_2438069 := by exact prefixLift 2438069
  have htrace : WordTrace (prefixWord ++ tailWord_2438069) baseStart_2438069 baseEnd_2438069 := by
    simpa [prefixWord, tailWord_2438069, baseEnd_2438069] using wordTrace_append hprefix tailTrace_2438069
  have hstable : (prefixWord ++ tailWord_2438069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2438069).length < 2 ^ (prefixWord ++ tailWord_2438069).sum := by decide
  have hdescent : baseEnd_2438069 < baseStart_2438069 := by decide
  rcases family_descends (prefixWord ++ tailWord_2438069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2438106 : List Nat := [3, 1, 1, 2, 4, 3, 2, 1, 1, 2, 3]
def baseStart_2438106 : Nat := 118140960795 + 2438106 * 2 ^ 59
def prefixEnd_2438106 : Nat := 4983230072969 + 3 ^ 40 * 2438106 * 2
def baseEnd_2438106 : Nat := 1251920264610943132762361

theorem tailTrace_2438106 : CollatzResearch.WordTrace tailWord_2438106 prefixEnd_2438106 1251920264610943132762361 := by
  unfold tailWord_2438106
  simp only [CollatzResearch.WordTrace]
  refine ⟨22231257826291458049745543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59283354203443888132654781 22231257826291458049745543)
  ·
    refine ⟨33346886739437187074618315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22231257826291458049745543 33346886739437187074618315)
    ·
      refine ⟨50020330109155780611927473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33346886739437187074618315 50020330109155780611927473)
      ·
        refine ⟨37515247581866835458945605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50020330109155780611927473 37515247581866835458945605)
        ·
          refine ⟨7034108921600031648552301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37515247581866835458945605 7034108921600031648552301)
          ·
            refine ⟨2637790845600011868207113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7034108921600031648552301 2637790845600011868207113)
            ·
              refine ⟨1978343134200008901155335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2637790845600011868207113 1978343134200008901155335)
              ·
                refine ⟨2967514701300013351733003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1978343134200008901155335 2967514701300013351733003)
                ·
                  refine ⟨4451272051950020027599505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2967514701300013351733003 4451272051950020027599505)
                  ·
                    refine ⟨3338454038962515020699629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4451272051950020027599505 3338454038962515020699629)
                    ·
                      refine ⟨1251920264610943132762361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3338454038962515020699629 1251920264610943132762361)
                      ·
                        rfl

theorem cell23_2438106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 2, 1, 1, 2, 3].length) (baseStart_2438106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2438106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2438106 prefixEnd_2438106 := by exact prefixLift 2438106
  have htrace : WordTrace (prefixWord ++ tailWord_2438106) baseStart_2438106 baseEnd_2438106 := by
    simpa [prefixWord, tailWord_2438106, baseEnd_2438106] using wordTrace_append hprefix tailTrace_2438106
  have hstable : (prefixWord ++ tailWord_2438106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2438106).length < 2 ^ (prefixWord ++ tailWord_2438106).sum := by decide
  have hdescent : baseEnd_2438106 < baseStart_2438106 := by decide
  rcases family_descends (prefixWord ++ tailWord_2438106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2438119 : List Nat := [1, 1, 5, 2, 2, 2, 1, 1, 4, 1, 3]
def baseStart_2438119 : Nat := 118140960795 + 2438119 * 2 ^ 59
def prefixEnd_2438119 : Nat := 4983230072969 + 3 ^ 40 * 2438119 * 2
def baseEnd_2438119 : Nat := 1251926939859451581899801

theorem tailTrace_2438119 : CollatzResearch.WordTrace tailWord_2438119 prefixEnd_2438119 1251926939859451581899801 := by
  unfold tailWord_2438119
  simp only [CollatzResearch.WordTrace]
  refine ⟨88925505454118735419205411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59283670302745823612803607 88925505454118735419205411)
  ·
    refine ⟨133388258181178103128808117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88925505454118735419205411 133388258181178103128808117)
    ·
      refine ⟨12505149204485447168325761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 133388258181178103128808117 12505149204485447168325761)
      ·
        refine ⟨9378861903364085376244321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12505149204485447168325761 9378861903364085376244321)
        ·
          refine ⟨7034146427523064032183241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9378861903364085376244321 7034146427523064032183241)
          ·
            refine ⟨5275609820642298024137431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7034146427523064032183241 5275609820642298024137431)
            ·
              refine ⟨7913414730963447036206147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5275609820642298024137431 7913414730963447036206147)
              ·
                refine ⟨11870122096445170554309221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7913414730963447036206147 11870122096445170554309221)
                ·
                  refine ⟨2225647893083469478932979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11870122096445170554309221 2225647893083469478932979)
                  ·
                    refine ⟨3338471839625204218399469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2225647893083469478932979 3338471839625204218399469)
                    ·
                      refine ⟨1251926939859451581899801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3338471839625204218399469 1251926939859451581899801)
                      ·
                        rfl

theorem cell23_2438119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 1, 4, 1, 3].length) (baseStart_2438119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2438119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2438119 prefixEnd_2438119 := by exact prefixLift 2438119
  have htrace : WordTrace (prefixWord ++ tailWord_2438119) baseStart_2438119 baseEnd_2438119 := by
    simpa [prefixWord, tailWord_2438119, baseEnd_2438119] using wordTrace_append hprefix tailTrace_2438119
  have hstable : (prefixWord ++ tailWord_2438119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2438119).length < 2 ^ (prefixWord ++ tailWord_2438119).sum := by decide
  have hdescent : baseEnd_2438119 < baseStart_2438119 := by decide
  rcases family_descends (prefixWord ++ tailWord_2438119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2438133 : List Nat := [1, 3, 5, 2, 2, 1, 1, 1, 1, 2, 4]
def baseStart_2438133 : Nat := 118140960795 + 2438133 * 2 ^ 59
def prefixEnd_2438133 : Nat := 4983230072969 + 3 ^ 40 * 2438133 * 2
def baseEnd_2438133 : Nat := 1251934128588614527124737

theorem tailTrace_2438133 : CollatzResearch.WordTrace tailWord_2438133 prefixEnd_2438133 1251934128588614527124737 := by
  unfold tailWord_2438133
  simp only [CollatzResearch.WordTrace]
  refine ⟨88926016076068015810215053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59284010717378677206810035 88926016076068015810215053)
  ·
    refine ⟨33347256028525505928830645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88926016076068015810215053 33347256028525505928830645)
    ·
      refine ⟨3126305252674266180827873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33347256028525505928830645 3126305252674266180827873)
      ·
        refine ⟨2344728939505699635620905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3126305252674266180827873 2344728939505699635620905)
        ·
          refine ⟨1758546704629274726715679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2344728939505699635620905 1758546704629274726715679)
          ·
            refine ⟨2637820056943912090073519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1758546704629274726715679 2637820056943912090073519)
            ·
              refine ⟨3956730085415868135110279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2637820056943912090073519 3956730085415868135110279)
              ·
                refine ⟨5935095128123802202665419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3956730085415868135110279 5935095128123802202665419)
                ·
                  refine ⟨8902642692185703303998129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5935095128123802202665419 8902642692185703303998129)
                  ·
                    refine ⟨6676982019139277477998597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8902642692185703303998129 6676982019139277477998597)
                    ·
                      refine ⟨1251934128588614527124737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6676982019139277477998597 1251934128588614527124737)
                      ·
                        rfl

theorem cell23_2438133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_2438133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2438133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2438133 prefixEnd_2438133 := by exact prefixLift 2438133
  have htrace : WordTrace (prefixWord ++ tailWord_2438133) baseStart_2438133 baseEnd_2438133 := by
    simpa [prefixWord, tailWord_2438133, baseEnd_2438133] using wordTrace_append hprefix tailTrace_2438133
  have hstable : (prefixWord ++ tailWord_2438133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2438133).length < 2 ^ (prefixWord ++ tailWord_2438133).sum := by decide
  have hdescent : baseEnd_2438133 < baseStart_2438133 := by decide
  rcases family_descends (prefixWord ++ tailWord_2438133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2438195 : List Nat := [1, 1, 1, 2, 4, 1, 1, 1, 6, 5]
def baseStart_2438195 : Nat := 118140960795 + 2438195 * 2 ^ 59
def prefixEnd_2438195 : Nat := 4983230072969 + 3 ^ 40 * 2438195 * 2
def baseEnd_2438195 : Nat := 417321988129731094849817

theorem tailTrace_2438195 : CollatzResearch.WordTrace tailWord_2438195 prefixEnd_2438195 417321988129731094849817 := by
  unfold tailWord_2438195
  simp only [CollatzResearch.WordTrace]
  refine ⟨88928277401843400398972039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59285518267895600265981359 88928277401843400398972039)
  ·
    refine ⟨133392416102765100598458059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88928277401843400398972039 133392416102765100598458059)
    ·
      refine ⟨200088624154147650897687089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133392416102765100598458059 200088624154147650897687089)
      ·
        refine ⟨150066468115610738173265317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 200088624154147650897687089 150066468115610738173265317)
        ·
          refine ⟨28137462771677013407487247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 150066468115610738173265317 28137462771677013407487247)
          ·
            refine ⟨42206194157515520111230871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28137462771677013407487247 42206194157515520111230871)
            ·
              refine ⟨63309291236273280166846307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42206194157515520111230871 63309291236273280166846307)
              ·
                refine ⟨94963936854409920250269461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63309291236273280166846307 94963936854409920250269461)
                ·
                  refine ⟨4451434540050465011731381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 94963936854409920250269461 4451434540050465011731381)
                  ·
                    refine ⟨417321988129731094849817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4451434540050465011731381 417321988129731094849817)
                    ·
                      rfl

theorem cell23_2438195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 6, 5].length) (baseStart_2438195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2438195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2438195 prefixEnd_2438195 := by exact prefixLift 2438195
  have htrace : WordTrace (prefixWord ++ tailWord_2438195) baseStart_2438195 baseEnd_2438195 := by
    simpa [prefixWord, tailWord_2438195, baseEnd_2438195] using wordTrace_append hprefix tailTrace_2438195
  have hstable : (prefixWord ++ tailWord_2438195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2438195).length < 2 ^ (prefixWord ++ tailWord_2438195).sum := by decide
  have hdescent : baseEnd_2438195 < baseStart_2438195 := by decide
  rcases family_descends (prefixWord ++ tailWord_2438195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2438232 : List Nat := [2, 1, 2, 2, 1, 3, 1, 4, 2, 1, 4]
def baseStart_2438232 : Nat := 118140960795 + 2438232 * 2 ^ 59
def prefixEnd_2438232 : Nat := 4983230072969 + 3 ^ 40 * 2438232 * 2
def baseEnd_2438232 : Nat := 1251984963173409639786781

theorem tailTrace_2438232 : CollatzResearch.WordTrace tailWord_2438232 prefixEnd_2438232 1251984963173409639786781 := by
  unfold tailWord_2438232
  simp only [CollatzResearch.WordTrace]
  refine ⟨44464813451354677859034475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59286417935139570478712633 44464813451354677859034475)
  ·
    refine ⟨66697220177032016788551713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44464813451354677859034475 66697220177032016788551713)
    ·
      refine ⟨50022915132774012591413785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66697220177032016788551713 50022915132774012591413785)
      ·
        refine ⟨37517186349580509443560339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50022915132774012591413785 37517186349580509443560339)
        ·
          refine ⟨56275779524370764165340509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37517186349580509443560339 56275779524370764165340509)
          ·
            refine ⟨21103417321639036562002691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56275779524370764165340509 21103417321639036562002691)
            ·
              refine ⟨31655125982458554843004037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21103417321639036562002691 31655125982458554843004037)
              ·
                refine ⟨5935336121710979033063257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31655125982458554843004037 5935336121710979033063257)
                ·
                  refine ⟨4451502091283234274797443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5935336121710979033063257 4451502091283234274797443)
                  ·
                    refine ⟨6677253136924851412196165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4451502091283234274797443 6677253136924851412196165)
                    ·
                      refine ⟨1251984963173409639786781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6677253136924851412196165 1251984963173409639786781)
                      ·
                        rfl

theorem cell23_2438232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 4, 2, 1, 4].length) (baseStart_2438232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2438232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2438232 prefixEnd_2438232 := by exact prefixLift 2438232
  have htrace : WordTrace (prefixWord ++ tailWord_2438232) baseStart_2438232 baseEnd_2438232 := by
    simpa [prefixWord, tailWord_2438232, baseEnd_2438232] using wordTrace_append hprefix tailTrace_2438232
  have hstable : (prefixWord ++ tailWord_2438232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2438232).length < 2 ^ (prefixWord ++ tailWord_2438232).sum := by decide
  have hdescent : baseEnd_2438232 < baseStart_2438232 := by decide
  rcases family_descends (prefixWord ++ tailWord_2438232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2438249 : List Nat := [1, 2, 1, 1, 1, 7, 1, 1, 2, 4, 2]
def baseStart_2438249 : Nat := 118140960795 + 2438249 * 2 ^ 59
def prefixEnd_2438249 : Nat := 4983230072969 + 3 ^ 40 * 2438249 * 2
def baseEnd_2438249 : Nat := 1251993692344536073274203

theorem tailTrace_2438249 : CollatzResearch.WordTrace tailWord_2438249 prefixEnd_2438249 1251993692344536073274203 := by
  unfold tailWord_2438249
  simp only [CollatzResearch.WordTrace]
  refine ⟨88930246943647767621437801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59286831295765178414291867 88930246943647767621437801)
  ·
    refine ⟨66697685207735825716078351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88930246943647767621437801 66697685207735825716078351)
    ·
      refine ⟨100046527811603738574117527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66697685207735825716078351 100046527811603738574117527)
      ·
        refine ⟨150069791717405607861176291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100046527811603738574117527 150069791717405607861176291)
        ·
          refine ⟨225104687576108411791764437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150069791717405607861176291 225104687576108411791764437)
          ·
            refine ⟨5275891115065040901369479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 225104687576108411791764437 5275891115065040901369479)
            ·
              refine ⟨7913836672597561352054219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5275891115065040901369479 7913836672597561352054219)
              ·
                refine ⟨11870755008896342028081329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7913836672597561352054219 11870755008896342028081329)
                ·
                  refine ⟨8903066256672256521060997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11870755008896342028081329 8903066256672256521060997)
                  ·
                    refine ⟨1669324923126048097698937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8903066256672256521060997 1669324923126048097698937)
                    ·
                      refine ⟨1251993692344536073274203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1669324923126048097698937 1251993692344536073274203)
                      ·
                        rfl

theorem cell23_2438249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 1, 2, 4, 2].length) (baseStart_2438249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2438249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2438249 prefixEnd_2438249 := by exact prefixLift 2438249
  have htrace : WordTrace (prefixWord ++ tailWord_2438249) baseStart_2438249 baseEnd_2438249 := by
    simpa [prefixWord, tailWord_2438249, baseEnd_2438249] using wordTrace_append hprefix tailTrace_2438249
  have hstable : (prefixWord ++ tailWord_2438249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2438249).length < 2 ^ (prefixWord ++ tailWord_2438249).sum := by decide
  have hdescent : baseEnd_2438249 < baseStart_2438249 := by decide
  rcases family_descends (prefixWord ++ tailWord_2438249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2438252 : List Nat := [2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 3]
def baseStart_2438252 : Nat := 118140960795 + 2438252 * 2 ^ 59
def prefixEnd_2438252 : Nat := 4983230072969 + 3 ^ 40 * 2438252 * 2
def baseEnd_2438252 : Nat := 1251995232786499561536689

theorem tailTrace_2438252 : CollatzResearch.WordTrace tailWord_2438252 prefixEnd_2438252 1251995232786499561536689 := by
  unfold tailWord_2438252
  simp only [CollatzResearch.WordTrace]
  refine ⟨44465178181318449566898505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59286904241757932755864673 44465178181318449566898505)
  ·
    refine ⟨33348883635988837175173879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44465178181318449566898505 33348883635988837175173879)
    ·
      refine ⟨50023325453983255762760819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33348883635988837175173879 50023325453983255762760819)
      ·
        refine ⟨75034988180974883644141229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50023325453983255762760819 75034988180974883644141229)
        ·
          refine ⟨28138120567865581366552961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75034988180974883644141229 28138120567865581366552961)
          ·
            refine ⟨21103590425899186024914721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28138120567865581366552961 21103590425899186024914721)
            ·
              refine ⟨15827692819424389518686041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21103590425899186024914721 15827692819424389518686041)
              ·
                refine ⟨11870769614568292139014531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15827692819424389518686041 11870769614568292139014531)
                ·
                  refine ⟨17806154421852438208521797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11870769614568292139014531 17806154421852438208521797)
                  ·
                    refine ⟨3338653954097332164097837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17806154421852438208521797 3338653954097332164097837)
                    ·
                      refine ⟨1251995232786499561536689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3338653954097332164097837 1251995232786499561536689)
                      ·
                        rfl

theorem cell23_2438252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 3].length) (baseStart_2438252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2438252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2438252 prefixEnd_2438252 := by exact prefixLift 2438252
  have htrace : WordTrace (prefixWord ++ tailWord_2438252) baseStart_2438252 baseEnd_2438252 := by
    simpa [prefixWord, tailWord_2438252, baseEnd_2438252] using wordTrace_append hprefix tailTrace_2438252
  have hstable : (prefixWord ++ tailWord_2438252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2438252).length < 2 ^ (prefixWord ++ tailWord_2438252).sum := by decide
  have hdescent : baseEnd_2438252 < baseStart_2438252 := by decide
  rcases family_descends (prefixWord ++ tailWord_2438252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2438276 : List Nat := [2, 3, 2, 1, 2, 2, 1, 5, 1, 4]
def baseStart_2438276 : Nat := 118140960795 + 2438276 * 2 ^ 59
def prefixEnd_2438276 : Nat := 4983230072969 + 3 ^ 40 * 2438276 * 2
def baseEnd_2438276 : Nat := 417335852107402489212193

theorem tailTrace_2438276 : CollatzResearch.WordTrace tailWord_2438276 prefixEnd_2438276 417335852107402489212193 := by
  unfold tailWord_2438276
  simp only [CollatzResearch.WordTrace]
  refine ⟨44465615857274975616335341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59287487809699967488447121 44465615857274975616335341)
  ·
    refine ⟨16674605946478115856125753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44465615857274975616335341 16674605946478115856125753)
    ·
      refine ⟨12505954459858586892094315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16674605946478115856125753 12505954459858586892094315)
      ·
        refine ⟨18758931689787880338141473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12505954459858586892094315 18758931689787880338141473)
        ·
          refine ⟨14069198767340910253606105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18758931689787880338141473 14069198767340910253606105)
          ·
            refine ⟨10551899075505682690204579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14069198767340910253606105 10551899075505682690204579)
            ·
              refine ⟨15827848613258524035306869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10551899075505682690204579 15827848613258524035306869)
              ·
                refine ⟨1483860807492986628310019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15827848613258524035306869 1483860807492986628310019)
                ·
                  refine ⟨2225791211239479942465029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1483860807492986628310019 2225791211239479942465029)
                  ·
                    refine ⟨417335852107402489212193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2225791211239479942465029 417335852107402489212193)
                    ·
                      rfl

theorem cell23_2438276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 5, 1, 4].length) (baseStart_2438276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2438276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2438276 prefixEnd_2438276 := by exact prefixLift 2438276
  have htrace : WordTrace (prefixWord ++ tailWord_2438276) baseStart_2438276 baseEnd_2438276 := by
    simpa [prefixWord, tailWord_2438276, baseEnd_2438276] using wordTrace_append hprefix tailTrace_2438276
  have hstable : (prefixWord ++ tailWord_2438276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2438276).length < 2 ^ (prefixWord ++ tailWord_2438276).sum := by decide
  have hdescent : baseEnd_2438276 < baseStart_2438276 := by decide
  rcases family_descends (prefixWord ++ tailWord_2438276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2438309 : List Nat := [1, 3, 1, 2, 1, 4, 1, 2, 1, 5, 2]
def baseStart_2438309 : Nat := 118140960795 + 2438309 * 2 ^ 59
def prefixEnd_2438309 : Nat := 4983230072969 + 3 ^ 40 * 2438309 * 2
def baseEnd_2438309 : Nat := 1252024501183805838523927

theorem tailTrace_2438309 : CollatzResearch.WordTrace tailWord_2438309 prefixEnd_2438309 1252024501183805838523927 := by
  unfold tailWord_2438309
  simp only [CollatzResearch.WordTrace]
  refine ⟨88932435323430397868621981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59288290215620265245747987 88932435323430397868621981)
  ·
    refine ⟨33349663246286399200733243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88932435323430397868621981 33349663246286399200733243)
    ·
      refine ⟨50024494869429598801099865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33349663246286399200733243 50024494869429598801099865)
      ·
        refine ⟨37518371152072199100824899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50024494869429598801099865 37518371152072199100824899)
        ·
          refine ⟨56277556728108298651237349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37518371152072199100824899 56277556728108298651237349)
          ·
            refine ⟨10552041886520305997107003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56277556728108298651237349 10552041886520305997107003)
            ·
              refine ⟨15828062829780458995660505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10552041886520305997107003 15828062829780458995660505)
              ·
                refine ⟨11871047122335344246745379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15828062829780458995660505 11871047122335344246745379)
                ·
                  refine ⟨17806570683503016370118069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11871047122335344246745379 17806570683503016370118069)
                  ·
                    refine ⟨1669366001578407784698569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17806570683503016370118069 1669366001578407784698569)
                    ·
                      refine ⟨1252024501183805838523927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1669366001578407784698569 1252024501183805838523927)
                      ·
                        rfl

theorem cell23_2438309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 2, 1, 5, 2].length) (baseStart_2438309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2438309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2438309 prefixEnd_2438309 := by exact prefixLift 2438309
  have htrace : WordTrace (prefixWord ++ tailWord_2438309) baseStart_2438309 baseEnd_2438309 := by
    simpa [prefixWord, tailWord_2438309, baseEnd_2438309] using wordTrace_append hprefix tailTrace_2438309
  have hstable : (prefixWord ++ tailWord_2438309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2438309).length < 2 ^ (prefixWord ++ tailWord_2438309).sum := by decide
  have hdescent : baseEnd_2438309 < baseStart_2438309 := by decide
  rcases family_descends (prefixWord ++ tailWord_2438309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2438333 : List Nat := [1, 4, 1, 2, 1, 1, 5, 3, 1, 1, 3]
def baseStart_2438333 : Nat := 118140960795 + 2438333 * 2 ^ 59
def prefixEnd_2438333 : Nat := 4983230072969 + 3 ^ 40 * 2438333 * 2
def baseEnd_2438333 : Nat := 1252036824719513744623817

theorem tailTrace_2438333 : CollatzResearch.WordTrace tailWord_2438333 prefixEnd_2438333 1252036824719513744623817 := by
  unfold tailWord_2438333
  simp only [CollatzResearch.WordTrace]
  refine ⟨88933310675343449967495653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59288873783562299978330435 88933310675343449967495653)
  ·
    refine ⟨16674995751626896868905435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88933310675343449967495653 16674995751626896868905435)
    ·
      refine ⟨25012493627440345303358153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16674995751626896868905435 25012493627440345303358153)
      ·
        refine ⟨18759370220580258977518615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25012493627440345303358153 18759370220580258977518615)
        ·
          refine ⟨28139055330870388466277923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18759370220580258977518615 28139055330870388466277923)
          ·
            refine ⟨42208582996305582699416885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28139055330870388466277923 42208582996305582699416885)
            ·
              refine ⟨3957054655903648378070333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42208582996305582699416885 3957054655903648378070333)
              ·
                refine ⟨1483895495963868141776375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3957054655903648378070333 1483895495963868141776375)
                ·
                  refine ⟨2225843243945802212664563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1483895495963868141776375 2225843243945802212664563)
                  ·
                    refine ⟨3338764865918703318996845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2225843243945802212664563 3338764865918703318996845)
                    ·
                      refine ⟨1252036824719513744623817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3338764865918703318996845 1252036824719513744623817)
                      ·
                        rfl

theorem cell23_2438333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 3, 1, 1, 3].length) (baseStart_2438333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2438333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2438333 prefixEnd_2438333 := by exact prefixLift 2438333
  have htrace : WordTrace (prefixWord ++ tailWord_2438333) baseStart_2438333 baseEnd_2438333 := by
    simpa [prefixWord, tailWord_2438333, baseEnd_2438333] using wordTrace_append hprefix tailTrace_2438333
  have hstable : (prefixWord ++ tailWord_2438333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2438333).length < 2 ^ (prefixWord ++ tailWord_2438333).sum := by decide
  have hdescent : baseEnd_2438333 < baseStart_2438333 := by decide
  rcases family_descends (prefixWord ++ tailWord_2438333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2438350 : List Nat := [4, 1, 1, 1, 6, 1, 1, 1, 3, 1, 3]
def baseStart_2438350 : Nat := 118140960795 + 2438350 * 2 ^ 59
def prefixEnd_2438350 : Nat := 4983230072969 + 3 ^ 40 * 2438350 * 2
def baseEnd_2438350 : Nat := 1252045553890640178111239

theorem tailTrace_2438350 : CollatzResearch.WordTrace tailWord_2438350 prefixEnd_2438350 1252045553890640178111239 := by
  unfold tailWord_2438350
  simp only [CollatzResearch.WordTrace]
  refine ⟨11116741339535232733858063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59289287144187907913909669 11116741339535232733858063)
  ·
    refine ⟨16675112009302849100787095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11116741339535232733858063 16675112009302849100787095)
    ·
      refine ⟨25012668013954273651180643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16675112009302849100787095 25012668013954273651180643)
      ·
        refine ⟨37519002020931410476770965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25012668013954273651180643 37519002020931410476770965)
        ·
          refine ⟨1758703219731159866098639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 37519002020931410476770965 1758703219731159866098639)
          ·
            refine ⟨2638054829596739799147959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1758703219731159866098639 2638054829596739799147959)
            ·
              refine ⟨3957082244395109698721939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2638054829596739799147959 3957082244395109698721939)
              ·
                refine ⟨5935623366592664548082909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3957082244395109698721939 5935623366592664548082909)
                ·
                  refine ⟨2225858762472249205531091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5935623366592664548082909 2225858762472249205531091)
                  ·
                    refine ⟨3338788143708373808296637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2225858762472249205531091 3338788143708373808296637)
                    ·
                      refine ⟨1252045553890640178111239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3338788143708373808296637 1252045553890640178111239)
                      ·
                        rfl

theorem cell23_2438350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 1, 3, 1, 3].length) (baseStart_2438350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2438350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2438350 prefixEnd_2438350 := by exact prefixLift 2438350
  have htrace : WordTrace (prefixWord ++ tailWord_2438350) baseStart_2438350 baseEnd_2438350 := by
    simpa [prefixWord, tailWord_2438350, baseEnd_2438350] using wordTrace_append hprefix tailTrace_2438350
  have hstable : (prefixWord ++ tailWord_2438350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2438350).length < 2 ^ (prefixWord ++ tailWord_2438350).sum := by decide
  have hdescent : baseEnd_2438350 < baseStart_2438350 := by decide
  rcases family_descends (prefixWord ++ tailWord_2438350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2438373 : List Nat := [1, 3, 1, 4, 3, 2, 1, 2, 1, 1, 4]
def baseStart_2438373 : Nat := 118140960795 + 2438373 * 2 ^ 59
def prefixEnd_2438373 : Nat := 4983230072969 + 3 ^ 40 * 2438373 * 2
def baseEnd_2438373 : Nat := 1252057363945693588123633

theorem tailTrace_2438373 : CollatzResearch.WordTrace tailWord_2438373 prefixEnd_2438373 1252057363945693588123633 := by
  unfold tailWord_2438373
  simp only [CollatzResearch.WordTrace]
  refine ⟨88934769595198536798951773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59289846396799024532634515 88934769595198536798951773)
  ·
    refine ⟨33350538598199451299606915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88934769595198536798951773 33350538598199451299606915)
    ·
      refine ⟨50025807897299176949410373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33350538598199451299606915 50025807897299176949410373)
      ·
        refine ⟨9379838980743595678014445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50025807897299176949410373 9379838980743595678014445)
        ·
          refine ⟨3517439617778848379255417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9379838980743595678014445 3517439617778848379255417)
          ·
            refine ⟨2638079713334136284441563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3517439617778848379255417 2638079713334136284441563)
            ·
              refine ⟨3957119570001204426662345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2638079713334136284441563 3957119570001204426662345)
              ·
                refine ⟨2967839677500903319996759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3957119570001204426662345 2967839677500903319996759)
                ·
                  refine ⟨4451759516251354979995139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2967839677500903319996759 4451759516251354979995139)
                  ·
                    refine ⟨6677639274377032469992709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4451759516251354979995139 6677639274377032469992709)
                    ·
                      refine ⟨1252057363945693588123633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6677639274377032469992709 1252057363945693588123633)
                      ·
                        rfl

theorem cell23_2438373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 2, 1, 1, 4].length) (baseStart_2438373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2438373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2438373 prefixEnd_2438373 := by exact prefixLift 2438373
  have htrace : WordTrace (prefixWord ++ tailWord_2438373) baseStart_2438373 baseEnd_2438373 := by
    simpa [prefixWord, tailWord_2438373, baseEnd_2438373] using wordTrace_append hprefix tailTrace_2438373
  have hstable : (prefixWord ++ tailWord_2438373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2438373).length < 2 ^ (prefixWord ++ tailWord_2438373).sum := by decide
  have hdescent : baseEnd_2438373 < baseStart_2438373 := by decide
  rcases family_descends (prefixWord ++ tailWord_2438373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2438386 : List Nat := [3, 2, 1, 3, 3, 1, 1, 2, 1, 2, 4]
def baseStart_2438386 : Nat := 118140960795 + 2438386 * 2 ^ 59
def prefixEnd_2438386 : Nat := 4983230072969 + 3 ^ 40 * 2438386 * 2
def baseEnd_2438386 : Nat := 1252064039194202037261073

theorem tailTrace_2438386 : CollatzResearch.WordTrace tailWord_2438386 prefixEnd_2438386 1252064039194202037261073 := by
  unfold tailWord_2438386
  simp only [CollatzResearch.WordTrace]
  refine ⟨22233810936037860004793753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59290162496100960012783341 22233810936037860004793753)
  ·
    refine ⟨16675358202028395003595315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22233810936037860004793753 16675358202028395003595315)
    ·
      refine ⟨25013037303042592505392973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16675358202028395003595315 25013037303042592505392973)
      ·
        refine ⟨9379888988640972189522365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25013037303042592505392973 9379888988640972189522365)
        ·
          refine ⟨3517458370740364571070887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9379888988640972189522365 3517458370740364571070887)
          ·
            refine ⟨5276187556110546856606331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3517458370740364571070887 5276187556110546856606331)
            ·
              refine ⟨7914281334165820284909497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5276187556110546856606331 7914281334165820284909497)
              ·
                refine ⟨5935711000624365213682123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7914281334165820284909497 5935711000624365213682123)
                ·
                  refine ⟨8903566500936547820523185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5935711000624365213682123 8903566500936547820523185)
                  ·
                    refine ⟨6677674875702410865392389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8903566500936547820523185 6677674875702410865392389)
                    ·
                      refine ⟨1252064039194202037261073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6677674875702410865392389 1252064039194202037261073)
                      ·
                        rfl

theorem cell23_2438386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 2, 1, 2, 4].length) (baseStart_2438386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2438386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2438386 prefixEnd_2438386 := by exact prefixLift 2438386
  have htrace : WordTrace (prefixWord ++ tailWord_2438386) baseStart_2438386 baseEnd_2438386 := by
    simpa [prefixWord, tailWord_2438386, baseEnd_2438386] using wordTrace_append hprefix tailTrace_2438386
  have hstable : (prefixWord ++ tailWord_2438386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2438386).length < 2 ^ (prefixWord ++ tailWord_2438386).sum := by decide
  have hdescent : baseEnd_2438386 < baseStart_2438386 := by decide
  rcases family_descends (prefixWord ++ tailWord_2438386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2438390 : List Nat := [5, 1, 1, 1, 1, 1, 1, 7, 1, 2, 2]
def baseStart_2438390 : Nat := 118140960795 + 2438390 * 2 ^ 59
def prefixEnd_2438390 : Nat := 4983230072969 + 3 ^ 40 * 2438390 * 2
def baseEnd_2438390 : Nat := 1252066093116820021611055

theorem tailTrace_2438390 : CollatzResearch.WordTrace tailWord_2438390 prefixEnd_2438390 1252066093116820021611055 := by
  unfold tailWord_2438390
  simp only [CollatzResearch.WordTrace]
  refine ⟨5558461852258559293895039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 59290259757424632468213749 5558461852258559293895039)
  ·
    refine ⟨8337692778387838940842559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5558461852258559293895039 8337692778387838940842559)
    ·
      refine ⟨12506539167581758411263839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8337692778387838940842559 12506539167581758411263839)
      ·
        refine ⟨18759808751372637616895759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12506539167581758411263839 18759808751372637616895759)
        ·
          refine ⟨28139713127058956425343639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18759808751372637616895759 28139713127058956425343639)
          ·
            refine ⟨42209569690588434638015459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28139713127058956425343639 42209569690588434638015459)
            ·
              refine ⟨63314354535882651957023189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42209569690588434638015459 63314354535882651957023189)
              ·
                refine ⟨1483930184434749655242731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 63314354535882651957023189 1483930184434749655242731)
                ·
                  refine ⟨2225895276652124482864097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1483930184434749655242731 2225895276652124482864097)
                  ·
                    refine ⟨1669421457489093362148073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2225895276652124482864097 1669421457489093362148073)
                    ·
                      refine ⟨1252066093116820021611055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1669421457489093362148073 1252066093116820021611055)
                      ·
                        rfl

theorem cell23_2438390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 7, 1, 2, 2].length) (baseStart_2438390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2438390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2438390 prefixEnd_2438390 := by exact prefixLift 2438390
  have htrace : WordTrace (prefixWord ++ tailWord_2438390) baseStart_2438390 baseEnd_2438390 := by
    simpa [prefixWord, tailWord_2438390, baseEnd_2438390] using wordTrace_append hprefix tailTrace_2438390
  have hstable : (prefixWord ++ tailWord_2438390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2438390).length < 2 ^ (prefixWord ++ tailWord_2438390).sum := by decide
  have hdescent : baseEnd_2438390 < baseStart_2438390 := by decide
  rcases family_descends (prefixWord ++ tailWord_2438390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2438450 : List Nat := [3, 2, 1, 1, 4, 1, 4, 1, 1, 3, 2]
def baseStart_2438450 : Nat := 118140960795 + 2438450 * 2 ^ 59
def prefixEnd_2438450 : Nat := 4983230072969 + 3 ^ 40 * 2438450 * 2
def baseEnd_2438450 : Nat := 1252096901956089786860779

theorem tailTrace_2438450 : CollatzResearch.WordTrace tailWord_2438450 prefixEnd_2438450 1252096901956089786860779 := by
  unfold tailWord_2438450
  simp only [CollatzResearch.WordTrace]
  refine ⟨22234394503979894737376201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59291718677279719299669869 22234394503979894737376201)
  ·
    refine ⟨16675795877984921053032151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22234394503979894737376201 16675795877984921053032151)
    ·
      refine ⟨25013693816977381579548227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16675795877984921053032151 25013693816977381579548227)
      ·
        refine ⟨37520540725466072369322341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25013693816977381579548227 37520540725466072369322341)
        ·
          refine ⟨7035101386024888569247939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37520540725466072369322341 7035101386024888569247939)
          ·
            refine ⟨10552652079037332853871909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7035101386024888569247939 10552652079037332853871909)
            ·
              refine ⟨1978622264819499910100983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10552652079037332853871909 1978622264819499910100983)
              ·
                refine ⟨2967933397229249865151475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1978622264819499910100983 2967933397229249865151475)
                ·
                  refine ⟨4451900095843874797727213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2967933397229249865151475 4451900095843874797727213)
                  ·
                    refine ⟨1669462535941453049147705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4451900095843874797727213 1669462535941453049147705)
                    ·
                      refine ⟨1252096901956089786860779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1669462535941453049147705 1252096901956089786860779)
                      ·
                        rfl

theorem cell23_2438450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 4, 1, 1, 3, 2].length) (baseStart_2438450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2438450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2438450 prefixEnd_2438450 := by exact prefixLift 2438450
  have htrace : WordTrace (prefixWord ++ tailWord_2438450) baseStart_2438450 baseEnd_2438450 := by
    simpa [prefixWord, tailWord_2438450, baseEnd_2438450] using wordTrace_append hprefix tailTrace_2438450
  have hstable : (prefixWord ++ tailWord_2438450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2438450).length < 2 ^ (prefixWord ++ tailWord_2438450).sum := by decide
  have hdescent : baseEnd_2438450 < baseStart_2438450 := by decide
  rcases family_descends (prefixWord ++ tailWord_2438450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2438457 : List Nat := [1, 2, 1, 6, 3, 1, 1, 2, 2, 1, 3]
def baseStart_2438457 : Nat := 118140960795 + 2438457 * 2 ^ 59
def prefixEnd_2438457 : Nat := 4983230072969 + 3 ^ 40 * 2438457 * 2
def baseEnd_2438457 : Nat := 1252100496320671259473247

theorem tailTrace_2438457 : CollatzResearch.WordTrace tailWord_2438457 prefixEnd_2438457 1252100496320671259473247 := by
  unfold tailWord_2438457
  simp only [CollatzResearch.WordTrace]
  refine ⟨88937833326894219145009625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59291888884596146096673083 88937833326894219145009625)
  ·
    refine ⟨66703374995170664358757219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88937833326894219145009625 66703374995170664358757219)
    ·
      refine ⟨100055062492755996538135829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66703374995170664358757219 100055062492755996538135829)
      ·
        refine ⟨4690081054347937337725117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 100055062492755996538135829 4690081054347937337725117)
        ·
          refine ⟨1758780395380476501646919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4690081054347937337725117 1758780395380476501646919)
          ·
            refine ⟨2638170593070714752470379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1758780395380476501646919 2638170593070714752470379)
            ·
              refine ⟨3957255889606072128705569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2638170593070714752470379 3957255889606072128705569)
              ·
                refine ⟨2967941917204554096529177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3957255889606072128705569 2967941917204554096529177)
                ·
                  refine ⟨2225956437903415572396883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2967941917204554096529177 2225956437903415572396883)
                  ·
                    refine ⟨3338934656855123358595325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2225956437903415572396883 3338934656855123358595325)
                    ·
                      refine ⟨1252100496320671259473247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3338934656855123358595325 1252100496320671259473247)
                      ·
                        rfl

theorem cell23_2438457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 2, 2, 1, 3].length) (baseStart_2438457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2438457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2438457 prefixEnd_2438457 := by exact prefixLift 2438457
  have htrace : WordTrace (prefixWord ++ tailWord_2438457) baseStart_2438457 baseEnd_2438457 := by
    simpa [prefixWord, tailWord_2438457, baseEnd_2438457] using wordTrace_append hprefix tailTrace_2438457
  have hstable : (prefixWord ++ tailWord_2438457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2438457).length < 2 ^ (prefixWord ++ tailWord_2438457).sum := by decide
  have hdescent : baseEnd_2438457 < baseStart_2438457 := by decide
  rcases family_descends (prefixWord ++ tailWord_2438457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2438463 : List Nat := [1, 1, 2, 2, 4, 3, 1, 1, 4, 2, 2]
def baseStart_2438463 : Nat := 118140960795 + 2438463 * 2 ^ 59
def prefixEnd_2438463 : Nat := 4983230072969 + 3 ^ 40 * 2438463 * 2
def baseEnd_2438463 : Nat := 1252103577204598235998219

theorem tailTrace_2438463 : CollatzResearch.WordTrace tailWord_2438463 prefixEnd_2438463 1252103577204598235998219 := by
  unfold tailWord_2438463
  simp only [CollatzResearch.WordTrace]
  refine ⟨88938052164872482169728043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59292034776581654779818695 88938052164872482169728043)
  ·
    refine ⟨133407078247308723254592065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88938052164872482169728043 133407078247308723254592065)
    ·
      refine ⟨100055308685481542440944049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133407078247308723254592065 100055308685481542440944049)
      ·
        refine ⟨75041481514111156830708037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100055308685481542440944049 75041481514111156830708037)
        ·
          refine ⟨14070277783895841905757757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75041481514111156830708037 14070277783895841905757757)
          ·
            refine ⟨5276354168960940714659159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14070277783895841905757757 5276354168960940714659159)
            ·
              refine ⟨7914531253441411071988739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5276354168960940714659159 7914531253441411071988739)
              ·
                refine ⟨11871796880162116607983109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7914531253441411071988739 11871796880162116607983109)
                ·
                  refine ⟨2225961915030396863996833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11871796880162116607983109 2225961915030396863996833)
                  ·
                    refine ⟨1669471436272797647997625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2225961915030396863996833 1669471436272797647997625)
                    ·
                      refine ⟨1252103577204598235998219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1669471436272797647997625 1252103577204598235998219)
                      ·
                        rfl

theorem cell23_2438463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 1, 4, 2, 2].length) (baseStart_2438463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2438463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2438463 prefixEnd_2438463 := by exact prefixLift 2438463
  have htrace : WordTrace (prefixWord ++ tailWord_2438463) baseStart_2438463 baseEnd_2438463 := by
    simpa [prefixWord, tailWord_2438463, baseEnd_2438463] using wordTrace_append hprefix tailTrace_2438463
  have hstable : (prefixWord ++ tailWord_2438463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2438463).length < 2 ^ (prefixWord ++ tailWord_2438463).sum := by decide
  have hdescent : baseEnd_2438463 < baseStart_2438463 := by decide
  rcases family_descends (prefixWord ++ tailWord_2438463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2438480 : List Nat := [2, 1, 1, 1, 1, 5, 5, 1, 2, 2, 2]
def baseStart_2438480 : Nat := 118140960795 + 2438480 * 2 ^ 59
def prefixEnd_2438480 : Nat := 4983230072969 + 3 ^ 40 * 2438480 * 2
def baseEnd_2438480 : Nat := 1252112306375724669485641

theorem tailTrace_2438480 : CollatzResearch.WordTrace tailWord_2438480 prefixEnd_2438480 1252112306375724669485641 := by
  unfold tailWord_2438480
  simp only [CollatzResearch.WordTrace]
  refine ⟨44469336102905447036548447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59292448137207262715397929 44469336102905447036548447)
  ·
    refine ⟨66704004154358170554822671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44469336102905447036548447 66704004154358170554822671)
    ·
      refine ⟨100056006231537255832234007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66704004154358170554822671 100056006231537255832234007)
      ·
        refine ⟨150084009347305883748351011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100056006231537255832234007 150084009347305883748351011)
        ·
          refine ⟨225126014020958825622526517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150084009347305883748351011 225126014020958825622526517)
          ·
            refine ⟨21105563814464889902111861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 225126014020958825622526517 21105563814464889902111861)
            ·
              refine ⟨1978646607606083428322987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21105563814464889902111861 1978646607606083428322987)
              ·
                refine ⟨2967969911409125142484481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1978646607606083428322987 2967969911409125142484481)
                ·
                  refine ⟨2225977433556843856863361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2967969911409125142484481 2225977433556843856863361)
                  ·
                    refine ⟨1669483075167632892647521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2225977433556843856863361 1669483075167632892647521)
                    ·
                      refine ⟨1252112306375724669485641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1669483075167632892647521 1252112306375724669485641)
                      ·
                        rfl

theorem cell23_2438480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 5, 1, 2, 2, 2].length) (baseStart_2438480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2438480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2438480 prefixEnd_2438480 := by exact prefixLift 2438480
  have htrace : WordTrace (prefixWord ++ tailWord_2438480) baseStart_2438480 baseEnd_2438480 := by
    simpa [prefixWord, tailWord_2438480, baseEnd_2438480] using wordTrace_append hprefix tailTrace_2438480
  have hstable : (prefixWord ++ tailWord_2438480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2438480).length < 2 ^ (prefixWord ++ tailWord_2438480).sum := by decide
  have hdescent : baseEnd_2438480 < baseStart_2438480 := by decide
  rcases family_descends (prefixWord ++ tailWord_2438480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2438499 : List Nat := [1, 1, 1, 5, 2, 2, 2, 1, 1, 7]
def baseStart_2438499 : Nat := 118140960795 + 2438499 * 2 ^ 59
def prefixEnd_2438499 : Nat := 4983230072969 + 3 ^ 40 * 2438499 * 2
def baseEnd_2438499 : Nat := 417374020836053365049351

theorem tailTrace_2438499 : CollatzResearch.WordTrace tailWord_2438499 prefixEnd_2438499 417374020836053365049351 := by
  unfold tailWord_2438499
  simp only [CollatzResearch.WordTrace]
  refine ⟨88939365192742060318038551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59292910128494706878692367 88939365192742060318038551)
  ·
    refine ⟨133409047789113090477057827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88939365192742060318038551 133409047789113090477057827)
    ·
      refine ⟨200113571683669635715586741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133409047789113090477057827 200113571683669635715586741)
      ·
        refine ⟨18760647345344028348336257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 200113571683669635715586741 18760647345344028348336257)
        ·
          refine ⟨14070485509008021261252193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18760647345344028348336257 14070485509008021261252193)
          ·
            refine ⟨10552864131756015945939145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14070485509008021261252193 10552864131756015945939145)
            ·
              refine ⟨7914648098817011959454359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10552864131756015945939145 7914648098817011959454359)
              ·
                refine ⟨11871972148225517939181539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7914648098817011959454359 11871972148225517939181539)
                ·
                  refine ⟨17807958222338276908772309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11871972148225517939181539 17807958222338276908772309)
                  ·
                    refine ⟨417374020836053365049351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17807958222338276908772309 417374020836053365049351)
                    ·
                      rfl

theorem cell23_2438499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 1, 1, 7].length) (baseStart_2438499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2438499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2438499 prefixEnd_2438499 := by exact prefixLift 2438499
  have htrace : WordTrace (prefixWord ++ tailWord_2438499) baseStart_2438499 baseEnd_2438499 := by
    simpa [prefixWord, tailWord_2438499, baseEnd_2438499] using wordTrace_append hprefix tailTrace_2438499
  have hstable : (prefixWord ++ tailWord_2438499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2438499).length < 2 ^ (prefixWord ++ tailWord_2438499).sum := by decide
  have hdescent : baseEnd_2438499 < baseStart_2438499 := by decide
  rcases family_descends (prefixWord ++ tailWord_2438499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2438549 : List Nat := [1, 3, 2, 1, 1, 2, 2, 1, 2, 4, 4]
def baseStart_2438549 : Nat := 118140960795 + 2438549 * 2 ^ 59
def prefixEnd_2438549 : Nat := 4983230072969 + 3 ^ 40 * 2438549 * 2
def baseEnd_2438549 : Nat := 1252147736540884899522823

theorem tailTrace_2438549 : CollatzResearch.WordTrace tailWord_2438549 prefixEnd_2438549 1252147736540884899522823 := by
  unfold tailWord_2438549
  simp only [CollatzResearch.WordTrace]
  refine ⟨88941188842560918857358701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59294125895040612571572467 88941188842560918857358701)
  ·
    refine ⟨33352945815960344571509513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88941188842560918857358701 33352945815960344571509513)
    ·
      refine ⟨25014709361970258428632135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33352945815960344571509513 25014709361970258428632135)
      ·
        refine ⟨37522064042955387642948203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25014709361970258428632135 37522064042955387642948203)
        ·
          refine ⟨56283096064433081464422305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37522064042955387642948203 56283096064433081464422305)
          ·
            refine ⟨42212322048324811098316729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56283096064433081464422305 42212322048324811098316729)
            ·
              refine ⟨31659241536243608323737547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42212322048324811098316729 31659241536243608323737547)
              ·
                refine ⟨47488862304365412485606321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31659241536243608323737547 47488862304365412485606321)
                ·
                  refine ⟨35616646728274059364204741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47488862304365412485606321 35616646728274059364204741)
                  ·
                    refine ⟨6678121261551386130788389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35616646728274059364204741 6678121261551386130788389)
                    ·
                      refine ⟨1252147736540884899522823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6678121261551386130788389 1252147736540884899522823)
                      ·
                        rfl

theorem cell23_2438549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 2, 4, 4].length) (baseStart_2438549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2438549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2438549 prefixEnd_2438549 := by exact prefixLift 2438549
  have htrace : WordTrace (prefixWord ++ tailWord_2438549) baseStart_2438549 baseEnd_2438549 := by
    simpa [prefixWord, tailWord_2438549, baseEnd_2438549] using wordTrace_append hprefix tailTrace_2438549
  have hstable : (prefixWord ++ tailWord_2438549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2438549).length < 2 ^ (prefixWord ++ tailWord_2438549).sum := by decide
  have hdescent : baseEnd_2438549 < baseStart_2438549 := by decide
  rcases family_descends (prefixWord ++ tailWord_2438549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2438563 : List Nat := [1, 1, 1, 4, 1, 3, 2, 5, 1, 4]
def baseStart_2438563 : Nat := 118140960795 + 2438563 * 2 ^ 59
def prefixEnd_2438563 : Nat := 4983230072969 + 3 ^ 40 * 2438563 * 2
def baseEnd_2438563 : Nat := 417384975090015948249253

theorem tailTrace_2438563 : CollatzResearch.WordTrace tailWord_2438563 prefixEnd_2438563 417384975090015948249253 := by
  unfold tailWord_2438563
  simp only [CollatzResearch.WordTrace]
  refine ⟨88941699464510199248368343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59294466309673466165578895 88941699464510199248368343)
  ·
    refine ⟨133412549196765298872552515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88941699464510199248368343 133412549196765298872552515)
    ·
      refine ⟨200118823795147948308828773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133412549196765298872552515 200118823795147948308828773)
      ·
        refine ⟨37522279461590240307905395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 200118823795147948308828773 37522279461590240307905395)
        ·
          refine ⟨56283419192385360461858093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37522279461590240307905395 56283419192385360461858093)
          ·
            refine ⟨21106282197144510173196785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56283419192385360461858093 21106282197144510173196785)
            ·
              refine ⟨15829711647858382629897589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21106282197144510173196785 15829711647858382629897589)
              ·
                refine ⟨1484035466986723371552899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15829711647858382629897589 1484035466986723371552899)
                ·
                  refine ⟨2226053200480085057329349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1484035466986723371552899 2226053200480085057329349)
                  ·
                    refine ⟨417384975090015948249253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2226053200480085057329349 417384975090015948249253)
                    ·
                      rfl

theorem cell23_2438563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 5, 1, 4].length) (baseStart_2438563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2438563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2438563 prefixEnd_2438563 := by exact prefixLift 2438563
  have htrace : WordTrace (prefixWord ++ tailWord_2438563) baseStart_2438563 baseEnd_2438563 := by
    simpa [prefixWord, tailWord_2438563, baseEnd_2438563] using wordTrace_append hprefix tailTrace_2438563
  have hstable : (prefixWord ++ tailWord_2438563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2438563).length < 2 ^ (prefixWord ++ tailWord_2438563).sum := by decide
  have hdescent : baseEnd_2438563 < baseStart_2438563 := by decide
  rcases family_descends (prefixWord ++ tailWord_2438563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2438599 : List Nat := [1, 1, 4, 1, 1, 3, 1, 1, 2, 1, 7]
def baseStart_2438599 : Nat := 118140960795 + 2438599 * 2 ^ 59
def prefixEnd_2438599 : Nat := 4983230072969 + 3 ^ 40 * 2438599 * 2
def baseEnd_2438599 : Nat := 1252173410573609703897593

theorem tailTrace_2438599 : CollatzResearch.WordTrace tailWord_2438599 prefixEnd_2438599 1252173410573609703897593 := by
  unfold tailWord_2438599
  simp only [CollatzResearch.WordTrace]
  refine ⟨88943012492379777396678851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59295341661586518264452567 88943012492379777396678851)
  ·
    refine ⟨133414518738569666095018277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88943012492379777396678851 133414518738569666095018277)
    ·
      refine ⟨25015222263481812392815927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 133414518738569666095018277 25015222263481812392815927)
      ·
        refine ⟨37522833395222718589223891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25015222263481812392815927 37522833395222718589223891)
        ·
          refine ⟨56284250092834077883835837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37522833395222718589223891 56284250092834077883835837)
          ·
            refine ⟨21106593784812779206438439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56284250092834077883835837 21106593784812779206438439)
            ·
              refine ⟨31659890677219168809657659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21106593784812779206438439 31659890677219168809657659)
              ·
                refine ⟨47489836015828753214486489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31659890677219168809657659 47489836015828753214486489)
                ·
                  refine ⟨35617377011871564910864867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47489836015828753214486489 35617377011871564910864867)
                  ·
                    refine ⟨53426065517807347366297301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35617377011871564910864867 53426065517807347366297301)
                    ·
                      refine ⟨1252173410573609703897593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 53426065517807347366297301 1252173410573609703897593)
                      ·
                        rfl

theorem cell23_2438599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 2, 1, 7].length) (baseStart_2438599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2438599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2438599 prefixEnd_2438599 := by exact prefixLift 2438599
  have htrace : WordTrace (prefixWord ++ tailWord_2438599) baseStart_2438599 baseEnd_2438599 := by
    simpa [prefixWord, tailWord_2438599, baseEnd_2438599] using wordTrace_append hprefix tailTrace_2438599
  have hstable : (prefixWord ++ tailWord_2438599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2438599).length < 2 ^ (prefixWord ++ tailWord_2438599).sum := by decide
  have hdescent : baseEnd_2438599 < baseStart_2438599 := by decide
  rcases family_descends (prefixWord ++ tailWord_2438599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2438606 : List Nat := [4, 1, 1, 1, 2, 1, 4, 1, 3, 5]
def baseStart_2438606 : Nat := 118140960795 + 2438606 * 2 ^ 59
def prefixEnd_2438606 : Nat := 4983230072969 + 3 ^ 40 * 2438606 * 2
def baseEnd_2438606 : Nat := 417392334979397058836687

theorem tailTrace_2438606 : CollatzResearch.WordTrace tailWord_2438606 prefixEnd_2438606 417392334979397058836687 := by
  unfold tailWord_2438606
  simp only [CollatzResearch.WordTrace]
  refine ⟨11117908475419302199022959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59295511868902945061455781 11117908475419302199022959)
  ·
    refine ⟨16676862713128953298534439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11117908475419302199022959 16676862713128953298534439)
    ·
      refine ⟨25015294069693429947801659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16676862713128953298534439 25015294069693429947801659)
      ·
        refine ⟨37522941104540144921702489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25015294069693429947801659 37522941104540144921702489)
        ·
          refine ⟨28142205828405108691276867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37522941104540144921702489 28142205828405108691276867)
          ·
            refine ⟨42213308742607663036915301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28142205828405108691276867 42213308742607663036915301)
            ·
              refine ⟨7914995389238936819421619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42213308742607663036915301 7914995389238936819421619)
              ·
                refine ⟨11872493083858405229132429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7914995389238936819421619 11872493083858405229132429)
                ·
                  refine ⟨4452184906446901960924661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11872493083858405229132429 4452184906446901960924661)
                  ·
                    refine ⟨417392334979397058836687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4452184906446901960924661 417392334979397058836687)
                    ·
                      rfl

theorem cell23_2438606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 1, 3, 5].length) (baseStart_2438606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2438606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2438606 prefixEnd_2438606 := by exact prefixLift 2438606
  have htrace : WordTrace (prefixWord ++ tailWord_2438606) baseStart_2438606 baseEnd_2438606 := by
    simpa [prefixWord, tailWord_2438606, baseEnd_2438606] using wordTrace_append hprefix tailTrace_2438606
  have hstable : (prefixWord ++ tailWord_2438606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2438606).length < 2 ^ (prefixWord ++ tailWord_2438606).sum := by decide
  have hdescent : baseEnd_2438606 < baseStart_2438606 := by decide
  rcases family_descends (prefixWord ++ tailWord_2438606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2438613 : List Nat := [1, 3, 2, 3, 1, 1, 3, 1, 1, 5, 2]
def baseStart_2438613 : Nat := 118140960795 + 2438613 * 2 ^ 59
def prefixEnd_2438613 : Nat := 4983230072969 + 3 ^ 40 * 2438613 * 2
def baseEnd_2438613 : Nat := 1252180599302772649122529

theorem tailTrace_2438613 : CollatzResearch.WordTrace tailWord_2438613 prefixEnd_2438613 1252180599302772649122529 := by
  unfold tailWord_2438613
  simp only [CollatzResearch.WordTrace]
  refine ⟨88943523114329057787688493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59295682076219371858458995 88943523114329057787688493)
  ·
    refine ⟨33353821167873396670383185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88943523114329057787688493 33353821167873396670383185)
    ·
      refine ⟨25015365875905047502787389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33353821167873396670383185 25015365875905047502787389)
      ·
        refine ⟨9380762203464392813545271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25015365875905047502787389 9380762203464392813545271)
        ·
          refine ⟨14071143305196589220317907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9380762203464392813545271 14071143305196589220317907)
          ·
            refine ⟨21106714957794883830476861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14071143305196589220317907 21106714957794883830476861)
            ·
              refine ⟨7915018109173081436428823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21106714957794883830476861 7915018109173081436428823)
              ·
                refine ⟨11872527163759622154643235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7915018109173081436428823 11872527163759622154643235)
                ·
                  refine ⟨17808790745639433231964853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11872527163759622154643235 17808790745639433231964853)
                  ·
                    refine ⟨1669574132403696865496705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17808790745639433231964853 1669574132403696865496705)
                    ·
                      refine ⟨1252180599302772649122529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1669574132403696865496705 1252180599302772649122529)
                      ·
                        rfl

theorem cell23_2438613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 1, 1, 5, 2].length) (baseStart_2438613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2438613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2438613 prefixEnd_2438613 := by exact prefixLift 2438613
  have htrace : WordTrace (prefixWord ++ tailWord_2438613) baseStart_2438613 baseEnd_2438613 := by
    simpa [prefixWord, tailWord_2438613, baseEnd_2438613] using wordTrace_append hprefix tailTrace_2438613
  have hstable : (prefixWord ++ tailWord_2438613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2438613).length < 2 ^ (prefixWord ++ tailWord_2438613).sum := by decide
  have hdescent : baseEnd_2438613 < baseStart_2438613 := by decide
  rcases family_descends (prefixWord ++ tailWord_2438613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2438637 : List Nat := [1, 5, 1, 3, 2, 1, 2, 1, 3, 1, 3]
def baseStart_2438637 : Nat := 118140960795 + 2438637 * 2 ^ 59
def prefixEnd_2438637 : Nat := 4983230072969 + 3 ^ 40 * 2438637 * 2
def baseEnd_2438637 : Nat := 1252192922838480555222419

theorem tailTrace_2438637 : CollatzResearch.WordTrace tailWord_2438637 prefixEnd_2438637 1252192922838480555222419 := by
  unfold tailWord_2438637
  simp only [CollatzResearch.WordTrace]
  refine ⟨88944398466242109886562165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59296265644161406591041443 88944398466242109886562165)
  ·
    refine ⟨8338537356210197801865203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 88944398466242109886562165 8338537356210197801865203)
    ·
      refine ⟨12507806034315296702797805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8338537356210197801865203 12507806034315296702797805)
      ·
        refine ⟨4690427262868236263549177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12507806034315296702797805 4690427262868236263549177)
        ·
          refine ⟨3517820447151177197661883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4690427262868236263549177 3517820447151177197661883)
          ·
            refine ⟨5276730670726765796492825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3517820447151177197661883 5276730670726765796492825)
            ·
              refine ⟨3957548003045074347369619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5276730670726765796492825 3957548003045074347369619)
              ·
                refine ⟨5936322004567611521054429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3957548003045074347369619 5936322004567611521054429)
                ·
                  refine ⟨2226120751712854320395411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5936322004567611521054429 2226120751712854320395411)
                  ·
                    refine ⟨3339181127569281480593117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2226120751712854320395411 3339181127569281480593117)
                    ·
                      refine ⟨1252192922838480555222419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3339181127569281480593117 1252192922838480555222419)
                      ·
                        rfl

theorem cell23_2438637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_2438637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2438637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2438637 prefixEnd_2438637 := by exact prefixLift 2438637
  have htrace : WordTrace (prefixWord ++ tailWord_2438637) baseStart_2438637 baseEnd_2438637 := by
    simpa [prefixWord, tailWord_2438637, baseEnd_2438637] using wordTrace_append hprefix tailTrace_2438637
  have hstable : (prefixWord ++ tailWord_2438637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2438637).length < 2 ^ (prefixWord ++ tailWord_2438637).sum := by decide
  have hdescent : baseEnd_2438637 < baseStart_2438637 := by decide
  rcases family_descends (prefixWord ++ tailWord_2438637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2438649 : List Nat := [1, 2, 1, 3, 1, 2, 1, 12]
def baseStart_2438649 : Nat := 118140960795 + 2438649 * 2 ^ 59
def prefixEnd_2438649 : Nat := 4983230072969 + 3 ^ 40 * 2438649 * 2
def baseEnd_2438649 : Nat := 46377743874308685491569

theorem tailTrace_2438649 : CollatzResearch.WordTrace tailWord_2438649 prefixEnd_2438649 46377743874308685491569 := by
  unfold tailWord_2438649
  simp only [CollatzResearch.WordTrace]
  refine ⟨88944836142198635935999001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59296557428132423957332667 88944836142198635935999001)
  ·
    refine ⟨66708627106648976951999251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88944836142198635935999001 66708627106648976951999251)
    ·
      refine ⟨100062940659973465427998877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66708627106648976951999251 100062940659973465427998877)
      ·
        refine ⟨37523602747490049535499579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100062940659973465427998877 37523602747490049535499579)
        ·
          refine ⟨56285404121235074303249369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37523602747490049535499579 56285404121235074303249369)
          ·
            refine ⟨42214053090926305727437027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56285404121235074303249369 42214053090926305727437027)
            ·
              refine ⟨63321079636389458591155541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42214053090926305727437027 63321079636389458591155541)
              ·
                refine ⟨46377743874308685491569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 63321079636389458591155541 46377743874308685491569)
                ·
                  rfl

theorem cell23_2438649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 12].length) (baseStart_2438649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2438649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2438649 prefixEnd_2438649 := by exact prefixLift 2438649
  have htrace : WordTrace (prefixWord ++ tailWord_2438649) baseStart_2438649 baseEnd_2438649 := by
    simpa [prefixWord, tailWord_2438649, baseEnd_2438649] using wordTrace_append hprefix tailTrace_2438649
  have hstable : (prefixWord ++ tailWord_2438649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2438649).length < 2 ^ (prefixWord ++ tailWord_2438649).sum := by decide
  have hdescent : baseEnd_2438649 < baseStart_2438649 := by decide
  rcases family_descends (prefixWord ++ tailWord_2438649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2438653 : List Nat := [1, 4, 1, 1, 1, 6, 1, 1, 1, 6]
def baseStart_2438653 : Nat := 118140960795 + 2438653 * 2 ^ 59
def prefixEnd_2438653 : Nat := 4983230072969 + 3 ^ 40 * 2438653 * 2
def baseEnd_2438653 : Nat := 417400379509650830874115

theorem tailTrace_2438653 : CollatzResearch.WordTrace tailWord_2438653 prefixEnd_2438653 417400379509650830874115 := by
  unfold tailWord_2438653
  simp only [CollatzResearch.WordTrace]
  refine ⟨88944982034184144619144613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59296654689456096412763075 88944982034184144619144613)
  ·
    refine ⟨16677184131409527116089615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88944982034184144619144613 16677184131409527116089615)
    ·
      refine ⟨25015776197114290674134423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16677184131409527116089615 25015776197114290674134423)
      ·
        refine ⟨37523664295671436011201635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25015776197114290674134423 37523664295671436011201635)
        ·
          refine ⟨56285496443507154016802453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37523664295671436011201635 56285496443507154016802453)
          ·
            refine ⟨2638382645789397844537615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 56285496443507154016802453 2638382645789397844537615)
            ·
              refine ⟨3957573968684096766806423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2638382645789397844537615 3957573968684096766806423)
              ·
                refine ⟨5936360953026145150209635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3957573968684096766806423 5936360953026145150209635)
                ·
                  refine ⟨8904541429539217725314453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5936360953026145150209635 8904541429539217725314453)
                  ·
                    refine ⟨417400379509650830874115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8904541429539217725314453 417400379509650830874115)
                    ·
                      rfl

theorem cell23_2438653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 1, 1, 6].length) (baseStart_2438653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2438653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2438653 prefixEnd_2438653 := by exact prefixLift 2438653
  have htrace : WordTrace (prefixWord ++ tailWord_2438653) baseStart_2438653 baseEnd_2438653 := by
    simpa [prefixWord, tailWord_2438653, baseEnd_2438653] using wordTrace_append hprefix tailTrace_2438653
  have hstable : (prefixWord ++ tailWord_2438653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2438653).length < 2 ^ (prefixWord ++ tailWord_2438653).sum := by decide
  have hdescent : baseEnd_2438653 < baseStart_2438653 := by decide
  rcases family_descends (prefixWord ++ tailWord_2438653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2438666 : List Nat := [3, 1, 2, 2, 2, 3, 1, 9]
def baseStart_2438666 : Nat := 118140960795 + 2438666 * 2 ^ 59
def prefixEnd_2438666 : Nat := 4983230072969 + 3 ^ 40 * 2438666 * 2
def baseEnd_2438666 : Nat := 46378067176942997842955

theorem tailTrace_2438666 : CollatzResearch.WordTrace tailWord_2438666 prefixEnd_2438666 46378067176942997842955 := by
  unfold tailWord_2438666
  simp only [CollatzResearch.WordTrace]
  refine ⟨22236364045784261959841963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59296970788758031892911901 22236364045784261959841963)
  ·
    refine ⟨33354546068676392939762945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22236364045784261959841963 33354546068676392939762945)
    ·
      refine ⟨25015909551507294704822209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33354546068676392939762945 25015909551507294704822209)
      ·
        refine ⟨18761932163630471028616657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25015909551507294704822209 18761932163630471028616657)
        ·
          refine ⟨14071449122722853271462493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18761932163630471028616657 14071449122722853271462493)
          ·
            refine ⟨5276793421021069976798435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14071449122722853271462493 5276793421021069976798435)
            ·
              refine ⟨7915190131531604965197653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5276793421021069976798435 7915190131531604965197653)
              ·
                refine ⟨46378067176942997842955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7915190131531604965197653 46378067176942997842955)
                ·
                  rfl

theorem cell23_2438666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 9].length) (baseStart_2438666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2438666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2438666 prefixEnd_2438666 := by exact prefixLift 2438666
  have htrace : WordTrace (prefixWord ++ tailWord_2438666) baseStart_2438666 baseEnd_2438666 := by
    simpa [prefixWord, tailWord_2438666, baseEnd_2438666] using wordTrace_append hprefix tailTrace_2438666
  have hstable : (prefixWord ++ tailWord_2438666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2438666).length < 2 ^ (prefixWord ++ tailWord_2438666).sum := by decide
  have hdescent : baseEnd_2438666 < baseStart_2438666 := by decide
  rcases family_descends (prefixWord ++ tailWord_2438666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2438736 : List Nat := [2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 5]
def baseStart_2438736 : Nat := 118140960795 + 2438736 * 2 ^ 59
def prefixEnd_2438736 : Nat := 4983230072969 + 3 ^ 40 * 2438736 * 2
def baseEnd_2438736 : Nat := 1252243757423275667884463

theorem tailTrace_2438736 : CollatzResearch.WordTrace tailWord_2438736 prefixEnd_2438736 1252243757423275667884463 := by
  unfold tailWord_2438736
  simp only [CollatzResearch.WordTrace]
  refine ⟨44474004646441724897208031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59298672861922299862944041 44474004646441724897208031)
  ·
    refine ⟨66711006969662587345812047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44474004646441724897208031 66711006969662587345812047)
    ·
      refine ⟨100066510454493881018718071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66711006969662587345812047 100066510454493881018718071)
      ·
        refine ⟨150099765681740821528077107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100066510454493881018718071 150099765681740821528077107)
        ·
          refine ⟨225149648522611232292115661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150099765681740821528077107 225149648522611232292115661)
          ·
            refine ⟨84431118195979212109543373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 225149648522611232292115661 84431118195979212109543373)
            ·
              refine ⟨31661669323492204541078765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84431118195979212109543373 31661669323492204541078765)
              ·
                refine ⟨11873125996309576702904537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31661669323492204541078765 11873125996309576702904537)
                ·
                  refine ⟨8904844497232182527178403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11873125996309576702904537 8904844497232182527178403)
                  ·
                    refine ⟨13357266745848273790767605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8904844497232182527178403 13357266745848273790767605)
                    ·
                      refine ⟨1252243757423275667884463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13357266745848273790767605 1252243757423275667884463)
                      ·
                        rfl

theorem cell23_2438736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 5].length) (baseStart_2438736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2438736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2438736 prefixEnd_2438736 := by exact prefixLift 2438736
  have htrace : WordTrace (prefixWord ++ tailWord_2438736) baseStart_2438736 baseEnd_2438736 := by
    simpa [prefixWord, tailWord_2438736, baseEnd_2438736] using wordTrace_append hprefix tailTrace_2438736
  have hstable : (prefixWord ++ tailWord_2438736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2438736).length < 2 ^ (prefixWord ++ tailWord_2438736).sum := by decide
  have hdescent : baseEnd_2438736 < baseStart_2438736 := by decide
  rcases family_descends (prefixWord ++ tailWord_2438736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2438737 : List Nat := [1, 2, 2, 1, 3, 2, 5, 1, 1, 3, 2]
def baseStart_2438737 : Nat := 118140960795 + 2438737 * 2 ^ 59
def prefixEnd_2438737 : Nat := 4983230072969 + 3 ^ 40 * 2438737 * 2
def baseEnd_2438737 : Nat := 1252244270903930163971959

theorem tailTrace_2438737 : CollatzResearch.WordTrace tailWord_2438737 prefixEnd_2438737 1252244270903930163971959 := by
  unfold tailWord_2438737
  simp only [CollatzResearch.WordTrace]
  refine ⟨88948045765879826965202465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59298697177253217976801643 88948045765879826965202465)
  ·
    refine ⟨66711034324409870223901849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88948045765879826965202465 66711034324409870223901849)
    ·
      refine ⟨50033275743307402667926387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66711034324409870223901849 50033275743307402667926387)
      ·
        refine ⟨75049913614961104001889581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50033275743307402667926387 75049913614961104001889581)
        ·
          refine ⟨28143717605610414000708593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75049913614961104001889581 28143717605610414000708593)
          ·
            refine ⟨21107788204207810500531445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28143717605610414000708593 21107788204207810500531445)
            ·
              refine ⟨1978855144144482234424823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21107788204207810500531445 1978855144144482234424823)
              ·
                refine ⟨2968282716216723351637235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1978855144144482234424823 2968282716216723351637235)
                ·
                  refine ⟨4452424074325085027455853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2968282716216723351637235 4452424074325085027455853)
                  ·
                    refine ⟨1669659027871906885295945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4452424074325085027455853 1669659027871906885295945)
                    ·
                      refine ⟨1252244270903930163971959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1669659027871906885295945 1252244270903930163971959)
                      ·
                        rfl

theorem cell23_2438737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 5, 1, 1, 3, 2].length) (baseStart_2438737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2438737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2438737 prefixEnd_2438737 := by exact prefixLift 2438737
  have htrace : WordTrace (prefixWord ++ tailWord_2438737) baseStart_2438737 baseEnd_2438737 := by
    simpa [prefixWord, tailWord_2438737, baseEnd_2438737] using wordTrace_append hprefix tailTrace_2438737
  have hstable : (prefixWord ++ tailWord_2438737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2438737).length < 2 ^ (prefixWord ++ tailWord_2438737).sum := by decide
  have hdescent : baseEnd_2438737 < baseStart_2438737 := by decide
  rcases family_descends (prefixWord ++ tailWord_2438737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2438746 : List Nat := [3, 1, 1, 2, 1, 1, 1, 2, 3, 4, 4]
def baseStart_2438746 : Nat := 118140960795 + 2438746 * 2 ^ 59
def prefixEnd_2438746 : Nat := 4983230072969 + 3 ^ 40 * 2438746 * 2
def baseEnd_2438746 : Nat := 1252248892229820628759417

theorem tailTrace_2438746 : CollatzResearch.WordTrace tailWord_2438746 prefixEnd_2438746 1252248892229820628759417 := by
  unfold tailWord_2438746
  simp only [CollatzResearch.WordTrace]
  refine ⟨22237093505711805375570023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59298916015231481001520061 22237093505711805375570023)
  ·
    refine ⟨33355640258567708063355035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22237093505711805375570023 33355640258567708063355035)
    ·
      refine ⟨50033460387851562095032553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33355640258567708063355035 50033460387851562095032553)
      ·
        refine ⟨37525095290888671571274415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50033460387851562095032553 37525095290888671571274415)
        ·
          refine ⟨56287642936333007356911623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37525095290888671571274415 56287642936333007356911623)
          ·
            refine ⟨84431464404499511035367435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56287642936333007356911623 84431464404499511035367435)
            ·
              refine ⟨126647196606749266553051153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84431464404499511035367435 126647196606749266553051153)
              ·
                refine ⟨94985397455061949914788365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 126647196606749266553051153 94985397455061949914788365)
                ·
                  refine ⟨35619524045648231218045637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 94985397455061949914788365 35619524045648231218045637)
                  ·
                    refine ⟨6678660758559043353383557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35619524045648231218045637 6678660758559043353383557)
                    ·
                      refine ⟨1252248892229820628759417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6678660758559043353383557 1252248892229820628759417)
                      ·
                        rfl

theorem cell23_2438746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 3, 4, 4].length) (baseStart_2438746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2438746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2438746 prefixEnd_2438746 := by exact prefixLift 2438746
  have htrace : WordTrace (prefixWord ++ tailWord_2438746) baseStart_2438746 baseEnd_2438746 := by
    simpa [prefixWord, tailWord_2438746, baseEnd_2438746] using wordTrace_append hprefix tailTrace_2438746
  have hstable : (prefixWord ++ tailWord_2438746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2438746).length < 2 ^ (prefixWord ++ tailWord_2438746).sum := by decide
  have hdescent : baseEnd_2438746 < baseStart_2438746 := by decide
  rcases family_descends (prefixWord ++ tailWord_2438746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2438773 : List Nat := [1, 3, 4, 2, 1, 1, 1, 1, 9]
def baseStart_2438773 : Nat := 118140960795 + 2438773 * 2 ^ 59
def prefixEnd_2438773 : Nat := 4983230072969 + 3 ^ 40 * 2438773 * 2
def baseEnd_2438773 : Nat := 139140306245276891457977

theorem tailTrace_2438773 : CollatzResearch.WordTrace tailWord_2438773 prefixEnd_2438773 139140306245276891457977 := by
  unfold tailWord_2438773
  simp only [CollatzResearch.WordTrace]
  refine ⟨88949358793749405113512973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59299572529166270075675315 88949358793749405113512973)
  ·
    refine ⟨33356009547656026917567365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88949358793749405113512973 33356009547656026917567365)
    ·
      refine ⟨6254251790185505047043881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33356009547656026917567365 6254251790185505047043881)
      ·
        refine ⟨4690688842639128785282911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6254251790185505047043881 4690688842639128785282911)
        ·
          refine ⟨7036033263958693177924367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4690688842639128785282911 7036033263958693177924367)
          ·
            refine ⟨10554049895938039766886551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7036033263958693177924367 10554049895938039766886551)
            ·
              refine ⟨15831074843907059650329827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10554049895938039766886551 15831074843907059650329827)
              ·
                refine ⟨23746612265860589475494741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15831074843907059650329827 23746612265860589475494741)
                ·
                  refine ⟨139140306245276891457977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 23746612265860589475494741 139140306245276891457977)
                  ·
                    rfl

theorem cell23_2438773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 1, 9].length) (baseStart_2438773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2438773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2438773 prefixEnd_2438773 := by exact prefixLift 2438773
  have htrace : WordTrace (prefixWord ++ tailWord_2438773) baseStart_2438773 baseEnd_2438773 := by
    simpa [prefixWord, tailWord_2438773, baseEnd_2438773] using wordTrace_append hprefix tailTrace_2438773
  have hstable : (prefixWord ++ tailWord_2438773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2438773).length < 2 ^ (prefixWord ++ tailWord_2438773).sum := by decide
  have hdescent : baseEnd_2438773 < baseStart_2438773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2438773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2438818 : List Nat := [3, 3, 1, 4, 1, 1, 3, 1, 2, 2, 2]
def baseStart_2438818 : Nat := 118140960795 + 2438818 * 2 ^ 59
def prefixEnd_2438818 : Nat := 4983230072969 + 3 ^ 40 * 2438818 * 2
def baseEnd_2438818 : Nat := 1252285862836944347059087

theorem tailTrace_2438818 : CollatzResearch.WordTrace tailWord_2438818 prefixEnd_2438818 1252285862836944347059087 := by
  unfold tailWord_2438818
  simp only [CollatzResearch.WordTrace]
  refine ⟨22237750019646594449725277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59300666719057585199267405 22237750019646594449725277)
  ·
    refine ⟨8339156257367472918646979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22237750019646594449725277 8339156257367472918646979)
    ·
      refine ⟨12508734386051209377970469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8339156257367472918646979 12508734386051209377970469)
      ·
        refine ⟨2345387697384601758369463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12508734386051209377970469 2345387697384601758369463)
        ·
          refine ⟨3518081546076902637554195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2345387697384601758369463 3518081546076902637554195)
          ·
            refine ⟨5277122319115353956331293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3518081546076902637554195 5277122319115353956331293)
            ·
              refine ⟨1978920869668257733624235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5277122319115353956331293 1978920869668257733624235)
              ·
                refine ⟨2968381304502386600436353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1978920869668257733624235 2968381304502386600436353)
                ·
                  refine ⟨2226285978376789950327265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2968381304502386600436353 2226285978376789950327265)
                  ·
                    refine ⟨1669714483782592462745449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2226285978376789950327265 1669714483782592462745449)
                    ·
                      refine ⟨1252285862836944347059087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1669714483782592462745449 1252285862836944347059087)
                      ·
                        rfl

theorem cell23_2438818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_2438818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2438818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2438818 prefixEnd_2438818 := by exact prefixLift 2438818
  have htrace : WordTrace (prefixWord ++ tailWord_2438818) baseStart_2438818 baseEnd_2438818 := by
    simpa [prefixWord, tailWord_2438818, baseEnd_2438818] using wordTrace_append hprefix tailTrace_2438818
  have hstable : (prefixWord ++ tailWord_2438818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2438818).length < 2 ^ (prefixWord ++ tailWord_2438818).sum := by decide
  have hdescent : baseEnd_2438818 < baseStart_2438818 := by decide
  rcases family_descends (prefixWord ++ tailWord_2438818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2438843 : List Nat := [1, 1, 1, 1, 1, 2, 3, 2, 6, 2, 3]
def baseStart_2438843 : Nat := 118140960795 + 2438843 * 2 ^ 59
def prefixEnd_2438843 : Nat := 4983230072969 + 3 ^ 40 * 2438843 * 2
def baseEnd_2438843 : Nat := 1252298699853306749246471

theorem tailTrace_2438843 : CollatzResearch.WordTrace tailWord_2438843 prefixEnd_2438843 1252298699853306749246471 := by
  unfold tailWord_2438843
  simp only [CollatzResearch.WordTrace]
  refine ⟨88951911903495807068561183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59301274602330538045707455 88951911903495807068561183)
  ·
    refine ⟨133427867855243710602841775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88951911903495807068561183 133427867855243710602841775)
    ·
      refine ⟨200141801782865565904262663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133427867855243710602841775 200141801782865565904262663)
      ·
        refine ⟨300212702674298348856393995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200141801782865565904262663 300212702674298348856393995)
        ·
          refine ⟨450319054011447523284590993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 300212702674298348856393995 450319054011447523284590993)
          ·
            refine ⟨337739290508585642463443245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 450319054011447523284590993 337739290508585642463443245)
            ·
              refine ⟨126652233940719615923791217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 337739290508585642463443245 126652233940719615923791217)
              ·
                refine ⟨94989175455539711942843413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 126652233940719615923791217 94989175455539711942843413)
                ·
                  refine ⟨4452617599478423997320785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 94989175455539711942843413 4452617599478423997320785)
                  ·
                    refine ⟨3339463199608817997990589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4452617599478423997320785 3339463199608817997990589)
                    ·
                      refine ⟨1252298699853306749246471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3339463199608817997990589 1252298699853306749246471)
                      ·
                        rfl

theorem cell23_2438843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 6, 2, 3].length) (baseStart_2438843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2438843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2438843 prefixEnd_2438843 := by exact prefixLift 2438843
  have htrace : WordTrace (prefixWord ++ tailWord_2438843) baseStart_2438843 baseEnd_2438843 := by
    simpa [prefixWord, tailWord_2438843, baseEnd_2438843] using wordTrace_append hprefix tailTrace_2438843
  have hstable : (prefixWord ++ tailWord_2438843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2438843).length < 2 ^ (prefixWord ++ tailWord_2438843).sum := by decide
  have hdescent : baseEnd_2438843 < baseStart_2438843 := by decide
  rcases family_descends (prefixWord ++ tailWord_2438843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2438854 : List Nat := [6, 1, 2, 1, 1, 2, 1, 2, 2, 5]
def baseStart_2438854 : Nat := 118140960795 + 2438854 * 2 ^ 59
def prefixEnd_2438854 : Nat := 4983230072969 + 3 ^ 40 * 2438854 * 2
def baseEnd_2438854 : Nat := 417434782713502068736307

theorem tailTrace_2438854 : CollatzResearch.WordTrace tailWord_2438854 prefixEnd_2438854 417434782713502068736307 := by
  unfold tailWord_2438854
  simp only [CollatzResearch.WordTrace]
  refine ⟨2779759784576748623350363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 59301542070970637298141077 2779759784576748623350363)
  ·
    refine ⟨4169639676865122935025545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2779759784576748623350363 4169639676865122935025545)
    ·
      refine ⟨3127229757648842201269159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4169639676865122935025545 3127229757648842201269159)
      ·
        refine ⟨4690844636473263301903739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3127229757648842201269159 4690844636473263301903739)
        ·
          refine ⟨7036266954709894952855609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4690844636473263301903739 7036266954709894952855609)
          ·
            refine ⟨5277200216032421214641707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7036266954709894952855609 5277200216032421214641707)
            ·
              refine ⟨7915800324048631821962561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5277200216032421214641707 7915800324048631821962561)
              ·
                refine ⟨5936850243036473866471921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7915800324048631821962561 5936850243036473866471921)
                ·
                  refine ⟨4452637682277355399853941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5936850243036473866471921 4452637682277355399853941)
                  ·
                    refine ⟨417434782713502068736307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4452637682277355399853941 417434782713502068736307)
                    ·
                      rfl

theorem cell23_2438854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_2438854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2438854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2438854 prefixEnd_2438854 := by exact prefixLift 2438854
  have htrace : WordTrace (prefixWord ++ tailWord_2438854) baseStart_2438854 baseEnd_2438854 := by
    simpa [prefixWord, tailWord_2438854, baseEnd_2438854] using wordTrace_append hprefix tailTrace_2438854
  have hstable : (prefixWord ++ tailWord_2438854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2438854).length < 2 ^ (prefixWord ++ tailWord_2438854).sum := by decide
  have hdescent : baseEnd_2438854 < baseStart_2438854 := by decide
  rcases family_descends (prefixWord ++ tailWord_2438854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2438880 : List Nat := [2, 1, 1, 3, 1, 2, 6, 1, 6]
def baseStart_2438880 : Nat := 118140960795 + 2438880 * 2 ^ 59
def prefixEnd_2438880 : Nat := 4983230072969 + 3 ^ 40 * 2438880 * 2
def baseEnd_2438880 : Nat := 139146410959724789387089

theorem tailTrace_2438880 : CollatzResearch.WordTrace tailWord_2438880 prefixEnd_2438880 139146410959724789387089 := by
  unfold tailWord_2438880
  simp only [CollatzResearch.WordTrace]
  refine ⟨44476630702180881193829047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59302174269574508258438729 44476630702180881193829047)
  ·
    refine ⟨66714946053271321790743571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44476630702180881193829047 66714946053271321790743571)
    ·
      refine ⟨100072419079906982686115357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66714946053271321790743571 100072419079906982686115357)
      ·
        refine ⟨37527157154965118507293259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100072419079906982686115357 37527157154965118507293259)
        ·
          refine ⟨56290735732447677760939889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37527157154965118507293259 56290735732447677760939889)
          ·
            refine ⟨42218051799335758320704917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56290735732447677760939889 42218051799335758320704917)
            ·
              refine ⟨1978971178093863671283043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 42218051799335758320704917 1978971178093863671283043)
              ·
                refine ⟨2968456767140795506924565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1978971178093863671283043 2968456767140795506924565)
                ·
                  refine ⟨139146410959724789387089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2968456767140795506924565 139146410959724789387089)
                  ·
                    rfl

theorem cell23_2438880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 6, 1, 6].length) (baseStart_2438880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2438880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2438880 prefixEnd_2438880 := by exact prefixLift 2438880
  have htrace : WordTrace (prefixWord ++ tailWord_2438880) baseStart_2438880 baseEnd_2438880 := by
    simpa [prefixWord, tailWord_2438880, baseEnd_2438880] using wordTrace_append hprefix tailTrace_2438880
  have hstable : (prefixWord ++ tailWord_2438880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2438880).length < 2 ^ (prefixWord ++ tailWord_2438880).sum := by decide
  have hdescent : baseEnd_2438880 < baseStart_2438880 := by decide
  rcases family_descends (prefixWord ++ tailWord_2438880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2438940 : List Nat := [2, 2, 3, 1, 1, 2, 4, 1, 1, 6]
def baseStart_2438940 : Nat := 118140960795 + 2438940 * 2 ^ 59
def prefixEnd_2438940 : Nat := 4983230072969 + 3 ^ 40 * 2438940 * 2
def baseEnd_2438940 : Nat := 417449502492264289911175

theorem tailTrace_2438940 : CollatzResearch.WordTrace tailWord_2438940 prefixEnd_2438940 417449502492264289911175 := by
  unfold tailWord_2438940
  simp only [CollatzResearch.WordTrace]
  refine ⟨44477724892072196317421137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59303633189429595089894849 44477724892072196317421137)
  ·
    refine ⟨33358293669054147238065853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44477724892072196317421137 33358293669054147238065853)
    ·
      refine ⟨12509360125895305214274695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33358293669054147238065853 12509360125895305214274695)
      ·
        refine ⟨18764040188842957821412043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12509360125895305214274695 18764040188842957821412043)
        ·
          refine ⟨28146060283264436732118065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18764040188842957821412043 28146060283264436732118065)
          ·
            refine ⟨21109545212448327549088549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28146060283264436732118065 21109545212448327549088549)
            ·
              refine ⟨3958039727334061415454103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21109545212448327549088549 3958039727334061415454103)
              ·
                refine ⟨5937059591001092123181155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3958039727334061415454103 5937059591001092123181155)
                ·
                  refine ⟨8905589386501638184771733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5937059591001092123181155 8905589386501638184771733)
                  ·
                    refine ⟨417449502492264289911175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8905589386501638184771733 417449502492264289911175)
                    ·
                      rfl

theorem cell23_2438940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 1, 1, 6].length) (baseStart_2438940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2438940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2438940 prefixEnd_2438940 := by exact prefixLift 2438940
  have htrace : WordTrace (prefixWord ++ tailWord_2438940) baseStart_2438940 baseEnd_2438940 := by
    simpa [prefixWord, tailWord_2438940, baseEnd_2438940] using wordTrace_append hprefix tailTrace_2438940
  have hstable : (prefixWord ++ tailWord_2438940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2438940).length < 2 ^ (prefixWord ++ tailWord_2438940).sum := by decide
  have hdescent : baseEnd_2438940 < baseStart_2438940 := by decide
  rcases family_descends (prefixWord ++ tailWord_2438940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2438947 : List Nat := [1, 1, 1, 4, 2, 1, 3, 1, 5, 2, 2]
def baseStart_2438947 : Nat := 118140960795 + 2438947 * 2 ^ 59
def prefixEnd_2438947 : Nat := 4983230072969 + 3 ^ 40 * 2438947 * 2
def baseEnd_2438947 : Nat := 1252352101841374342345993

theorem tailTrace_2438947 : CollatzResearch.WordTrace tailWord_2438947 prefixEnd_2438947 1252352101841374342345993 := by
  unfold tailWord_2438947
  simp only [CollatzResearch.WordTrace]
  refine ⟨88955705095119032830347095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59303803396746021886898063 88955705095119032830347095)
  ·
    refine ⟨133433557642678549245520643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88955705095119032830347095 133433557642678549245520643)
    ·
      refine ⟨200150336464017823868280965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133433557642678549245520643 200150336464017823868280965)
      ·
        refine ⟨37528188087003341975302681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 200150336464017823868280965 37528188087003341975302681)
        ·
          refine ⟨28146141065252506481477011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37528188087003341975302681 28146141065252506481477011)
          ·
            refine ⟨42219211597878759722215517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28146141065252506481477011 42219211597878759722215517)
            ·
              refine ⟨15832204349204534895830819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42219211597878759722215517 15832204349204534895830819)
              ·
                refine ⟨23748306523806802343746229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15832204349204534895830819 23748306523806802343746229)
                ·
                  refine ⟨2226403736606887719726209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23748306523806802343746229 2226403736606887719726209)
                  ·
                    refine ⟨1669802802455165789794657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2226403736606887719726209 1669802802455165789794657)
                    ·
                      refine ⟨1252352101841374342345993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1669802802455165789794657 1252352101841374342345993)
                      ·
                        rfl

theorem cell23_2438947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 1, 5, 2, 2].length) (baseStart_2438947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2438947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2438947 prefixEnd_2438947 := by exact prefixLift 2438947
  have htrace : WordTrace (prefixWord ++ tailWord_2438947) baseStart_2438947 baseEnd_2438947 := by
    simpa [prefixWord, tailWord_2438947, baseEnd_2438947] using wordTrace_append hprefix tailTrace_2438947
  have hstable : (prefixWord ++ tailWord_2438947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2438947).length < 2 ^ (prefixWord ++ tailWord_2438947).sum := by decide
  have hdescent : baseEnd_2438947 < baseStart_2438947 := by decide
  rcases family_descends (prefixWord ++ tailWord_2438947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2438958 : List Nat := [4, 1, 3, 2, 2, 1, 2, 3, 1, 1, 3]
def baseStart_2438958 : Nat := 118140960795 + 2438958 * 2 ^ 59
def prefixEnd_2438958 : Nat := 4983230072969 + 3 ^ 40 * 2438958 * 2
def baseEnd_2438958 : Nat := 1252357750128573799308443

theorem tailTrace_2438958 : CollatzResearch.WordTrace tailWord_2438958 prefixEnd_2438958 1252357750128573799308443 := by
  unfold tailWord_2438958
  simp only [CollatzResearch.WordTrace]
  refine ⟨11119513287259897713624691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59304070865386121139331685 11119513287259897713624691)
  ·
    refine ⟨16679269930889846570437037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11119513287259897713624691 16679269930889846570437037)
    ·
      refine ⟨6254726224083692463913889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16679269930889846570437037 6254726224083692463913889)
      ·
        refine ⟨4691044668062769347935417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6254726224083692463913889 4691044668062769347935417)
        ·
          refine ⟨3518283501047077010951563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4691044668062769347935417 3518283501047077010951563)
          ·
            refine ⟨5277425251570615516427345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3518283501047077010951563 5277425251570615516427345)
            ·
              refine ⟨3958068938677961637320509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5277425251570615516427345 3958068938677961637320509)
              ·
                refine ⟨1484275852004235613995191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3958068938677961637320509 1484275852004235613995191)
                ·
                  refine ⟨2226413778006353420992787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1484275852004235613995191 2226413778006353420992787)
                  ·
                    refine ⟨3339620667009530131489181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2226413778006353420992787 3339620667009530131489181)
                    ·
                      refine ⟨1252357750128573799308443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3339620667009530131489181 1252357750128573799308443)
                      ·
                        rfl

theorem cell23_2438958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 3, 1, 1, 3].length) (baseStart_2438958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2438958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2438958 prefixEnd_2438958 := by exact prefixLift 2438958
  have htrace : WordTrace (prefixWord ++ tailWord_2438958) baseStart_2438958 baseEnd_2438958 := by
    simpa [prefixWord, tailWord_2438958, baseEnd_2438958] using wordTrace_append hprefix tailTrace_2438958
  have hstable : (prefixWord ++ tailWord_2438958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2438958).length < 2 ^ (prefixWord ++ tailWord_2438958).sum := by decide
  have hdescent : baseEnd_2438958 < baseStart_2438958 := by decide
  rcases family_descends (prefixWord ++ tailWord_2438958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2438964 : List Nat := [2, 5, 1, 1, 2, 2, 1, 3, 1, 1, 4]
def baseStart_2438964 : Nat := 118140960795 + 2438964 * 2 ^ 59
def prefixEnd_2438964 : Nat := 4983230072969 + 3 ^ 40 * 2438964 * 2
def baseEnd_2438964 : Nat := 1252360831012500775833415

theorem tailTrace_2438964 : CollatzResearch.WordTrace tailWord_2438964 prefixEnd_2438964 1252360831012500775833415 := by
  unfold tailWord_2438964
  simp only [CollatzResearch.WordTrace]
  refine ⟨44478162568028722366857973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59304216757371629822477297 44478162568028722366857973)
  ·
    refine ⟨4169827740752692721892935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 44478162568028722366857973 4169827740752692721892935)
    ·
      refine ⟨6254741611129039082839403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4169827740752692721892935 6254741611129039082839403)
      ·
        refine ⟨9382112416693558624259105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6254741611129039082839403 9382112416693558624259105)
        ·
          refine ⟨7036584312520168968194329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9382112416693558624259105 7036584312520168968194329)
          ·
            refine ⟨5277438234390126726145747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7036584312520168968194329 5277438234390126726145747)
            ·
              refine ⟨7916157351585190089218621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5277438234390126726145747 7916157351585190089218621)
              ·
                refine ⟨2968559006844446283456983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7916157351585190089218621 2968559006844446283456983)
                ·
                  refine ⟨4452838510266669425185475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2968559006844446283456983 4452838510266669425185475)
                  ·
                    refine ⟨6679257765400004137778213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4452838510266669425185475 6679257765400004137778213)
                    ·
                      refine ⟨1252360831012500775833415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6679257765400004137778213 1252360831012500775833415)
                      ·
                        rfl

theorem cell23_2438964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 3, 1, 1, 4].length) (baseStart_2438964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2438964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2438964 prefixEnd_2438964 := by exact prefixLift 2438964
  have htrace : WordTrace (prefixWord ++ tailWord_2438964) baseStart_2438964 baseEnd_2438964 := by
    simpa [prefixWord, tailWord_2438964, baseEnd_2438964] using wordTrace_append hprefix tailTrace_2438964
  have hstable : (prefixWord ++ tailWord_2438964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2438964).length < 2 ^ (prefixWord ++ tailWord_2438964).sum := by decide
  have hdescent : baseEnd_2438964 < baseStart_2438964 := by decide
  rcases family_descends (prefixWord ++ tailWord_2438964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2438974 : List Nat := [4, 2, 1, 2, 2, 1, 3, 2, 2, 4]
def baseStart_2438974 : Nat := 118140960795 + 2438974 * 2 ^ 59
def prefixEnd_2438974 : Nat := 4983230072969 + 3 ^ 40 * 2438974 * 2
def baseEnd_2438974 : Nat := 417455321939681912236123

theorem tailTrace_2438974 : CollatzResearch.WordTrace tailWord_2438974 prefixEnd_2438974 417455321939681912236123 := by
  unfold tailWord_2438974
  simp only [CollatzResearch.WordTrace]
  refine ⟨11119586233252652055197497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59304459910680810961053317 11119586233252652055197497)
  ·
    refine ⟨8339689674939489041398123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11119586233252652055197497 8339689674939489041398123)
    ·
      refine ⟨12509534512409233562097185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8339689674939489041398123 12509534512409233562097185)
      ·
        refine ⟨9382150884306925171572889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12509534512409233562097185 9382150884306925171572889)
        ·
          refine ⟨7036613163230193878679667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9382150884306925171572889 7036613163230193878679667)
          ·
            refine ⟨10554919744845290818019501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7036613163230193878679667 10554919744845290818019501)
            ·
              refine ⟨3958094904316984056757313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10554919744845290818019501 3958094904316984056757313)
              ·
                refine ⟨2968571178237738042567985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3958094904316984056757313 2968571178237738042567985)
                ·
                  refine ⟨2226428383678303531925989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2968571178237738042567985 2226428383678303531925989)
                  ·
                    refine ⟨417455321939681912236123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2226428383678303531925989 417455321939681912236123)
                    ·
                      rfl

theorem cell23_2438974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 2, 2, 4].length) (baseStart_2438974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2438974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2438974 prefixEnd_2438974 := by exact prefixLift 2438974
  have htrace : WordTrace (prefixWord ++ tailWord_2438974) baseStart_2438974 baseEnd_2438974 := by
    simpa [prefixWord, tailWord_2438974, baseEnd_2438974] using wordTrace_append hprefix tailTrace_2438974
  have hstable : (prefixWord ++ tailWord_2438974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2438974).length < 2 ^ (prefixWord ++ tailWord_2438974).sum := by decide
  have hdescent : baseEnd_2438974 < baseStart_2438974 := by decide
  rcases family_descends (prefixWord ++ tailWord_2438974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2438983 : List Nat := [1, 1, 4, 1, 2, 1, 2, 1, 1, 9]
def baseStart_2438983 : Nat := 118140960795 + 2438983 * 2 ^ 59
def prefixEnd_2438983 : Nat := 4983230072969 + 3 ^ 40 * 2438983 * 2
def baseEnd_2438983 : Nat := 417456862381645400498609

theorem tailTrace_2438983 : CollatzResearch.WordTrace tailWord_2438983 prefixEnd_2438983 417456862381645400498609 := by
  unfold tailWord_2438983
  simp only [CollatzResearch.WordTrace]
  refine ⟨88957018122988610978657603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59304678748659073985771735 88957018122988610978657603)
  ·
    refine ⟨133435527184482916467986405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88957018122988610978657603 133435527184482916467986405)
    ·
      refine ⟨25019161347090546837747451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 133435527184482916467986405 25019161347090546837747451)
      ·
        refine ⟨37528742020635820256621177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25019161347090546837747451 37528742020635820256621177)
        ·
          refine ⟨28146556515476865192465883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37528742020635820256621177 28146556515476865192465883)
          ·
            refine ⟨42219834773215297788698825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28146556515476865192465883 42219834773215297788698825)
            ·
              refine ⟨31664876079911473341524119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42219834773215297788698825 31664876079911473341524119)
              ·
                refine ⟨47497314119867210012286179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31664876079911473341524119 47497314119867210012286179)
                ·
                  refine ⟨71245971179800815018429269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47497314119867210012286179 71245971179800815018429269)
                  ·
                    refine ⟨417456862381645400498609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 71245971179800815018429269 417456862381645400498609)
                    ·
                      rfl

theorem cell23_2438983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 9].length) (baseStart_2438983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2438983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2438983 prefixEnd_2438983 := by exact prefixLift 2438983
  have htrace : WordTrace (prefixWord ++ tailWord_2438983) baseStart_2438983 baseEnd_2438983 := by
    simpa [prefixWord, tailWord_2438983, baseEnd_2438983] using wordTrace_append hprefix tailTrace_2438983
  have hstable : (prefixWord ++ tailWord_2438983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2438983).length < 2 ^ (prefixWord ++ tailWord_2438983).sum := by decide
  have hdescent : baseEnd_2438983 < baseStart_2438983 := by decide
  rcases family_descends (prefixWord ++ tailWord_2438983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2438997 : List Nat := [1, 3, 2, 2, 2, 2, 3, 1, 1, 3, 3]
def baseStart_2438997 : Nat := 118140960795 + 2438997 * 2 ^ 59
def prefixEnd_2438997 : Nat := 4983230072969 + 3 ^ 40 * 2438997 * 2
def baseEnd_2438997 : Nat := 1252377775874099146720763

theorem tailTrace_2438997 : CollatzResearch.WordTrace tailWord_2438997 prefixEnd_2438997 1252377775874099146720763 := by
  unfold tailWord_2438997
  simp only [CollatzResearch.WordTrace]
  refine ⟨88957528744937891369667245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59305019163291927579778163 88957528744937891369667245)
  ·
    refine ⟨33359073279351709263625217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88957528744937891369667245 33359073279351709263625217)
    ·
      refine ⟨25019304959513781947718913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33359073279351709263625217 25019304959513781947718913)
      ·
        refine ⟨18764478719635336460789185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25019304959513781947718913 18764478719635336460789185)
        ·
          refine ⟨14073359039726502345591889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18764478719635336460789185 14073359039726502345591889)
          ·
            refine ⟨10555019279794876759193917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14073359039726502345591889 10555019279794876759193917)
            ·
              refine ⟨3958132229923078784697719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10555019279794876759193917 3958132229923078784697719)
              ·
                refine ⟨5937198344884618177046579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3958132229923078784697719 5937198344884618177046579)
                ·
                  refine ⟨8905797517326927265569869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5937198344884618177046579 8905797517326927265569869)
                  ·
                    refine ⟨3339674068997597724588701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8905797517326927265569869 3339674068997597724588701)
                    ·
                      refine ⟨1252377775874099146720763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3339674068997597724588701 1252377775874099146720763)
                      ·
                        rfl

theorem cell23_2438997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 1, 1, 3, 3].length) (baseStart_2438997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2438997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2438997 prefixEnd_2438997 := by exact prefixLift 2438997
  have htrace : WordTrace (prefixWord ++ tailWord_2438997) baseStart_2438997 baseEnd_2438997 := by
    simpa [prefixWord, tailWord_2438997, baseEnd_2438997] using wordTrace_append hprefix tailTrace_2438997
  have hstable : (prefixWord ++ tailWord_2438997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2438997).length < 2 ^ (prefixWord ++ tailWord_2438997).sum := by decide
  have hdescent : baseEnd_2438997 < baseStart_2438997 := by decide
  rcases family_descends (prefixWord ++ tailWord_2438997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2439004 : List Nat := [2, 2, 4, 2, 2, 2, 2, 7]
def baseStart_2439004 : Nat := 118140960795 + 2439004 * 2 ^ 59
def prefixEnd_2439004 : Nat := 4983230072969 + 3 ^ 40 * 2439004 * 2
def baseEnd_2439004 : Nat := 46384495194025208123453

theorem tailTrace_2439004 : CollatzResearch.WordTrace tailWord_2439004 prefixEnd_2439004 46384495194025208123453 := by
  unfold tailWord_2439004
  simp only [CollatzResearch.WordTrace]
  refine ⟨44478892027956265782586033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59305189370608354376781377 44478892027956265782586033)
  ·
    refine ⟨33359169020967199336939525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44478892027956265782586033 33359169020967199336939525)
    ·
      refine ⟨6254844191431349875676161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33359169020967199336939525 6254844191431349875676161)
      ·
        refine ⟨4691133143573512406757121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6254844191431349875676161 4691133143573512406757121)
        ·
          refine ⟨3518349857680134305067841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4691133143573512406757121 3518349857680134305067841)
          ·
            refine ⟨2638762393260100728800881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3518349857680134305067841 2638762393260100728800881)
            ·
              refine ⟨1979071794945075546600661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2638762393260100728800881 1979071794945075546600661)
              ·
                refine ⟨46384495194025208123453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1979071794945075546600661 46384495194025208123453)
                ·
                  rfl

theorem cell23_2439004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 2, 7].length) (baseStart_2439004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2439004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2439004 prefixEnd_2439004 := by exact prefixLift 2439004
  have htrace : WordTrace (prefixWord ++ tailWord_2439004) baseStart_2439004 baseEnd_2439004 := by
    simpa [prefixWord, tailWord_2439004, baseEnd_2439004] using wordTrace_append hprefix tailTrace_2439004
  have hstable : (prefixWord ++ tailWord_2439004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2439004).length < 2 ^ (prefixWord ++ tailWord_2439004).sum := by decide
  have hdescent : baseEnd_2439004 < baseStart_2439004 := by decide
  rcases family_descends (prefixWord ++ tailWord_2439004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2439040 : List Nat := [2, 1, 1, 2, 1, 2, 4, 1, 2, 4, 3]
def baseStart_2439040 : Nat := 118140960795 + 2439040 * 2 ^ 59
def prefixEnd_2439040 : Nat := 4983230072969 + 3 ^ 40 * 2439040 * 2
def baseEnd_2439040 : Nat := 1252399855542242478483065

theorem tailTrace_2439040 : CollatzResearch.WordTrace tailWord_2439040 prefixEnd_2439040 1252399855542242478483065 := by
  unfold tailWord_2439040
  simp only [CollatzResearch.WordTrace]
  refine ⟨44479548541891054856741287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59306064722521406475655049 44479548541891054856741287)
  ·
    refine ⟨66719322812836582285111931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44479548541891054856741287 66719322812836582285111931)
    ·
      refine ⟨100078984219254873427667897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66719322812836582285111931 100078984219254873427667897)
      ·
        refine ⟨75059238164441155070750923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100078984219254873427667897 75059238164441155070750923)
        ·
          refine ⟨112588857246661732606126385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75059238164441155070750923 112588857246661732606126385)
          ·
            refine ⟨84441642934996299454594789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112588857246661732606126385 84441642934996299454594789)
            ·
              refine ⟨15832808050311806147736523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 84441642934996299454594789 15832808050311806147736523)
              ·
                refine ⟨23749212075467709221604785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15832808050311806147736523 23749212075467709221604785)
                ·
                  refine ⟨17811909056600781916203589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23749212075467709221604785 17811909056600781916203589)
                  ·
                    refine ⟨3339732948112646609288173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17811909056600781916203589 3339732948112646609288173)
                    ·
                      refine ⟨1252399855542242478483065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3339732948112646609288173 1252399855542242478483065)
                      ·
                        rfl

theorem cell23_2439040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 1, 2, 4, 3].length) (baseStart_2439040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2439040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2439040 prefixEnd_2439040 := by exact prefixLift 2439040
  have htrace : WordTrace (prefixWord ++ tailWord_2439040) baseStart_2439040 baseEnd_2439040 := by
    simpa [prefixWord, tailWord_2439040, baseEnd_2439040] using wordTrace_append hprefix tailTrace_2439040
  have hstable : (prefixWord ++ tailWord_2439040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2439040).length < 2 ^ (prefixWord ++ tailWord_2439040).sum := by decide
  have hdescent : baseEnd_2439040 < baseStart_2439040 := by decide
  rcases family_descends (prefixWord ++ tailWord_2439040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2439048 : List Nat := [2, 1, 3, 3, 3, 2, 2, 1, 2, 1, 3]
def baseStart_2439048 : Nat := 118140960795 + 2439048 * 2 ^ 59
def prefixEnd_2439048 : Nat := 4983230072969 + 3 ^ 40 * 2439048 * 2
def baseEnd_2439048 : Nat := 1252403963387478447183029

theorem tailTrace_2439048 : CollatzResearch.WordTrace tailWord_2439048 prefixEnd_2439048 1252403963387478447183029 := by
  unfold tailWord_2439048
  simp only [CollatzResearch.WordTrace]
  refine ⟨44479694433876563539886899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59306259245168751386515865 44479694433876563539886899)
  ·
    refine ⟨66719541650814845309830349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44479694433876563539886899 66719541650814845309830349)
    ·
      refine ⟨25019828119055566991186381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66719541650814845309830349 25019828119055566991186381)
      ·
        refine ⟨9382435544645837621694893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25019828119055566991186381 9382435544645837621694893)
        ·
          refine ⟨3518413329242189108135585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9382435544645837621694893 3518413329242189108135585)
          ·
            refine ⟨2638809996931641831101689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3518413329242189108135585 2638809996931641831101689)
            ·
              refine ⟨1979107497698731373326267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2638809996931641831101689 1979107497698731373326267)
              ·
                refine ⟨2968661246548097059989401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1979107497698731373326267 2968661246548097059989401)
                ·
                  refine ⟨2226495934911072794992051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2968661246548097059989401 2226495934911072794992051)
                  ·
                    refine ⟨3339743902366609192488077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2226495934911072794992051 3339743902366609192488077)
                    ·
                      refine ⟨1252403963387478447183029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3339743902366609192488077 1252403963387478447183029)
                      ·
                        rfl

theorem cell23_2439048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 2, 1, 2, 1, 3].length) (baseStart_2439048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2439048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2439048 prefixEnd_2439048 := by exact prefixLift 2439048
  have htrace : WordTrace (prefixWord ++ tailWord_2439048) baseStart_2439048 baseEnd_2439048 := by
    simpa [prefixWord, tailWord_2439048, baseEnd_2439048] using wordTrace_append hprefix tailTrace_2439048
  have hstable : (prefixWord ++ tailWord_2439048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2439048).length < 2 ^ (prefixWord ++ tailWord_2439048).sum := by decide
  have hdescent : baseEnd_2439048 < baseStart_2439048 := by decide
  rcases family_descends (prefixWord ++ tailWord_2439048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2439058 : List Nat := [3, 2, 3, 2, 1, 3, 1, 2, 1, 3, 2]
def baseStart_2439058 : Nat := 118140960795 + 2439058 * 2 ^ 59
def prefixEnd_2439058 : Nat := 4983230072969 + 3 ^ 40 * 2439058 * 2
def baseEnd_2439058 : Nat := 1252409098194023408057983

theorem tailTrace_2439058 : CollatzResearch.WordTrace tailWord_2439058 prefixEnd_2439058 1252409098194023408057983 := by
  unfold tailWord_2439058
  simp only [CollatzResearch.WordTrace]
  refine ⟨22239938399429224696909457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59306502398477932525091885 22239938399429224696909457)
  ·
    refine ⟨16679953799571918522682093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22239938399429224696909457 16679953799571918522682093)
    ·
      refine ⟨6254982674839469446005785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16679953799571918522682093 6254982674839469446005785)
      ·
        refine ⟨4691237006129602084504339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6254982674839469446005785 4691237006129602084504339)
        ·
          refine ⟨7036855509194403126756509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4691237006129602084504339 7036855509194403126756509)
          ·
            refine ⟨2638820815947901172533691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7036855509194403126756509 2638820815947901172533691)
            ·
              refine ⟨3958231223921851758800537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2638820815947901172533691 3958231223921851758800537)
              ·
                refine ⟨2968673417941388819100403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3958231223921851758800537 2968673417941388819100403)
                ·
                  refine ⟨4453010126912083228650605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2968673417941388819100403 4453010126912083228650605)
                  ·
                    refine ⟨1669878797592031210743977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4453010126912083228650605 1669878797592031210743977)
                    ·
                      refine ⟨1252409098194023408057983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1669878797592031210743977 1252409098194023408057983)
                      ·
                        rfl

theorem cell23_2439058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 2, 1, 3, 2].length) (baseStart_2439058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2439058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2439058 prefixEnd_2439058 := by exact prefixLift 2439058
  have htrace : WordTrace (prefixWord ++ tailWord_2439058) baseStart_2439058 baseEnd_2439058 := by
    simpa [prefixWord, tailWord_2439058, baseEnd_2439058] using wordTrace_append hprefix tailTrace_2439058
  have hstable : (prefixWord ++ tailWord_2439058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2439058).length < 2 ^ (prefixWord ++ tailWord_2439058).sum := by decide
  have hdescent : baseEnd_2439058 < baseStart_2439058 := by decide
  rcases family_descends (prefixWord ++ tailWord_2439058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2439097 : List Nat := [1, 2, 1, 4, 2, 1, 1, 1, 1, 7, 2]
def baseStart_2439097 : Nat := 118140960795 + 2439097 * 2 ^ 59
def prefixEnd_2439097 : Nat := 4983230072969 + 3 ^ 40 * 2439097 * 2
def baseEnd_2439097 : Nat := 1252429123939548755470303

theorem tailTrace_2439097 : CollatzResearch.WordTrace tailWord_2439097 prefixEnd_2439097 1252429123939548755470303 := by
  unfold tailWord_2439097
  simp only [CollatzResearch.WordTrace]
  refine ⟨88961176044575608448307545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59307450696383738965538363 88961176044575608448307545)
  ·
    refine ⟨66720882033431706336230659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88961176044575608448307545 66720882033431706336230659)
    ·
      refine ⟨100081323050147559504345989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66720882033431706336230659 100081323050147559504345989)
      ·
        refine ⟨18765248071902667407064873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 100081323050147559504345989 18765248071902667407064873)
        ·
          refine ⟨14073936053927000555298655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18765248071902667407064873 14073936053927000555298655)
          ·
            refine ⟨21110904080890500832947983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14073936053927000555298655 21110904080890500832947983)
            ·
              refine ⟨31666356121335751249421975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21110904080890500832947983 31666356121335751249421975)
              ·
                refine ⟨47499534182003626874132963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31666356121335751249421975 47499534182003626874132963)
                ·
                  refine ⟨71249301273005440311199445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47499534182003626874132963 71249301273005440311199445)
                  ·
                    refine ⟨1669905498586065007293737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 71249301273005440311199445 1669905498586065007293737)
                    ·
                      refine ⟨1252429123939548755470303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1669905498586065007293737 1252429123939548755470303)
                      ·
                        rfl

theorem cell23_2439097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 7, 2].length) (baseStart_2439097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2439097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2439097 prefixEnd_2439097 := by exact prefixLift 2439097
  have htrace : WordTrace (prefixWord ++ tailWord_2439097) baseStart_2439097 baseEnd_2439097 := by
    simpa [prefixWord, tailWord_2439097, baseEnd_2439097] using wordTrace_append hprefix tailTrace_2439097
  have hstable : (prefixWord ++ tailWord_2439097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2439097).length < 2 ^ (prefixWord ++ tailWord_2439097).sum := by decide
  have hdescent : baseEnd_2439097 < baseStart_2439097 := by decide
  rcases family_descends (prefixWord ++ tailWord_2439097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2439127 : List Nat := [1, 1, 3, 2, 1, 1, 3, 2, 1, 6, 2]
def baseStart_2439127 : Nat := 118140960795 + 2439127 * 2 ^ 59
def prefixEnd_2439127 : Nat := 4983230072969 + 3 ^ 40 * 2439127 * 2
def baseEnd_2439127 : Nat := 1252444528359183638095165

theorem tailTrace_2439127 : CollatzResearch.WordTrace tailWord_2439127 prefixEnd_2439127 1252444528359183638095165 := by
  unfold tailWord_2439127
  simp only [CollatzResearch.WordTrace]
  refine ⟨88962270234466923571899635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59308180156311282381266423 88962270234466923571899635)
  ·
    refine ⟨133443405351700385357849453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88962270234466923571899635 133443405351700385357849453)
    ·
      refine ⟨50041277006887644509193545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133443405351700385357849453 50041277006887644509193545)
      ·
        refine ⟨37530957755165733381895159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50041277006887644509193545 37530957755165733381895159)
        ·
          refine ⟨56296436632748600072842739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37530957755165733381895159 56296436632748600072842739)
          ·
            refine ⟨84444654949122900109264109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56296436632748600072842739 84444654949122900109264109)
            ·
              refine ⟨31666745605921087540974041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84444654949122900109264109 31666745605921087540974041)
              ·
                refine ⟨23750059204440815655730531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31666745605921087540974041 23750059204440815655730531)
                ·
                  refine ⟨35625088806661223483595797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23750059204440815655730531 35625088806661223483595797)
                  ·
                    refine ⟨1669926037812244850793553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 35625088806661223483595797 1669926037812244850793553)
                    ·
                      refine ⟨1252444528359183638095165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1669926037812244850793553 1252444528359183638095165)
                      ·
                        rfl

theorem cell23_2439127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 2, 1, 6, 2].length) (baseStart_2439127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2439127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2439127 prefixEnd_2439127 := by exact prefixLift 2439127
  have htrace : WordTrace (prefixWord ++ tailWord_2439127) baseStart_2439127 baseEnd_2439127 := by
    simpa [prefixWord, tailWord_2439127, baseEnd_2439127] using wordTrace_append hprefix tailTrace_2439127
  have hstable : (prefixWord ++ tailWord_2439127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2439127).length < 2 ^ (prefixWord ++ tailWord_2439127).sum := by decide
  have hdescent : baseEnd_2439127 < baseStart_2439127 := by decide
  rcases family_descends (prefixWord ++ tailWord_2439127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2439140 : List Nat := [2, 3, 1, 1, 1, 1, 3, 1, 1, 3, 6]
def baseStart_2439140 : Nat := 118140960795 + 2439140 * 2 ^ 59
def prefixEnd_2439140 : Nat := 4983230072969 + 3 ^ 40 * 2439140 * 2
def baseEnd_2439140 : Nat := 1252451203607692087232605

theorem tailTrace_2439140 : CollatzResearch.WordTrace tailWord_2439140 prefixEnd_2439140 1252451203607692087232605 := by
  unfold tailWord_2439140
  simp only [CollatzResearch.WordTrace]
  refine ⟨44481372191709913396061437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59308496255613217861415249 44481372191709913396061437)
  ·
    refine ⟨16680514571891217523523039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44481372191709913396061437 16680514571891217523523039)
    ·
      refine ⟨25020771857836826285284559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16680514571891217523523039 25020771857836826285284559)
      ·
        refine ⟨37531157786755239427926839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25020771857836826285284559 37531157786755239427926839)
        ·
          refine ⟨56296736680132859141890259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37531157786755239427926839 56296736680132859141890259)
          ·
            refine ⟨84445105020199288712835389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56296736680132859141890259 84445105020199288712835389)
            ·
              refine ⟨31666914382574733267313271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84445105020199288712835389 31666914382574733267313271)
              ·
                refine ⟨47500371573862099900969907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31666914382574733267313271 47500371573862099900969907)
                ·
                  refine ⟨71250557360793149851454861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47500371573862099900969907 71250557360793149851454861)
                  ·
                    refine ⟨26718959010297431194295573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 71250557360793149851454861 26718959010297431194295573)
                    ·
                      refine ⟨1252451203607692087232605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26718959010297431194295573 1252451203607692087232605)
                      ·
                        rfl

theorem cell23_2439140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 1, 3, 6].length) (baseStart_2439140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2439140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2439140 prefixEnd_2439140 := by exact prefixLift 2439140
  have htrace : WordTrace (prefixWord ++ tailWord_2439140) baseStart_2439140 baseEnd_2439140 := by
    simpa [prefixWord, tailWord_2439140, baseEnd_2439140] using wordTrace_append hprefix tailTrace_2439140
  have hstable : (prefixWord ++ tailWord_2439140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2439140).length < 2 ^ (prefixWord ++ tailWord_2439140).sum := by decide
  have hdescent : baseEnd_2439140 < baseStart_2439140 := by decide
  rcases family_descends (prefixWord ++ tailWord_2439140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2439147 : List Nat := [1, 1, 1, 1, 2, 3, 1, 6, 2, 2, 3]
def baseStart_2439147 : Nat := 118140960795 + 2439147 * 2 ^ 59
def prefixEnd_2439147 : Nat := 4983230072969 + 3 ^ 40 * 2439147 * 2
def baseEnd_2439147 : Nat := 1252454797972273559845073

theorem tailTrace_2439147 : CollatzResearch.WordTrace tailWord_2439147 prefixEnd_2439147 1252454797972273559845073 := by
  unfold tailWord_2439147
  simp only [CollatzResearch.WordTrace]
  refine ⟨88962999694394466987627695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59308666462929644658418463 88962999694394466987627695)
  ·
    refine ⟨133444499541591700481441543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88962999694394466987627695 133444499541591700481441543)
    ·
      refine ⟨200166749312387550722162315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133444499541591700481441543 200166749312387550722162315)
      ·
        refine ⟨300250123968581326083243473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200166749312387550722162315 300250123968581326083243473)
        ·
          refine ⟨225187592976435994562432605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 300250123968581326083243473 225187592976435994562432605)
          ·
            refine ⟨84445347366163497960912227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 225187592976435994562432605 84445347366163497960912227)
            ·
              refine ⟨126668021049245246941368341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84445347366163497960912227 126668021049245246941368341)
              ·
                refine ⟨5937563486683370950376641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 126668021049245246941368341 5937563486683370950376641)
                ·
                  refine ⟨4453172615012528212782481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5937563486683370950376641 4453172615012528212782481)
                  ·
                    refine ⟨3339879461259396159586861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4453172615012528212782481 3339879461259396159586861)
                    ·
                      refine ⟨1252454797972273559845073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3339879461259396159586861 1252454797972273559845073)
                      ·
                        rfl

theorem cell23_2439147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 6, 2, 2, 3].length) (baseStart_2439147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2439147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2439147 prefixEnd_2439147 := by exact prefixLift 2439147
  have htrace : WordTrace (prefixWord ++ tailWord_2439147) baseStart_2439147 baseEnd_2439147 := by
    simpa [prefixWord, tailWord_2439147, baseEnd_2439147] using wordTrace_append hprefix tailTrace_2439147
  have hstable : (prefixWord ++ tailWord_2439147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2439147).length < 2 ^ (prefixWord ++ tailWord_2439147).sum := by decide
  have hdescent : baseEnd_2439147 < baseStart_2439147 := by decide
  rcases family_descends (prefixWord ++ tailWord_2439147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2439247 : List Nat := [1, 1, 2, 1, 1, 2, 2, 6, 1, 2, 4]
def baseStart_2439247 : Nat := 118140960795 + 2439247 * 2 ^ 59
def prefixEnd_2439247 : Nat := 4983230072969 + 3 ^ 40 * 2439247 * 2
def baseEnd_2439247 : Nat := 1252506146037723168594613

theorem tailTrace_2439247 : CollatzResearch.WordTrace tailWord_2439247 prefixEnd_2439247 1252506146037723168594613 := by
  unfold tailWord_2439247
  simp only [CollatzResearch.WordTrace]
  refine ⟨88966646994032184066267995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59311097996021456044178663 88966646994032184066267995)
  ·
    refine ⟨133449970491048276099401993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88966646994032184066267995 133449970491048276099401993)
    ·
      refine ⟨100087477868286207074551495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133449970491048276099401993 100087477868286207074551495)
      ·
        refine ⟨150131216802429310611827243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100087477868286207074551495 150131216802429310611827243)
        ·
          refine ⟨225196825203643965917740865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150131216802429310611827243 225196825203643965917740865)
          ·
            refine ⟨168897618902732974438305649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 225196825203643965917740865 168897618902732974438305649)
            ·
              refine ⟨126673214177049730828729237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 168897618902732974438305649 126673214177049730828729237)
              ·
                refine ⟨5937806914549206132596683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 126673214177049730828729237 5937806914549206132596683)
                ·
                  refine ⟨8906710371823809198895025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5937806914549206132596683 8906710371823809198895025)
                  ·
                    refine ⟨6680032778867856899171269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8906710371823809198895025 6680032778867856899171269)
                    ·
                      refine ⟨1252506146037723168594613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6680032778867856899171269 1252506146037723168594613)
                      ·
                        rfl

theorem cell23_2439247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 6, 1, 2, 4].length) (baseStart_2439247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2439247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2439247 prefixEnd_2439247 := by exact prefixLift 2439247
  have htrace : WordTrace (prefixWord ++ tailWord_2439247) baseStart_2439247 baseEnd_2439247 := by
    simpa [prefixWord, tailWord_2439247, baseEnd_2439247] using wordTrace_append hprefix tailTrace_2439247
  have hstable : (prefixWord ++ tailWord_2439247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2439247).length < 2 ^ (prefixWord ++ tailWord_2439247).sum := by decide
  have hdescent : baseEnd_2439247 < baseStart_2439247 := by decide
  rcases family_descends (prefixWord ++ tailWord_2439247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2439317 : List Nat := [1, 3, 2, 1, 1, 1, 3, 1, 4, 6]
def baseStart_2439317 : Nat := 118140960795 + 2439317 * 2 ^ 59
def prefixEnd_2439317 : Nat := 4983230072969 + 3 ^ 40 * 2439317 * 2
def baseEnd_2439317 : Nat := 417514029894512631573097

theorem tailTrace_2439317 : CollatzResearch.WordTrace tailWord_2439317 prefixEnd_2439317 417514029894512631573097 := by
  unfold tailWord_2439317
  simp only [CollatzResearch.WordTrace]
  refine ⟨88969200103778586021316205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59312800069185724014210803 88969200103778586021316205)
  ·
    refine ⟨33363450038916969757993577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88969200103778586021316205 33363450038916969757993577)
    ·
      refine ⟨25022587529187727318495183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33363450038916969757993577 25022587529187727318495183)
      ·
        refine ⟨37533881293781590977742775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25022587529187727318495183 37533881293781590977742775)
        ·
          refine ⟨56300821940672386466614163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37533881293781590977742775 56300821940672386466614163)
          ·
            refine ⟨84451232911008579699921245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56300821940672386466614163 84451232911008579699921245)
            ·
              refine ⟨31669212341628217387470467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84451232911008579699921245 31669212341628217387470467)
              ·
                refine ⟨47503818512442326081205701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31669212341628217387470467 47503818512442326081205701)
                ·
                  refine ⟨8906965971082936140226069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47503818512442326081205701 8906965971082936140226069)
                  ·
                    refine ⟨417514029894512631573097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8906965971082936140226069 417514029894512631573097)
                    ·
                      rfl

theorem cell23_2439317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 4, 6].length) (baseStart_2439317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2439317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2439317 prefixEnd_2439317 := by exact prefixLift 2439317
  have htrace : WordTrace (prefixWord ++ tailWord_2439317) baseStart_2439317 baseEnd_2439317 := by
    simpa [prefixWord, tailWord_2439317, baseEnd_2439317] using wordTrace_append hprefix tailTrace_2439317
  have hstable : (prefixWord ++ tailWord_2439317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2439317).length < 2 ^ (prefixWord ++ tailWord_2439317).sum := by decide
  have hdescent : baseEnd_2439317 < baseStart_2439317 := by decide
  rcases family_descends (prefixWord ++ tailWord_2439317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2439335 : List Nat := [1, 1, 6, 2, 3, 1, 1, 1, 1, 3, 3]
def baseStart_2439335 : Nat := 118140960795 + 2439335 * 2 ^ 59
def prefixEnd_2439335 : Nat := 4983230072969 + 3 ^ 40 * 2439335 * 2
def baseEnd_2439335 : Nat := 1252551332335318824294209

theorem tailTrace_2439335 : CollatzResearch.WordTrace tailWord_2439335 prefixEnd_2439335 1252551332335318824294209 := by
  unfold tailWord_2439335
  simp only [CollatzResearch.WordTrace]
  refine ⟨88969856617713375095471459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59313237745142250063647639 88969856617713375095471459)
  ·
    refine ⟨133454784926570062643207189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88969856617713375095471459 133454784926570062643207189)
    ·
      refine ⟨6255693043432971686400337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 133454784926570062643207189 6255693043432971686400337)
      ·
        refine ⟨4691769782574728764800253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6255693043432971686400337 4691769782574728764800253)
        ·
          refine ⟨1759413668465523286800095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4691769782574728764800253 1759413668465523286800095)
          ·
            refine ⟨2639120502698284930200143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1759413668465523286800095 2639120502698284930200143)
            ·
              refine ⟨3958680754047427395300215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2639120502698284930200143 3958680754047427395300215)
              ·
                refine ⟨5938021131071141092950323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3958680754047427395300215 5938021131071141092950323)
                ·
                  refine ⟨8907031696606711639425485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5938021131071141092950323 8907031696606711639425485)
                  ·
                    refine ⟨3340136886227516864784557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8907031696606711639425485 3340136886227516864784557)
                    ·
                      refine ⟨1252551332335318824294209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3340136886227516864784557 1252551332335318824294209)
                      ·
                        rfl

theorem cell23_2439335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 1, 1, 3, 3].length) (baseStart_2439335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2439335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2439335 prefixEnd_2439335 := by exact prefixLift 2439335
  have htrace : WordTrace (prefixWord ++ tailWord_2439335) baseStart_2439335 baseEnd_2439335 := by
    simpa [prefixWord, tailWord_2439335, baseEnd_2439335] using wordTrace_append hprefix tailTrace_2439335
  have hstable : (prefixWord ++ tailWord_2439335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2439335).length < 2 ^ (prefixWord ++ tailWord_2439335).sum := by decide
  have hdescent : baseEnd_2439335 < baseStart_2439335 := by decide
  rcases family_descends (prefixWord ++ tailWord_2439335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2439345 : List Nat := [1, 2, 2, 5, 2, 1, 2, 2, 1, 3, 2]
def baseStart_2439345 : Nat := 118140960795 + 2439345 * 2 ^ 59
def prefixEnd_2439345 : Nat := 4983230072969 + 3 ^ 40 * 2439345 * 2
def baseEnd_2439345 : Nat := 1252556467141863785169163

theorem tailTrace_2439345 : CollatzResearch.WordTrace tailWord_2439345 prefixEnd_2439345 1252556467141863785169163 := by
  unfold tailWord_2439345
  simp only [CollatzResearch.WordTrace]
  refine ⟨88970221347677146803335489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59313480898451431202223659 88970221347677146803335489)
  ·
    refine ⟨66727666010757860102501617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88970221347677146803335489 66727666010757860102501617)
    ·
      refine ⟨50045749508068395076876213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66727666010757860102501617 50045749508068395076876213)
      ·
        refine ⟨4691789016381412038457145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 50045749508068395076876213 4691789016381412038457145)
        ·
          refine ⟨3518841762286059028842859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4691789016381412038457145 3518841762286059028842859)
          ·
            refine ⟨5278262643429088543264289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3518841762286059028842859 5278262643429088543264289)
            ·
              refine ⟨3958696982571816407448217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5278262643429088543264289 3958696982571816407448217)
              ·
                refine ⟨2969022736928862305586163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3958696982571816407448217 2969022736928862305586163)
                ·
                  refine ⟨4453534105393293458379245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2969022736928862305586163 4453534105393293458379245)
                  ·
                    refine ⟨1670075289522485046892217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4453534105393293458379245 1670075289522485046892217)
                    ·
                      refine ⟨1252556467141863785169163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1670075289522485046892217 1252556467141863785169163)
                      ·
                        rfl

theorem cell23_2439345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 2, 1, 3, 2].length) (baseStart_2439345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2439345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2439345 prefixEnd_2439345 := by exact prefixLift 2439345
  have htrace : WordTrace (prefixWord ++ tailWord_2439345) baseStart_2439345 baseEnd_2439345 := by
    simpa [prefixWord, tailWord_2439345, baseEnd_2439345] using wordTrace_append hprefix tailTrace_2439345
  have hstable : (prefixWord ++ tailWord_2439345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2439345).length < 2 ^ (prefixWord ++ tailWord_2439345).sum := by decide
  have hdescent : baseEnd_2439345 < baseStart_2439345 := by decide
  rcases family_descends (prefixWord ++ tailWord_2439345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2439362 : List Nat := [3, 5, 1, 1, 1, 1, 2, 3, 1, 3, 2]
def baseStart_2439362 : Nat := 118140960795 + 2439362 * 2 ^ 59
def prefixEnd_2439362 : Nat := 4983230072969 + 3 ^ 40 * 2439362 * 2
def baseEnd_2439362 : Nat := 1252565196312990218656585

theorem tailTrace_2439362 : CollatzResearch.WordTrace tailWord_2439362 prefixEnd_2439362 1252565196312990218656585 := by
  unfold tailWord_2439362
  simp only [CollatzResearch.WordTrace]
  refine ⟨22242710347153889676676085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59313894259077039137802893 22242710347153889676676085)
  ·
    refine ⟨2085254095045677157188383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22242710347153889676676085 2085254095045677157188383)
    ·
      refine ⟨3127881142568515735782575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2085254095045677157188383 3127881142568515735782575)
      ·
        refine ⟨4691821713852773603673863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3127881142568515735782575 4691821713852773603673863)
        ·
          refine ⟨7037732570779160405510795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4691821713852773603673863 7037732570779160405510795)
          ·
            refine ⟨10556598856168740608266193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7037732570779160405510795 10556598856168740608266193)
            ·
              refine ⟨7917449142126555456199645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10556598856168740608266193 7917449142126555456199645)
              ·
                refine ⟨2969043428297458296074867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7917449142126555456199645 2969043428297458296074867)
                ·
                  refine ⟨4453565142446187444112301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2969043428297458296074867 4453565142446187444112301)
                  ·
                    refine ⟨1670086928417320291542113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4453565142446187444112301 1670086928417320291542113)
                    ·
                      refine ⟨1252565196312990218656585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1670086928417320291542113 1252565196312990218656585)
                      ·
                        rfl

theorem cell23_2439362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 3, 1, 3, 2].length) (baseStart_2439362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2439362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2439362 prefixEnd_2439362 := by exact prefixLift 2439362
  have htrace : WordTrace (prefixWord ++ tailWord_2439362) baseStart_2439362 baseEnd_2439362 := by
    simpa [prefixWord, tailWord_2439362, baseEnd_2439362] using wordTrace_append hprefix tailTrace_2439362
  have hstable : (prefixWord ++ tailWord_2439362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2439362).length < 2 ^ (prefixWord ++ tailWord_2439362).sum := by decide
  have hdescent : baseEnd_2439362 < baseStart_2439362 := by decide
  rcases family_descends (prefixWord ++ tailWord_2439362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2439367 : List Nat := [1, 1, 4, 1, 1, 1, 1, 1, 2, 4, 6]
def baseStart_2439367 : Nat := 118140960795 + 2439367 * 2 ^ 59
def prefixEnd_2439367 : Nat := 4983230072969 + 3 ^ 40 * 2439367 * 2
def baseEnd_2439367 : Nat := 1252567763716262699094061

theorem tailTrace_2439367 : CollatzResearch.WordTrace tailWord_2439367 prefixEnd_2439367 1252567763716262699094061 := by
  unfold tailWord_2439367
  simp only [CollatzResearch.WordTrace]
  refine ⟨88971023753597444560636355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59314015835731629707090903 88971023753597444560636355)
  ·
    refine ⟨133456535630396166840954533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88971023753597444560636355 133456535630396166840954533)
    ·
      refine ⟨25023100430699281282678975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 133456535630396166840954533 25023100430699281282678975)
      ·
        refine ⟨37534650646048921924018463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25023100430699281282678975 37534650646048921924018463)
        ·
          refine ⟨56301975969073382886027695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37534650646048921924018463 56301975969073382886027695)
          ·
            refine ⟨84452963953610074329041543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56301975969073382886027695 84452963953610074329041543)
            ·
              refine ⟨126679445930415111493562315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84452963953610074329041543 126679445930415111493562315)
              ·
                refine ⟨190019168895622667240343473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126679445930415111493562315 190019168895622667240343473)
                ·
                  refine ⟨142514376671717000430257605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 190019168895622667240343473 142514376671717000430257605)
                  ·
                    refine ⟨26721445625946937580673301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 142514376671717000430257605 26721445625946937580673301)
                    ·
                      refine ⟨1252567763716262699094061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26721445625946937580673301 1252567763716262699094061)
                      ·
                        rfl

theorem cell23_2439367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 4, 6].length) (baseStart_2439367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2439367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2439367 prefixEnd_2439367 := by exact prefixLift 2439367
  have htrace : WordTrace (prefixWord ++ tailWord_2439367) baseStart_2439367 baseEnd_2439367 := by
    simpa [prefixWord, tailWord_2439367, baseEnd_2439367] using wordTrace_append hprefix tailTrace_2439367
  have hstable : (prefixWord ++ tailWord_2439367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2439367).length < 2 ^ (prefixWord ++ tailWord_2439367).sum := by decide
  have hdescent : baseEnd_2439367 < baseStart_2439367 := by decide
  rcases family_descends (prefixWord ++ tailWord_2439367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2439387 : List Nat := [1, 1, 1, 1, 1, 1, 1, 7, 1, 1, 7]
def baseStart_2439387 : Nat := 118140960795 + 2439387 * 2 ^ 59
def prefixEnd_2439387 : Nat := 4983230072969 + 3 ^ 40 * 2439387 * 2
def baseEnd_2439387 : Nat := 1252578033329352620843969

theorem tailTrace_2439387 : CollatzResearch.WordTrace tailWord_2439387 prefixEnd_2439387 1252578033329352620843969 := by
  unfold tailWord_2439387
  simp only [CollatzResearch.WordTrace]
  refine ⟨88971753213524987976364415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59314502142349991984242943 88971753213524987976364415)
  ·
    refine ⟨133457629820287481964546623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88971753213524987976364415 133457629820287481964546623)
    ·
      refine ⟨200186444730431222946819935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133457629820287481964546623 200186444730431222946819935)
      ·
        refine ⟨300279667095646834420229903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200186444730431222946819935 300279667095646834420229903)
        ·
          refine ⟨450419500643470251630344855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 300279667095646834420229903 450419500643470251630344855)
          ·
            refine ⟨675629250965205377445517283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 450419500643470251630344855 675629250965205377445517283)
            ·
              refine ⟨1013443876447808066168275925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 675629250965205377445517283 1013443876447808066168275925)
              ·
                refine ⟨23752590854245501550818967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1013443876447808066168275925 23752590854245501550818967)
                ·
                  refine ⟨35628886281368252326228451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23752590854245501550818967 35628886281368252326228451)
                  ·
                    refine ⟨53443329422052378489342677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35628886281368252326228451 53443329422052378489342677)
                    ·
                      refine ⟨1252578033329352620843969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 53443329422052378489342677 1252578033329352620843969)
                      ·
                        rfl

theorem cell23_2439387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 1, 1, 7].length) (baseStart_2439387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2439387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2439387 prefixEnd_2439387 := by exact prefixLift 2439387
  have htrace : WordTrace (prefixWord ++ tailWord_2439387) baseStart_2439387 baseEnd_2439387 := by
    simpa [prefixWord, tailWord_2439387, baseEnd_2439387] using wordTrace_append hprefix tailTrace_2439387
  have hstable : (prefixWord ++ tailWord_2439387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2439387).length < 2 ^ (prefixWord ++ tailWord_2439387).sum := by decide
  have hdescent : baseEnd_2439387 < baseStart_2439387 := by decide
  rcases family_descends (prefixWord ++ tailWord_2439387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2439458 : List Nat := [3, 3, 1, 1, 3, 2, 1, 2, 3, 4]
def baseStart_2439458 : Nat := 118140960795 + 2439458 * 2 ^ 59
def prefixEnd_2439458 : Nat := 4983230072969 + 3 ^ 40 * 2439458 * 2
def baseEnd_2439458 : Nat := 417538163485273947685381

theorem tailTrace_2439458 : CollatzResearch.WordTrace tailWord_2439458 prefixEnd_2439458 417538163485273947685381 := by
  unfold tailWord_2439458
  simp only [CollatzResearch.WordTrace]
  refine ⟨22243585699066941775549757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59316228530845178068132685 22243585699066941775549757)
  ·
    refine ⟨8341344637150103165831159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22243585699066941775549757 8341344637150103165831159)
    ·
      refine ⟨12512016955725154748746739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8341344637150103165831159 12512016955725154748746739)
      ·
        refine ⟨18768025433587732123120109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12512016955725154748746739 18768025433587732123120109)
        ·
          refine ⟨7038009537595399546170041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18768025433587732123120109 7038009537595399546170041)
          ·
            refine ⟨5278507153196549659627531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7038009537595399546170041 5278507153196549659627531)
            ·
              refine ⟨7917760729794824489441297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5278507153196549659627531 7917760729794824489441297)
              ·
                refine ⟨5938320547346118367080973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7917760729794824489441297 5938320547346118367080973)
                ·
                  refine ⟨2226870205254794387655365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5938320547346118367080973 2226870205254794387655365)
                  ·
                    refine ⟨417538163485273947685381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2226870205254794387655365 417538163485273947685381)
                    ·
                      rfl

theorem cell23_2439458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 2, 3, 4].length) (baseStart_2439458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2439458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2439458 prefixEnd_2439458 := by exact prefixLift 2439458
  have htrace : WordTrace (prefixWord ++ tailWord_2439458) baseStart_2439458 baseEnd_2439458 := by
    simpa [prefixWord, tailWord_2439458, baseEnd_2439458] using wordTrace_append hprefix tailTrace_2439458
  have hstable : (prefixWord ++ tailWord_2439458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2439458).length < 2 ^ (prefixWord ++ tailWord_2439458).sum := by decide
  have hdescent : baseEnd_2439458 < baseStart_2439458 := by decide
  rcases family_descends (prefixWord ++ tailWord_2439458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2439508 : List Nat := [2, 4, 1, 1, 2, 2, 1, 2, 1, 5, 2]
def baseStart_2439508 : Nat := 118140960795 + 2439508 * 2 ^ 59
def prefixEnd_2439508 : Nat := 4983230072969 + 3 ^ 40 * 2439508 * 2
def baseEnd_2439508 : Nat := 1252640164488546647430913

theorem tailTrace_2439508 : CollatzResearch.WordTrace tailWord_2439508 prefixEnd_2439508 1252640164488546647430913 := by
  unfold tailWord_2439508
  simp only [CollatzResearch.WordTrace]
  refine ⟨44488083223043312820759589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59317444297391083761012785 44488083223043312820759589)
  ·
    refine ⟨8341515604320621153892423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44488083223043312820759589 8341515604320621153892423)
    ·
      refine ⟨12512273406480931730838635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8341515604320621153892423 12512273406480931730838635)
      ·
        refine ⟨18768410109721397596257953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12512273406480931730838635 18768410109721397596257953)
        ·
          refine ⟨14076307582291048197193465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18768410109721397596257953 14076307582291048197193465)
          ·
            refine ⟨10557230686718286147895099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14076307582291048197193465 10557230686718286147895099)
            ·
              refine ⟨15835846030077429221842649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10557230686718286147895099 15835846030077429221842649)
              ·
                refine ⟨11876884522558071916381987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15835846030077429221842649 11876884522558071916381987)
                ·
                  refine ⟨17815326783837107874572981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11876884522558071916381987 17815326783837107874572981)
                  ·
                    refine ⟨1670186885984728863241217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17815326783837107874572981 1670186885984728863241217)
                    ·
                      refine ⟨1252640164488546647430913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1670186885984728863241217 1252640164488546647430913)
                      ·
                        rfl

theorem cell23_2439508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 2, 1, 5, 2].length) (baseStart_2439508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2439508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2439508 prefixEnd_2439508 := by exact prefixLift 2439508
  have htrace : WordTrace (prefixWord ++ tailWord_2439508) baseStart_2439508 baseEnd_2439508 := by
    simpa [prefixWord, tailWord_2439508, baseEnd_2439508] using wordTrace_append hprefix tailTrace_2439508
  have hstable : (prefixWord ++ tailWord_2439508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2439508).length < 2 ^ (prefixWord ++ tailWord_2439508).sum := by decide
  have hdescent : baseEnd_2439508 < baseStart_2439508 := by decide
  rcases family_descends (prefixWord ++ tailWord_2439508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2439538 : List Nat := [3, 2, 1, 2, 1, 3, 2, 3, 1, 1, 4]
def baseStart_2439538 : Nat := 118140960795 + 2439538 * 2 ^ 59
def prefixEnd_2439538 : Nat := 4983230072969 + 3 ^ 40 * 2439538 * 2
def baseEnd_2439538 : Nat := 1252655568908181530055775

theorem tailTrace_2439538 : CollatzResearch.WordTrace tailWord_2439538 prefixEnd_2439538 1252655568908181530055775 := by
  unfold tailWord_2439538
  simp only [CollatzResearch.WordTrace]
  refine ⟨22244315158994485191277817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59318173757318627176740845 22244315158994485191277817)
  ·
    refine ⟨16683236369245863893458363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22244315158994485191277817 16683236369245863893458363)
    ·
      refine ⟨25024854553868795840187545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16683236369245863893458363 25024854553868795840187545)
      ·
        refine ⟨18768640915401596880140659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25024854553868795840187545 18768640915401596880140659)
        ·
          refine ⟨28152961373102395320210989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18768640915401596880140659 28152961373102395320210989)
          ·
            refine ⟨10557360514913398245079121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28152961373102395320210989 10557360514913398245079121)
            ·
              refine ⟨7918020386185048683809341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10557360514913398245079121 7918020386185048683809341)
              ·
                refine ⟨2969257644819393256428503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7918020386185048683809341 2969257644819393256428503)
                ·
                  refine ⟨4453886467229089884642755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2969257644819393256428503 4453886467229089884642755)
                  ·
                    refine ⟨6680829700843634826964133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4453886467229089884642755 6680829700843634826964133)
                    ·
                      refine ⟨1252655568908181530055775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6680829700843634826964133 1252655568908181530055775)
                      ·
                        rfl

theorem cell23_2439538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 3, 1, 1, 4].length) (baseStart_2439538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2439538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2439538 prefixEnd_2439538 := by exact prefixLift 2439538
  have htrace : WordTrace (prefixWord ++ tailWord_2439538) baseStart_2439538 baseEnd_2439538 := by
    simpa [prefixWord, tailWord_2439538, baseEnd_2439538] using wordTrace_append hprefix tailTrace_2439538
  have hstable : (prefixWord ++ tailWord_2439538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2439538).length < 2 ^ (prefixWord ++ tailWord_2439538).sum := by decide
  have hdescent : baseEnd_2439538 < baseStart_2439538 := by decide
  rcases family_descends (prefixWord ++ tailWord_2439538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2439561 : List Nat := [1, 2, 1, 1, 6, 2, 2, 8]
def baseStart_2439561 : Nat := 118140960795 + 2439561 * 2 ^ 59
def prefixEnd_2439561 : Nat := 4983230072969 + 3 ^ 40 * 2439561 * 2
def baseEnd_2439561 : Nat := 46395088109749442224747

theorem tailTrace_2439561 : CollatzResearch.WordTrace tailWord_2439561 prefixEnd_2439561 46395088109749442224747 := by
  unfold tailWord_2439561
  simp only [CollatzResearch.WordTrace]
  refine ⟨88978099514894615693198537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59318733009929743795465691 88978099514894615693198537)
  ·
    refine ⟨66733574636170961769898903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88978099514894615693198537 66733574636170961769898903)
    ·
      refine ⟨100100361954256442654848355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66733574636170961769898903 100100361954256442654848355)
      ·
        refine ⟨150150542931384663982272533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100100361954256442654848355 150150542931384663982272533)
        ·
          refine ⟨7038306699908656124169025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 150150542931384663982272533 7038306699908656124169025)
          ·
            refine ⟨5278730024931492093126769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7038306699908656124169025 5278730024931492093126769)
            ·
              refine ⟨3959047518698619069845077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5278730024931492093126769 3959047518698619069845077)
              ·
                refine ⟨46395088109749442224747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3959047518698619069845077 46395088109749442224747)
                ·
                  rfl

theorem cell23_2439561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 8].length) (baseStart_2439561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2439561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2439561 prefixEnd_2439561 := by exact prefixLift 2439561
  have htrace : WordTrace (prefixWord ++ tailWord_2439561) baseStart_2439561 baseEnd_2439561 := by
    simpa [prefixWord, tailWord_2439561, baseEnd_2439561] using wordTrace_append hprefix tailTrace_2439561
  have hstable : (prefixWord ++ tailWord_2439561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2439561).length < 2 ^ (prefixWord ++ tailWord_2439561).sum := by decide
  have hdescent : baseEnd_2439561 < baseStart_2439561 := by decide
  rcases family_descends (prefixWord ++ tailWord_2439561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2439572 : List Nat := [2, 4, 2, 1, 3, 2, 1, 2, 1, 1, 4]
def baseStart_2439572 : Nat := 118140960795 + 2439572 * 2 ^ 59
def prefixEnd_2439572 : Nat := 4983230072969 + 3 ^ 40 * 2439572 * 2
def baseEnd_2439572 : Nat := 1252673027250434397030619

theorem tailTrace_2439572 : CollatzResearch.WordTrace tailWord_2439572 prefixEnd_2439572 1252673027250434397030619 := by
  unfold tailWord_2439572
  simp only [CollatzResearch.WordTrace]
  refine ⟨44489250358927382285924485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59319000478569843047899313 44489250358927382285924485)
  ·
    refine ⟨8341734442298884178610841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44489250358927382285924485 8341734442298884178610841)
    ·
      refine ⟨6256300831724163133958131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8341734442298884178610841 6256300831724163133958131)
      ·
        refine ⟨9384451247586244700937197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6256300831724163133958131 9384451247586244700937197)
        ·
          refine ⟨3519169217844841762851449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9384451247586244700937197 3519169217844841762851449)
          ·
            refine ⟨2639376913383631322138587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3519169217844841762851449 2639376913383631322138587)
            ·
              refine ⟨3959065370075446983207881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2639376913383631322138587 3959065370075446983207881)
              ·
                refine ⟨2969299027556585237405911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3959065370075446983207881 2969299027556585237405911)
                ·
                  refine ⟨4453948541334877856108867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2969299027556585237405911 4453948541334877856108867)
                  ·
                    refine ⟨6680922812002316784163301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4453948541334877856108867 6680922812002316784163301)
                    ·
                      refine ⟨1252673027250434397030619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6680922812002316784163301 1252673027250434397030619)
                      ·
                        rfl

theorem cell23_2439572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 2, 1, 1, 4].length) (baseStart_2439572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2439572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2439572 prefixEnd_2439572 := by exact prefixLift 2439572
  have htrace : WordTrace (prefixWord ++ tailWord_2439572) baseStart_2439572 baseEnd_2439572 := by
    simpa [prefixWord, tailWord_2439572, baseEnd_2439572] using wordTrace_append hprefix tailTrace_2439572
  have hstable : (prefixWord ++ tailWord_2439572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2439572).length < 2 ^ (prefixWord ++ tailWord_2439572).sum := by decide
  have hdescent : baseEnd_2439572 < baseStart_2439572 := by decide
  rcases family_descends (prefixWord ++ tailWord_2439572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2439585 : List Nat := [1, 2, 3, 5, 1, 1, 1, 2, 1, 2, 4]
def baseStart_2439585 : Nat := 118140960795 + 2439585 * 2 ^ 59
def prefixEnd_2439585 : Nat := 4983230072969 + 3 ^ 40 * 2439585 * 2
def baseEnd_2439585 : Nat := 1252679702498942846168059

theorem tailTrace_2439585 : CollatzResearch.WordTrace tailWord_2439585 prefixEnd_2439585 1252679702498942846168059 := by
  unfold tailWord_2439585
  simp only [CollatzResearch.WordTrace]
  refine ⟨88978974866807667792072209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59319316577871778528048139 88978974866807667792072209)
  ·
    refine ⟨66734231150105750844054157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88978974866807667792072209 66734231150105750844054157)
    ·
      refine ⟨25025336681289656566520309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66734231150105750844054157 25025336681289656566520309)
      ·
        refine ⟨2346125313870905303111279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25025336681289656566520309 2346125313870905303111279)
        ·
          refine ⟨3519187970806357954666919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2346125313870905303111279 3519187970806357954666919)
          ·
            refine ⟨5278781956209536932000379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3519187970806357954666919 5278781956209536932000379)
            ·
              refine ⟨7918172934314305398000569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5278781956209536932000379 7918172934314305398000569)
              ·
                refine ⟨5938629700735729048500427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7918172934314305398000569 5938629700735729048500427)
                ·
                  refine ⟨8907944551103593572750641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5938629700735729048500427 8907944551103593572750641)
                  ·
                    refine ⟨6680958413327695179562981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8907944551103593572750641 6680958413327695179562981)
                    ·
                      refine ⟨1252679702498942846168059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6680958413327695179562981 1252679702498942846168059)
                      ·
                        rfl

theorem cell23_2439585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_2439585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2439585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2439585 prefixEnd_2439585 := by exact prefixLift 2439585
  have htrace : WordTrace (prefixWord ++ tailWord_2439585) baseStart_2439585 baseEnd_2439585 := by
    simpa [prefixWord, tailWord_2439585, baseEnd_2439585] using wordTrace_append hprefix tailTrace_2439585
  have hstable : (prefixWord ++ tailWord_2439585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2439585).length < 2 ^ (prefixWord ++ tailWord_2439585).sum := by decide
  have hdescent : baseEnd_2439585 < baseStart_2439585 := by decide
  rcases family_descends (prefixWord ++ tailWord_2439585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2439588 : List Nat := [2, 3, 1, 2, 1, 1, 2, 1, 6, 1, 3]
def baseStart_2439588 : Nat := 118140960795 + 2439588 * 2 ^ 59
def prefixEnd_2439588 : Nat := 4983230072969 + 3 ^ 40 * 2439588 * 2
def baseEnd_2439588 : Nat := 1252681242940906334430545

theorem tailTrace_2439588 : CollatzResearch.WordTrace tailWord_2439588 prefixEnd_2439588 1252681242940906334430545 := by
  unfold tailWord_2439588
  simp only [CollatzResearch.WordTrace]
  refine ⟨44489542142898399652215709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59319389523864532869620945 44489542142898399652215709)
  ·
    refine ⟨16683578303586899869580891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44489542142898399652215709 16683578303586899869580891)
    ·
      refine ⟨25025367455380349804371337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16683578303586899869580891 25025367455380349804371337)
      ·
        refine ⟨18769025591535262353278503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25025367455380349804371337 18769025591535262353278503)
        ·
          refine ⟨28153538387302893529917755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18769025591535262353278503 28153538387302893529917755)
          ·
            refine ⟨42230307580954340294876633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28153538387302893529917755 42230307580954340294876633)
            ·
              refine ⟨31672730685715755221157475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42230307580954340294876633 31672730685715755221157475)
              ·
                refine ⟨47509096028573632831736213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31672730685715755221157475 47509096028573632831736213)
                ·
                  refine ⟨2226988876339389038987635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 47509096028573632831736213 2226988876339389038987635)
                  ·
                    refine ⟨3340483314509083558481453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2226988876339389038987635 3340483314509083558481453)
                    ·
                      refine ⟨1252681242940906334430545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3340483314509083558481453 1252681242940906334430545)
                      ·
                        rfl

theorem cell23_2439588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 6, 1, 3].length) (baseStart_2439588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2439588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2439588 prefixEnd_2439588 := by exact prefixLift 2439588
  have htrace : WordTrace (prefixWord ++ tailWord_2439588) baseStart_2439588 baseEnd_2439588 := by
    simpa [prefixWord, tailWord_2439588, baseEnd_2439588] using wordTrace_append hprefix tailTrace_2439588
  have hstable : (prefixWord ++ tailWord_2439588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2439588).length < 2 ^ (prefixWord ++ tailWord_2439588).sum := by decide
  have hdescent : baseEnd_2439588 < baseStart_2439588 := by decide
  rcases family_descends (prefixWord ++ tailWord_2439588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2439631 : List Nat := [1, 1, 2, 1, 1, 4, 1, 1, 4, 4, 3]
def baseStart_2439631 : Nat := 118140960795 + 2439631 * 2 ^ 59
def prefixEnd_2439631 : Nat := 4983230072969 + 3 ^ 40 * 2439631 * 2
def baseEnd_2439631 : Nat := 1252703322609049666192847

theorem tailTrace_2439631 : CollatzResearch.WordTrace tailWord_2439631 prefixEnd_2439631 1252703322609049666192847 := by
  unfold tailWord_2439631
  simp only [CollatzResearch.WordTrace]
  refine ⟨88980652624641017648246747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59320435083094011765497831 88980652624641017648246747)
  ·
    refine ⟨133470978936961526472370121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88980652624641017648246747 133470978936961526472370121)
    ·
      refine ⟨100103234202721144854277591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133470978936961526472370121 100103234202721144854277591)
      ·
        refine ⟨150154851304081717281416387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100103234202721144854277591 150154851304081717281416387)
        ·
          refine ⟨225232276956122575922124581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150154851304081717281416387 225232276956122575922124581)
          ·
            refine ⟨42231051929272982985398359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 225232276956122575922124581 42231051929272982985398359)
            ·
              refine ⟨63346577893909474478097539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42231051929272982985398359 63346577893909474478097539)
              ·
                refine ⟨95019866840864211717146309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63346577893909474478097539 95019866840864211717146309)
                ·
                  refine ⟨17816225032662039696964933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 95019866840864211717146309 17816225032662039696964933)
                  ·
                    refine ⟨3340542193624132443180925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17816225032662039696964933 3340542193624132443180925)
                    ·
                      refine ⟨1252703322609049666192847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3340542193624132443180925 1252703322609049666192847)
                      ·
                        rfl

theorem cell23_2439631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 4, 4, 3].length) (baseStart_2439631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2439631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2439631 prefixEnd_2439631 := by exact prefixLift 2439631
  have htrace : WordTrace (prefixWord ++ tailWord_2439631) baseStart_2439631 baseEnd_2439631 := by
    simpa [prefixWord, tailWord_2439631, baseEnd_2439631] using wordTrace_append hprefix tailTrace_2439631
  have hstable : (prefixWord ++ tailWord_2439631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2439631).length < 2 ^ (prefixWord ++ tailWord_2439631).sum := by decide
  have hdescent : baseEnd_2439631 < baseStart_2439631 := by decide
  rcases family_descends (prefixWord ++ tailWord_2439631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2439638 : List Nat := [5, 2, 1, 1, 1, 1, 1, 2, 1, 8]
def baseStart_2439638 : Nat := 118140960795 + 2439638 * 2 ^ 59
def prefixEnd_2439638 : Nat := 4983230072969 + 3 ^ 40 * 2439638 * 2
def baseEnd_2439638 : Nat := 417568972324543712935105

theorem tailTrace_2439638 : CollatzResearch.WordTrace tailWord_2439638 prefixEnd_2439638 417568972324543712935105 := by
  unfold tailWord_2439638
  simp only [CollatzResearch.WordTrace]
  refine ⟨5561306745975978615234473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 59320605290410438562501045 5561306745975978615234473)
  ·
    refine ⟨4170980059481983961425855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5561306745975978615234473 4170980059481983961425855)
    ·
      refine ⟨6256470089222975942138783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4170980059481983961425855 6256470089222975942138783)
      ·
        refine ⟨9384705133834463913208175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6256470089222975942138783 9384705133834463913208175)
        ·
          refine ⟨14077057700751695869812263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9384705133834463913208175 14077057700751695869812263)
          ·
            refine ⟨21115586551127543804718395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14077057700751695869812263 21115586551127543804718395)
            ·
              refine ⟨31673379826691315707077593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21115586551127543804718395 31673379826691315707077593)
              ·
                refine ⟨23755034870018486780308195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31673379826691315707077593 23755034870018486780308195)
                ·
                  refine ⟨35632552305027730170462293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23755034870018486780308195 35632552305027730170462293)
                  ·
                    refine ⟨417568972324543712935105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 35632552305027730170462293 417568972324543712935105)
                    ·
                      rfl

theorem cell23_2439638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_2439638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2439638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2439638 prefixEnd_2439638 := by exact prefixLift 2439638
  have htrace : WordTrace (prefixWord ++ tailWord_2439638) baseStart_2439638 baseEnd_2439638 := by
    simpa [prefixWord, tailWord_2439638, baseEnd_2439638] using wordTrace_append hprefix tailTrace_2439638
  have hstable : (prefixWord ++ tailWord_2439638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2439638).length < 2 ^ (prefixWord ++ tailWord_2439638).sum := by decide
  have hdescent : baseEnd_2439638 < baseStart_2439638 := by decide
  rcases family_descends (prefixWord ++ tailWord_2439638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2439641 : List Nat := [1, 2, 1, 2, 4, 1, 1, 2, 1, 4, 4]
def baseStart_2439641 : Nat := 118140960795 + 2439641 * 2 ^ 59
def prefixEnd_2439641 : Nat := 4983230072969 + 3 ^ 40 * 2439641 * 2
def baseEnd_2439641 : Nat := 1252708457415594627067801

theorem tailTrace_2439641 : CollatzResearch.WordTrace tailWord_2439641 prefixEnd_2439641 1252708457415594627067801 := by
  unfold tailWord_2439641
  simp only [CollatzResearch.WordTrace]
  refine ⟨88981017354604789356110777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59320678236403192904073851 88981017354604789356110777)
  ·
    refine ⟨66735763015953592017083083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88981017354604789356110777 66735763015953592017083083)
    ·
      refine ⟨100103644523930388025624625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66735763015953592017083083 100103644523930388025624625)
      ·
        refine ⟨75077733392947791019218469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100103644523930388025624625 75077733392947791019218469)
        ·
          refine ⟨14077075011177710816103463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75077733392947791019218469 14077075011177710816103463)
          ·
            refine ⟨21115612516766566224155195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14077075011177710816103463 21115612516766566224155195)
            ·
              refine ⟨31673418775149849336232793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21115612516766566224155195 31673418775149849336232793)
              ·
                refine ⟨23755064081362387002174595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31673418775149849336232793 23755064081362387002174595)
                ·
                  refine ⟨35632596122043580503261893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23755064081362387002174595 35632596122043580503261893)
                  ·
                    refine ⟨6681111772883171344361605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35632596122043580503261893 6681111772883171344361605)
                    ·
                      refine ⟨1252708457415594627067801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6681111772883171344361605 1252708457415594627067801)
                      ·
                        rfl

theorem cell23_2439641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 2, 1, 4, 4].length) (baseStart_2439641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2439641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2439641 prefixEnd_2439641 := by exact prefixLift 2439641
  have htrace : WordTrace (prefixWord ++ tailWord_2439641) baseStart_2439641 baseEnd_2439641 := by
    simpa [prefixWord, tailWord_2439641, baseEnd_2439641] using wordTrace_append hprefix tailTrace_2439641
  have hstable : (prefixWord ++ tailWord_2439641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2439641).length < 2 ^ (prefixWord ++ tailWord_2439641).sum := by decide
  have hdescent : baseEnd_2439641 < baseStart_2439641 := by decide
  rcases family_descends (prefixWord ++ tailWord_2439641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2439645 : List Nat := [1, 4, 3, 1, 1, 1, 1, 4, 1, 4, 2]
def baseStart_2439645 : Nat := 118140960795 + 2439645 * 2 ^ 59
def prefixEnd_2439645 : Nat := 4983230072969 + 3 ^ 40 * 2439645 * 2
def baseEnd_2439645 : Nat := 1252710511338212611417783

theorem tailTrace_2439645 : CollatzResearch.WordTrace tailWord_2439645 prefixEnd_2439645 1252710511338212611417783 := by
  unfold tailWord_2439645
  simp only [CollatzResearch.WordTrace]
  refine ⟨88981163246590298039256389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59320775497726865359504259 88981163246590298039256389)
  ·
    refine ⟨16683968108735680882360573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88981163246590298039256389 16683968108735680882360573)
    ·
      refine ⟨6256488040775880330885215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16683968108735680882360573 6256488040775880330885215)
      ·
        refine ⟨9384732061163820496327823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6256488040775880330885215 9384732061163820496327823)
        ·
          refine ⟨14077098091745730744491735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9384732061163820496327823 14077098091745730744491735)
          ·
            refine ⟨21115647137618596116737603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14077098091745730744491735 21115647137618596116737603)
            ·
              refine ⟨31673470706427894175106405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21115647137618596116737603 31673470706427894175106405)
              ·
                refine ⟨5938775757455230157832451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31673470706427894175106405 5938775757455230157832451)
                ·
                  refine ⟨8908163636182845236748677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5938775757455230157832451 8908163636182845236748677)
                  ·
                    refine ⟨1670280681784283481890377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8908163636182845236748677 1670280681784283481890377)
                    ·
                      refine ⟨1252710511338212611417783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1670280681784283481890377 1252710511338212611417783)
                      ·
                        rfl

theorem cell23_2439645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 4, 1, 4, 2].length) (baseStart_2439645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2439645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2439645 prefixEnd_2439645 := by exact prefixLift 2439645
  have htrace : WordTrace (prefixWord ++ tailWord_2439645) baseStart_2439645 baseEnd_2439645 := by
    simpa [prefixWord, tailWord_2439645, baseEnd_2439645] using wordTrace_append hprefix tailTrace_2439645
  have hstable : (prefixWord ++ tailWord_2439645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2439645).length < 2 ^ (prefixWord ++ tailWord_2439645).sum := by decide
  have hdescent : baseEnd_2439645 < baseStart_2439645 := by decide
  rcases family_descends (prefixWord ++ tailWord_2439645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2439658 : List Nat := [3, 1, 3, 1, 3, 1, 1, 2, 2, 2, 4]
def baseStart_2439658 : Nat := 118140960795 + 2439658 * 2 ^ 59
def prefixEnd_2439658 : Nat := 4983230072969 + 3 ^ 40 * 2439658 * 2
def baseEnd_2439658 : Nat := 1252717186586721060555223

theorem tailTrace_2439658 : CollatzResearch.WordTrace tailWord_2439658 prefixEnd_2439658 1252717186586721060555223 := by
  unfold tailWord_2439658
  simp only [CollatzResearch.WordTrace]
  refine ⟨22245409348885800314869907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59321091597028800839653085 22245409348885800314869907)
  ·
    refine ⟨33368114023328700472304861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22245409348885800314869907 33368114023328700472304861)
    ·
      refine ⟨12513042758748262677114323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33368114023328700472304861 12513042758748262677114323)
      ·
        refine ⟨18769564138122394015671485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12513042758748262677114323 18769564138122394015671485)
        ·
          refine ⟨7038586551795897755876807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18769564138122394015671485 7038586551795897755876807)
          ·
            refine ⟨10557879827693846633815211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7038586551795897755876807 10557879827693846633815211)
            ·
              refine ⟨15836819741540769950722817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10557879827693846633815211 15836819741540769950722817)
              ·
                refine ⟨11877614806155577463042113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15836819741540769950722817 11877614806155577463042113)
                ·
                  refine ⟨8908211104616683097281585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11877614806155577463042113 8908211104616683097281585)
                  ·
                    refine ⟨6681158328462512322961189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8908211104616683097281585 6681158328462512322961189)
                    ·
                      refine ⟨1252717186586721060555223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6681158328462512322961189 1252717186586721060555223)
                      ·
                        rfl

theorem cell23_2439658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 2, 2, 2, 4].length) (baseStart_2439658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2439658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2439658 prefixEnd_2439658 := by exact prefixLift 2439658
  have htrace : WordTrace (prefixWord ++ tailWord_2439658) baseStart_2439658 baseEnd_2439658 := by
    simpa [prefixWord, tailWord_2439658, baseEnd_2439658] using wordTrace_append hprefix tailTrace_2439658
  have hstable : (prefixWord ++ tailWord_2439658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2439658).length < 2 ^ (prefixWord ++ tailWord_2439658).sum := by decide
  have hdescent : baseEnd_2439658 < baseStart_2439658 := by decide
  rcases family_descends (prefixWord ++ tailWord_2439658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2439662 : List Nat := [4, 1, 2, 1, 2, 3, 1, 1, 4, 2, 2]
def baseStart_2439662 : Nat := 118140960795 + 2439662 * 2 ^ 59
def prefixEnd_2439662 : Nat := 4983230072969 + 3 ^ 40 * 2439662 * 2
def baseEnd_2439662 : Nat := 1252719240509339044905205

theorem tailTrace_2439662 : CollatzResearch.WordTrace tailWord_2439662 prefixEnd_2439662 1252719240509339044905205 := by
  unfold tailWord_2439662
  simp only [CollatzResearch.WordTrace]
  refine ⟨11122722910941088742828155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59321188858352473295083493 11122722910941088742828155)
  ·
    refine ⟨16684084366411633114242233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11122722910941088742828155 16684084366411633114242233)
    ·
      refine ⟨12513063274808724835681675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16684084366411633114242233 12513063274808724835681675)
      ·
        refine ⟨18769594912213087253522513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12513063274808724835681675 18769594912213087253522513)
        ·
          refine ⟨14077196184159815440141885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18769594912213087253522513 14077196184159815440141885)
          ·
            refine ⟨5278948569059930790053207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14077196184159815440141885 5278948569059930790053207)
            ·
              refine ⟨7918422853589896185079811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5278948569059930790053207 7918422853589896185079811)
              ·
                refine ⟨11877634280384844277619717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7918422853589896185079811 11877634280384844277619717)
                ·
                  refine ⟨2227056427572158302053697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11877634280384844277619717 2227056427572158302053697)
                  ·
                    refine ⟨1670292320679118726540273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2227056427572158302053697 1670292320679118726540273)
                    ·
                      refine ⟨1252719240509339044905205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1670292320679118726540273 1252719240509339044905205)
                      ·
                        rfl

theorem cell23_2439662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 1, 4, 2, 2].length) (baseStart_2439662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2439662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2439662 prefixEnd_2439662 := by exact prefixLift 2439662
  have htrace : WordTrace (prefixWord ++ tailWord_2439662) baseStart_2439662 baseEnd_2439662 := by
    simpa [prefixWord, tailWord_2439662, baseEnd_2439662] using wordTrace_append hprefix tailTrace_2439662
  have hstable : (prefixWord ++ tailWord_2439662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2439662).length < 2 ^ (prefixWord ++ tailWord_2439662).sum := by decide
  have hdescent : baseEnd_2439662 < baseStart_2439662 := by decide
  rcases family_descends (prefixWord ++ tailWord_2439662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2439719 : List Nat := [1, 1, 7, 2, 2, 1, 1, 1, 7]
def baseStart_2439719 : Nat := 118140960795 + 2439719 * 2 ^ 59
def prefixEnd_2439719 : Nat := 4983230072969 + 3 ^ 40 * 2439719 * 2
def baseEnd_2439719 : Nat := 139194278767405035765827

theorem tailTrace_2439719 : CollatzResearch.WordTrace tailWord_2439719 prefixEnd_2439719 139194278767405035765827 := by
  unfold tailWord_2439719
  simp only [CollatzResearch.WordTrace]
  refine ⟨88983862248322208677450211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59322574832214805784966807 88983862248322208677450211)
  ·
    refine ⟨133475793372483313016175317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88983862248322208677450211 133475793372483313016175317)
    ·
      refine ⟨3128338907167577648816609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 133475793372483313016175317 3128338907167577648816609)
      ·
        refine ⟨2346254180375683236612457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3128338907167577648816609 2346254180375683236612457)
        ·
          refine ⟨1759690635281762427459343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2346254180375683236612457 1759690635281762427459343)
          ·
            refine ⟨2639535952922643641189015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1759690635281762427459343 2639535952922643641189015)
            ·
              refine ⟨3959303929383965461783523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2639535952922643641189015 3959303929383965461783523)
              ·
                refine ⟨5938955894075948192675285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3959303929383965461783523 5938955894075948192675285)
                ·
                  refine ⟨139194278767405035765827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5938955894075948192675285 139194278767405035765827)
                  ·
                    rfl

theorem cell23_2439719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 1, 7].length) (baseStart_2439719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2439719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2439719 prefixEnd_2439719 := by exact prefixLift 2439719
  have htrace : WordTrace (prefixWord ++ tailWord_2439719) baseStart_2439719 baseEnd_2439719 := by
    simpa [prefixWord, tailWord_2439719, baseEnd_2439719] using wordTrace_append hprefix tailTrace_2439719
  have hstable : (prefixWord ++ tailWord_2439719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2439719).length < 2 ^ (prefixWord ++ tailWord_2439719).sum := by decide
  have hdescent : baseEnd_2439719 < baseStart_2439719 := by decide
  rcases family_descends (prefixWord ++ tailWord_2439719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2439762 : List Nat := [3, 2, 2, 1, 2, 1, 2, 5, 1, 4]
def baseStart_2439762 : Nat := 118140960795 + 2439762 * 2 ^ 59
def prefixEnd_2439762 : Nat := 4983230072969 + 3 ^ 40 * 2439762 * 2
def baseEnd_2439762 : Nat := 417590196191596217884915

theorem tailTrace_2439762 : CollatzResearch.WordTrace tailWord_2439762 prefixEnd_2439762 417590196191596217884915 := by
  unfold tailWord_2439762
  simp only [CollatzResearch.WordTrace]
  refine ⟨22246357646791606755316385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59323620391444284680843693 22246357646791606755316385)
  ·
    refine ⟨16684768235093705066487289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22246357646791606755316385 16684768235093705066487289)
    ·
      refine ⟨12513576176320278799865467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16684768235093705066487289 12513576176320278799865467)
      ·
        refine ⟨18770364264480418199798201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12513576176320278799865467 18770364264480418199798201)
        ·
          refine ⟨14077773198360313649848651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18770364264480418199798201 14077773198360313649848651)
          ·
            refine ⟨21116659797540470474772977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14077773198360313649848651 21116659797540470474772977)
            ·
              refine ⟨15837494848155352856079733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21116659797540470474772977 15837494848155352856079733)
              ·
                refine ⟨1484765142014564330257475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15837494848155352856079733 1484765142014564330257475)
                ·
                  refine ⟨2227147713021846495386213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1484765142014564330257475 2227147713021846495386213)
                  ·
                    refine ⟨417590196191596217884915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2227147713021846495386213 417590196191596217884915)
                    ·
                      rfl

theorem cell23_2439762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 5, 1, 4].length) (baseStart_2439762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2439762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2439762 prefixEnd_2439762 := by exact prefixLift 2439762
  have htrace : WordTrace (prefixWord ++ tailWord_2439762) baseStart_2439762 baseEnd_2439762 := by
    simpa [prefixWord, tailWord_2439762, baseEnd_2439762] using wordTrace_append hprefix tailTrace_2439762
  have hstable : (prefixWord ++ tailWord_2439762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2439762).length < 2 ^ (prefixWord ++ tailWord_2439762).sum := by decide
  have hdescent : baseEnd_2439762 < baseStart_2439762 := by decide
  rcases family_descends (prefixWord ++ tailWord_2439762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2439785 : List Nat := [1, 2, 1, 1, 1, 4, 1, 5, 3, 1, 3]
def baseStart_2439785 : Nat := 118140960795 + 2439785 * 2 ^ 59
def prefixEnd_2439785 : Nat := 4983230072969 + 3 ^ 40 * 2439785 * 2
def baseEnd_2439785 : Nat := 1252782398629842063667139

theorem tailTrace_2439785 : CollatzResearch.WordTrace tailWord_2439785 prefixEnd_2439785 1252782398629842063667139 := by
  unfold tailWord_2439785
  simp only [CollatzResearch.WordTrace]
  refine ⟨88986269466083101949352809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59324179644055401299568539 88986269466083101949352809)
  ·
    refine ⟨66739702099562326462014607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88986269466083101949352809 66739702099562326462014607)
    ·
      refine ⟨100109553149343489693021911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66739702099562326462014607 100109553149343489693021911)
      ·
        refine ⟨150164329724015234539532867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100109553149343489693021911 150164329724015234539532867)
        ·
          refine ⟨225246494586022851809299301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150164329724015234539532867 225246494586022851809299301)
          ·
            refine ⟨42233717734879284714243619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 225246494586022851809299301 42233717734879284714243619)
            ·
              refine ⟨63350576602318927071365429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42233717734879284714243619 63350576602318927071365429)
              ·
                refine ⟨5939116556467399412940509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 63350576602318927071365429 5939116556467399412940509)
                ·
                  refine ⟨2227168708675274779852691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5939116556467399412940509 2227168708675274779852691)
                  ·
                    refine ⟨3340753063012912169779037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2227168708675274779852691 3340753063012912169779037)
                    ·
                      refine ⟨1252782398629842063667139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3340753063012912169779037 1252782398629842063667139)
                      ·
                        rfl

theorem cell23_2439785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 5, 3, 1, 3].length) (baseStart_2439785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2439785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2439785 prefixEnd_2439785 := by exact prefixLift 2439785
  have htrace : WordTrace (prefixWord ++ tailWord_2439785) baseStart_2439785 baseEnd_2439785 := by
    simpa [prefixWord, tailWord_2439785, baseEnd_2439785] using wordTrace_append hprefix tailTrace_2439785
  have hstable : (prefixWord ++ tailWord_2439785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2439785).length < 2 ^ (prefixWord ++ tailWord_2439785).sum := by decide
  have hdescent : baseEnd_2439785 < baseStart_2439785 := by decide
  rcases family_descends (prefixWord ++ tailWord_2439785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2439788 : List Nat := [2, 2, 1, 1, 3, 1, 3, 2, 3, 5]
def baseStart_2439788 : Nat := 118140960795 + 2439788 * 2 ^ 59
def prefixEnd_2439788 : Nat := 4983230072969 + 3 ^ 40 * 2439788 * 2
def baseEnd_2439788 : Nat := 417594646357268517309875

theorem tailTrace_2439788 : CollatzResearch.WordTrace tailWord_2439788 prefixEnd_2439788 417594646357268517309875 := by
  unfold tailWord_2439788
  simp only [CollatzResearch.WordTrace]
  refine ⟨44493189442536116730856009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59324252590048155641141345 44493189442536116730856009)
  ·
    refine ⟨33369892081902087548142007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44493189442536116730856009 33369892081902087548142007)
    ·
      refine ⟨50054838122853131322213011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33369892081902087548142007 50054838122853131322213011)
      ·
        refine ⟨75082257184279696983319517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50054838122853131322213011 75082257184279696983319517)
        ·
          refine ⟨28155846444104886368744819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75082257184279696983319517 28155846444104886368744819)
          ·
            refine ⟨42233769666157329553117229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28155846444104886368744819 42233769666157329553117229)
            ·
              refine ⟨15837663624808998582418961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42233769666157329553117229 15837663624808998582418961)
              ·
                refine ⟨11878247718606748936814221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15837663624808998582418961 11878247718606748936814221)
                ·
                  refine ⟨4454342894477530851305333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11878247718606748936814221 4454342894477530851305333)
                  ·
                    refine ⟨417594646357268517309875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4454342894477530851305333 417594646357268517309875)
                    ·
                      rfl

theorem cell23_2439788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 5].length) (baseStart_2439788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2439788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2439788 prefixEnd_2439788 := by exact prefixLift 2439788
  have htrace : WordTrace (prefixWord ++ tailWord_2439788) baseStart_2439788 baseEnd_2439788 := by
    simpa [prefixWord, tailWord_2439788, baseEnd_2439788] using wordTrace_append hprefix tailTrace_2439788
  have hstable : (prefixWord ++ tailWord_2439788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2439788).length < 2 ^ (prefixWord ++ tailWord_2439788).sum := by decide
  have hdescent : baseEnd_2439788 < baseStart_2439788 := by decide
  rcases family_descends (prefixWord ++ tailWord_2439788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2439812 : List Nat := [2, 3, 2, 1, 3, 2, 1, 1, 1, 5, 2]
def baseStart_2439812 : Nat := 118140960795 + 2439812 * 2 ^ 59
def prefixEnd_2439812 : Nat := 4983230072969 + 3 ^ 40 * 2439812 * 2
def baseEnd_2439812 : Nat := 1252796262607513458029515

theorem tailTrace_2439812 : CollatzResearch.WordTrace tailWord_2439812 prefixEnd_2439812 1252796262607513458029515 := by
  unfold tailWord_2439812
  simp only [CollatzResearch.WordTrace]
  refine ⟨44493627118492642780292845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59324836157990190373723793 44493627118492642780292845)
  ·
    refine ⟨16685110169434741042609817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44493627118492642780292845 16685110169434741042609817)
    ·
      refine ⟨12513832627076055781957363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16685110169434741042609817 12513832627076055781957363)
      ·
        refine ⟨18770748940614083672936045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12513832627076055781957363 18770748940614083672936045)
        ·
          refine ⟨7039030852730281377351017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18770748940614083672936045 7039030852730281377351017)
          ·
            refine ⟨5279273139547711033013263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7039030852730281377351017 5279273139547711033013263)
            ·
              refine ⟨7918909709321566549519895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5279273139547711033013263 7918909709321566549519895)
              ·
                refine ⟨11878364563982349824279843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7918909709321566549519895 11878364563982349824279843)
                ·
                  refine ⟨17817546845973524736419765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11878364563982349824279843 17817546845973524736419765)
                  ·
                    refine ⟨1670395016810017944039353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17817546845973524736419765 1670395016810017944039353)
                    ·
                      refine ⟨1252796262607513458029515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1670395016810017944039353 1252796262607513458029515)
                      ·
                        rfl

theorem cell23_2439812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 1, 1, 5, 2].length) (baseStart_2439812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2439812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2439812 prefixEnd_2439812 := by exact prefixLift 2439812
  have htrace : WordTrace (prefixWord ++ tailWord_2439812) baseStart_2439812 baseEnd_2439812 := by
    simpa [prefixWord, tailWord_2439812, baseEnd_2439812] using wordTrace_append hprefix tailTrace_2439812
  have hstable : (prefixWord ++ tailWord_2439812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2439812).length < 2 ^ (prefixWord ++ tailWord_2439812).sum := by decide
  have hdescent : baseEnd_2439812 < baseStart_2439812 := by decide
  rcases family_descends (prefixWord ++ tailWord_2439812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2439855 : List Nat := [1, 1, 2, 1, 2, 5, 3, 1, 1, 2, 4]
def baseStart_2439855 : Nat := 118140960795 + 2439855 * 2 ^ 59
def prefixEnd_2439855 : Nat := 4983230072969 + 3 ^ 40 * 2439855 * 2
def baseEnd_2439855 : Nat := 1252818342275656789791817

theorem tailTrace_2439855 : CollatzResearch.WordTrace tailWord_2439855 prefixEnd_2439855 1252818342275656789791817 := by
  unfold tailWord_2439855
  simp only [CollatzResearch.WordTrace]
  refine ⟨88988822575829503904401019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59325881717219669269600679 88988822575829503904401019)
  ·
    refine ⟨133483233863744255856601529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88988822575829503904401019 133483233863744255856601529)
    ·
      refine ⟨100112425397808191892451147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133483233863744255856601529 100112425397808191892451147)
      ·
        refine ⟨150168638096712287838676721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100112425397808191892451147 150168638096712287838676721)
        ·
          refine ⟨112626478572534215879007541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150168638096712287838676721 112626478572534215879007541)
          ·
            refine ⟨10558732366175082738656957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 112626478572534215879007541 10558732366175082738656957)
            ·
              refine ⟨3959524637315656026996359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10558732366175082738656957 3959524637315656026996359)
              ·
                refine ⟨5939286955973484040494539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3959524637315656026996359 5939286955973484040494539)
                ·
                  refine ⟨8908930433960226060741809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5939286955973484040494539 8908930433960226060741809)
                  ·
                    refine ⟨6681697825470169545556357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8908930433960226060741809 6681697825470169545556357)
                    ·
                      refine ⟨1252818342275656789791817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6681697825470169545556357 1252818342275656789791817)
                      ·
                        rfl

theorem cell23_2439855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 1, 1, 2, 4].length) (baseStart_2439855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2439855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2439855 prefixEnd_2439855 := by exact prefixLift 2439855
  have htrace : WordTrace (prefixWord ++ tailWord_2439855) baseStart_2439855 baseEnd_2439855 := by
    simpa [prefixWord, tailWord_2439855, baseEnd_2439855] using wordTrace_append hprefix tailTrace_2439855
  have hstable : (prefixWord ++ tailWord_2439855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2439855).length < 2 ^ (prefixWord ++ tailWord_2439855).sum := by decide
  have hdescent : baseEnd_2439855 < baseStart_2439855 := by decide
  rcases family_descends (prefixWord ++ tailWord_2439855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2439893 : List Nat := [1, 3, 2, 5, 1, 2, 1, 1, 3, 2, 2]
def baseStart_2439893 : Nat := 118140960795 + 2439893 * 2 ^ 59
def prefixEnd_2439893 : Nat := 4983230072969 + 3 ^ 40 * 2439893 * 2
def baseEnd_2439893 : Nat := 1252837854540527641116643

theorem tailTrace_2439893 : CollatzResearch.WordTrace tailWord_2439893 prefixEnd_2439893 1252837854540527641116643 := by
  unfold tailWord_2439893
  simp only [CollatzResearch.WordTrace]
  refine ⟨88990208549691836394284333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59326805699794557596189555 88990208549691836394284333)
  ·
    refine ⟨33371328206134438647856625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88990208549691836394284333 33371328206134438647856625)
    ·
      refine ⟨25028496154600828985892469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33371328206134438647856625 25028496154600828985892469)
      ·
        refine ⟨2346421514493827717427419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25028496154600828985892469 2346421514493827717427419)
        ·
          refine ⟨3519632271740741576141129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2346421514493827717427419 3519632271740741576141129)
          ·
            refine ⟨2639724203805556182105847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3519632271740741576141129 2639724203805556182105847)
            ·
              refine ⟨3959586305708334273158771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2639724203805556182105847 3959586305708334273158771)
              ·
                refine ⟨5939379458562501409738157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3959586305708334273158771 5939379458562501409738157)
                ·
                  refine ⟨2227267296960938028651809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5939379458562501409738157 2227267296960938028651809)
                  ·
                    refine ⟨1670450472720703521488857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2227267296960938028651809 1670450472720703521488857)
                    ·
                      refine ⟨1252837854540527641116643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1670450472720703521488857 1252837854540527641116643)
                      ·
                        rfl

theorem cell23_2439893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_2439893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2439893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2439893 prefixEnd_2439893 := by exact prefixLift 2439893
  have htrace : WordTrace (prefixWord ++ tailWord_2439893) baseStart_2439893 baseEnd_2439893 := by
    simpa [prefixWord, tailWord_2439893, baseEnd_2439893] using wordTrace_append hprefix tailTrace_2439893
  have hstable : (prefixWord ++ tailWord_2439893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2439893).length < 2 ^ (prefixWord ++ tailWord_2439893).sum := by decide
  have hdescent : baseEnd_2439893 < baseStart_2439893 := by decide
  rcases family_descends (prefixWord ++ tailWord_2439893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2439909 : List Nat := [1, 3, 1, 4, 1, 3, 1, 3, 2, 1, 3]
def baseStart_2439909 : Nat := 118140960795 + 2439909 * 2 ^ 59
def prefixEnd_2439909 : Nat := 4983230072969 + 3 ^ 40 * 2439909 * 2
def baseEnd_2439909 : Nat := 1252846070230999578516569

theorem tailTrace_2439909 : CollatzResearch.WordTrace tailWord_2439909 prefixEnd_2439909 1252846070230999578516569 := by
  unfold tailWord_2439909
  simp only [CollatzResearch.WordTrace]
  refine ⟨88990792117633871126866781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59327194745089247417911187 88990792117633871126866781)
  ·
    refine ⟨33371547044112701672575043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88990792117633871126866781 33371547044112701672575043)
    ·
      refine ⟨50057320566169052508862565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33371547044112701672575043 50057320566169052508862565)
      ·
        refine ⟨9385747606156697345411731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50057320566169052508862565 9385747606156697345411731)
        ·
          refine ⟨14078621409235046018117597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9385747606156697345411731 14078621409235046018117597)
          ·
            refine ⟨5279483028463142256794099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14078621409235046018117597 5279483028463142256794099)
            ·
              refine ⟨7919224542694713385191149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5279483028463142256794099 7919224542694713385191149)
              ·
                refine ⟨2969709203510517519446681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7919224542694713385191149 2969709203510517519446681)
                ·
                  refine ⟨2227281902632888139585011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2969709203510517519446681 2227281902632888139585011)
                  ·
                    refine ⟨3340922853949332209377517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2227281902632888139585011 3340922853949332209377517)
                    ·
                      refine ⟨1252846070230999578516569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3340922853949332209377517 1252846070230999578516569)
                      ·
                        rfl

theorem cell23_2439909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 3, 2, 1, 3].length) (baseStart_2439909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2439909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2439909 prefixEnd_2439909 := by exact prefixLift 2439909
  have htrace : WordTrace (prefixWord ++ tailWord_2439909) baseStart_2439909 baseEnd_2439909 := by
    simpa [prefixWord, tailWord_2439909, baseEnd_2439909] using wordTrace_append hprefix tailTrace_2439909
  have hstable : (prefixWord ++ tailWord_2439909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2439909).length < 2 ^ (prefixWord ++ tailWord_2439909).sum := by decide
  have hdescent : baseEnd_2439909 < baseStart_2439909 := by decide
  rcases family_descends (prefixWord ++ tailWord_2439909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2439919 : List Nat := [1, 1, 2, 1, 5, 2, 3, 2, 1, 3, 2]
def baseStart_2439919 : Nat := 118140960795 + 2439919 * 2 ^ 59
def prefixEnd_2439919 : Nat := 4983230072969 + 3 ^ 40 * 2439919 * 2
def baseEnd_2439919 : Nat := 1252851205037544539391523

theorem tailTrace_2439919 : CollatzResearch.WordTrace tailWord_2439919 prefixEnd_2439919 1252851205037544539391523 := by
  unfold tailWord_2439919
  simp only [CollatzResearch.WordTrace]
  refine ⟨88991156847597642834730811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59327437898398428556487207 88991156847597642834730811)
  ·
    refine ⟨133486735271396464252096217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88991156847597642834730811 133486735271396464252096217)
    ·
      refine ⟨100115051453547348189072163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133486735271396464252096217 100115051453547348189072163)
      ·
        refine ⟨150172577180321022283608245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100115051453547348189072163 150172577180321022283608245)
        ·
          refine ⟨14078679110655095839088273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 150172577180321022283608245 14078679110655095839088273)
          ·
            refine ⟨10559009332991321879316205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14078679110655095839088273 10559009332991321879316205)
            ·
              refine ⟨3959628499871745704743577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10559009332991321879316205 3959628499871745704743577)
              ·
                refine ⟨2969721374903809278557683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3959628499871745704743577 2969721374903809278557683)
                ·
                  refine ⟨4454582062355713917836525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2969721374903809278557683 4454582062355713917836525)
                  ·
                    refine ⟨1670468273383392719188697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4454582062355713917836525 1670468273383392719188697)
                    ·
                      refine ⟨1252851205037544539391523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1670468273383392719188697 1252851205037544539391523)
                      ·
                        rfl

theorem cell23_2439919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 2, 1, 3, 2].length) (baseStart_2439919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2439919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2439919 prefixEnd_2439919 := by exact prefixLift 2439919
  have htrace : WordTrace (prefixWord ++ tailWord_2439919) baseStart_2439919 baseEnd_2439919 := by
    simpa [prefixWord, tailWord_2439919, baseEnd_2439919] using wordTrace_append hprefix tailTrace_2439919
  have hstable : (prefixWord ++ tailWord_2439919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2439919).length < 2 ^ (prefixWord ++ tailWord_2439919).sum := by decide
  have hdescent : baseEnd_2439919 < baseStart_2439919 := by decide
  rcases family_descends (prefixWord ++ tailWord_2439919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2439932 : List Nat := [2, 2, 2, 1, 3, 2, 1, 1, 3, 4, 2]
def baseStart_2439932 : Nat := 118140960795 + 2439932 * 2 ^ 59
def prefixEnd_2439932 : Nat := 4983230072969 + 3 ^ 40 * 2439932 * 2
def baseEnd_2439932 : Nat := 1252857880286052988528963

theorem tailTrace_2439932 : CollatzResearch.WordTrace tailWord_2439932 prefixEnd_2439932 1252857880286052988528963 := by
  unfold tailWord_2439932
  simp only [CollatzResearch.WordTrace]
  refine ⟨44495815498275273027477025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59327753997700364036636033 44495815498275273027477025)
  ·
    refine ⟨33371861623706454770607769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44495815498275273027477025 33371861623706454770607769)
    ·
      refine ⟨25028896217779841077955827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33371861623706454770607769 25028896217779841077955827)
      ·
        refine ⟨37543344326669761616933741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25028896217779841077955827 37543344326669761616933741)
        ·
          refine ⟨14078754122501160606350153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37543344326669761616933741 14078754122501160606350153)
          ·
            refine ⟨10559065591875870454762615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14078754122501160606350153 10559065591875870454762615)
            ·
              refine ⟨15838598387813805682143923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10559065591875870454762615 15838598387813805682143923)
              ·
                refine ⟨23757897581720708523215885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15838598387813805682143923 23757897581720708523215885)
                ·
                  refine ⟨8909211593145265696205957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23757897581720708523215885 8909211593145265696205957)
                  ·
                    refine ⟨1670477173714737318038617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8909211593145265696205957 1670477173714737318038617)
                    ·
                      refine ⟨1252857880286052988528963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1670477173714737318038617 1252857880286052988528963)
                      ·
                        rfl

theorem cell23_2439932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 1, 3, 4, 2].length) (baseStart_2439932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2439932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2439932 prefixEnd_2439932 := by exact prefixLift 2439932
  have htrace : WordTrace (prefixWord ++ tailWord_2439932) baseStart_2439932 baseEnd_2439932 := by
    simpa [prefixWord, tailWord_2439932, baseEnd_2439932] using wordTrace_append hprefix tailTrace_2439932
  have hstable : (prefixWord ++ tailWord_2439932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2439932).length < 2 ^ (prefixWord ++ tailWord_2439932).sum := by decide
  have hdescent : baseEnd_2439932 < baseStart_2439932 := by decide
  rcases family_descends (prefixWord ++ tailWord_2439932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2439972 : List Nat := [2, 3, 1, 3, 3, 1, 1, 2, 7]
def baseStart_2439972 : Nat := 118140960795 + 2439972 * 2 ^ 59
def prefixEnd_2439972 : Nat := 4983230072969 + 3 ^ 40 * 2439972 * 2
def baseEnd_2439972 : Nat := 139208713279136981336531

theorem tailTrace_2439972 : CollatzResearch.WordTrace tailWord_2439972 prefixEnd_2439972 139208713279136981336531 := by
  unfold tailWord_2439972
  simp only [CollatzResearch.WordTrace]
  refine ⟨44496544958202816443205085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59328726610937088590940113 44496544958202816443205085)
  ·
    refine ⟨16686204359326056166201907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44496544958202816443205085 16686204359326056166201907)
    ·
      refine ⟨25029306538989084249302861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16686204359326056166201907 25029306538989084249302861)
      ·
        refine ⟨9385989952120906593488573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25029306538989084249302861 9385989952120906593488573)
        ·
          refine ⟨3519746232045339972558215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9385989952120906593488573 3519746232045339972558215)
          ·
            refine ⟨5279619348068009958837323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3519746232045339972558215 5279619348068009958837323)
            ·
              refine ⟨7919429022102014938255985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5279619348068009958837323 7919429022102014938255985)
              ·
                refine ⟨5939571766576511203691989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7919429022102014938255985 5939571766576511203691989)
                ·
                  refine ⟨139208713279136981336531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5939571766576511203691989 139208713279136981336531)
                  ·
                    rfl

theorem cell23_2439972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 2, 7].length) (baseStart_2439972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2439972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2439972 prefixEnd_2439972 := by exact prefixLift 2439972
  have htrace : WordTrace (prefixWord ++ tailWord_2439972) baseStart_2439972 baseEnd_2439972 := by
    simpa [prefixWord, tailWord_2439972, baseEnd_2439972] using wordTrace_append hprefix tailTrace_2439972
  have hstable : (prefixWord ++ tailWord_2439972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2439972).length < 2 ^ (prefixWord ++ tailWord_2439972).sum := by decide
  have hdescent : baseEnd_2439972 < baseStart_2439972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2439972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2439985 : List Nat := [1, 2, 2, 3, 2, 1, 3, 1, 1, 7]
def baseStart_2439985 : Nat := 118140960795 + 2439985 * 2 ^ 59
def prefixEnd_2439985 : Nat := 4983230072969 + 3 ^ 40 * 2439985 * 2
def baseEnd_2439985 : Nat := 417628364920247093722073

theorem tailTrace_2439985 : CollatzResearch.WordTrace tailWord_2439985 prefixEnd_2439985 417628364920247093722073 := by
  unfold tailWord_2439985
  simp only [CollatzResearch.WordTrace]
  refine ⟨88993564065358536106633409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59329042710239024071088939 88993564065358536106633409)
  ·
    refine ⟨66745173049018902079975057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88993564065358536106633409 66745173049018902079975057)
    ·
      refine ⟨50058879786764176559981293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66745173049018902079975057 50058879786764176559981293)
      ·
        refine ⟨18772079920036566209992985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50058879786764176559981293 18772079920036566209992985)
        ·
          refine ⟨14079059940027424657494739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18772079920036566209992985 14079059940027424657494739)
          ·
            refine ⟨21118589910041136986242109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14079059940027424657494739 21118589910041136986242109)
            ·
              refine ⟨7919471216265426369840791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21118589910041136986242109 7919471216265426369840791)
              ·
                refine ⟨11879206824398139554761187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7919471216265426369840791 11879206824398139554761187)
                ·
                  refine ⟨17818810236597209332141781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11879206824398139554761187 17818810236597209332141781)
                  ·
                    refine ⟨417628364920247093722073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17818810236597209332141781 417628364920247093722073)
                    ·
                      rfl

theorem cell23_2439985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 1, 1, 7].length) (baseStart_2439985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2439985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2439985 prefixEnd_2439985 := by exact prefixLift 2439985
  have htrace : WordTrace (prefixWord ++ tailWord_2439985) baseStart_2439985 baseEnd_2439985 := by
    simpa [prefixWord, tailWord_2439985, baseEnd_2439985] using wordTrace_append hprefix tailTrace_2439985
  have hstable : (prefixWord ++ tailWord_2439985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2439985).length < 2 ^ (prefixWord ++ tailWord_2439985).sum := by decide
  have hdescent : baseEnd_2439985 < baseStart_2439985 := by decide
  rcases family_descends (prefixWord ++ tailWord_2439985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2439989 : List Nat := [1, 3, 3, 1, 3, 2, 2, 3, 5]
def baseStart_2439989 : Nat := 118140960795 + 2439989 * 2 ^ 59
def prefixEnd_2439989 : Nat := 4983230072969 + 3 ^ 40 * 2439989 * 2
def baseEnd_2439989 : Nat := 139209683187039918390689

theorem tailTrace_2439989 : CollatzResearch.WordTrace tailWord_2439989 prefixEnd_2439989 139209683187039918390689 := by
  unfold tailWord_2439989
  simp only [CollatzResearch.WordTrace]
  refine ⟨88993709957344044789779021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59329139971562696526519347 88993709957344044789779021)
  ·
    refine ⟨33372641234004016796167133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88993709957344044789779021 33372641234004016796167133)
    ·
      refine ⟨12514740462751506298562675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33372641234004016796167133 12514740462751506298562675)
      ·
        refine ⟨18772110694127259447844013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12514740462751506298562675 18772110694127259447844013)
        ·
          refine ⟨7039541510297722292941505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18772110694127259447844013 7039541510297722292941505)
          ·
            refine ⟨5279656132723291719706129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7039541510297722292941505 5279656132723291719706129)
            ·
              refine ⟨3959742099542468789779597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5279656132723291719706129 3959742099542468789779597)
              ·
                refine ⟨1484903287328425796167349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3959742099542468789779597 1484903287328425796167349)
                ·
                  refine ⟨139209683187039918390689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1484903287328425796167349 139209683187039918390689)
                  ·
                    rfl

theorem cell23_2439989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 3, 5].length) (baseStart_2439989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2439989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2439989 prefixEnd_2439989 := by exact prefixLift 2439989
  have htrace : WordTrace (prefixWord ++ tailWord_2439989) baseStart_2439989 baseEnd_2439989 := by
    simpa [prefixWord, tailWord_2439989, baseEnd_2439989] using wordTrace_append hprefix tailTrace_2439989
  have hstable : (prefixWord ++ tailWord_2439989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2439989).length < 2 ^ (prefixWord ++ tailWord_2439989).sum := by decide
  have hdescent : baseEnd_2439989 < baseStart_2439989 := by decide
  rcases family_descends (prefixWord ++ tailWord_2439989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2440006 : List Nat := [6, 1, 1, 2, 2, 1, 2, 1, 7]
def baseStart_2440006 : Nat := 118140960795 + 2440006 * 2 ^ 59
def prefixEnd_2440006 : Nat := 4983230072969 + 3 ^ 40 * 2440006 * 2
def baseEnd_2440006 : Nat := 139210653094942855444847

theorem tailTrace_2440006 : CollatzResearch.WordTrace tailWord_2440006 prefixEnd_2440006 139210653094942855444847 := by
  unfold tailWord_2440006
  simp only [CollatzResearch.WordTrace]
  refine ⟨2781072812446326771660871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 59329553332188304462098581 2781072812446326771660871)
  ·
    refine ⟨4171609218669490157491307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2781072812446326771660871 4171609218669490157491307)
    ·
      refine ⟨6257413828004235236236961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4171609218669490157491307 6257413828004235236236961)
      ·
        refine ⟨4693060371003176427177721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6257413828004235236236961 4693060371003176427177721)
        ·
          refine ⟨3519795278252382320383291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4693060371003176427177721 3519795278252382320383291)
          ·
            refine ⟨5279692917378573480574937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3519795278252382320383291 5279692917378573480574937)
            ·
              refine ⟨3959769688033930110431203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5279692917378573480574937 3959769688033930110431203)
              ·
                refine ⟨5939654532050895165646805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3959769688033930110431203 5939654532050895165646805)
                ·
                  refine ⟨139210653094942855444847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5939654532050895165646805 139210653094942855444847)
                  ·
                    rfl

theorem cell23_2440006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 1, 7].length) (baseStart_2440006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2440006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2440006 prefixEnd_2440006 := by exact prefixLift 2440006
  have htrace : WordTrace (prefixWord ++ tailWord_2440006) baseStart_2440006 baseEnd_2440006 := by
    simpa [prefixWord, tailWord_2440006, baseEnd_2440006] using wordTrace_append hprefix tailTrace_2440006
  have hstable : (prefixWord ++ tailWord_2440006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2440006).length < 2 ^ (prefixWord ++ tailWord_2440006).sum := by decide
  have hdescent : baseEnd_2440006 < baseStart_2440006 := by decide
  rcases family_descends (prefixWord ++ tailWord_2440006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2440032 : List Nat := [2, 1, 1, 3, 3, 1, 1, 4, 3, 4]
def baseStart_2440032 : Nat := 118140960795 + 2440032 * 2 ^ 59
def prefixEnd_2440032 : Nat := 4983230072969 + 3 ^ 40 * 2440032 * 2
def baseEnd_2440032 : Nat := 417636409450500865759501

theorem tailTrace_2440032 : CollatzResearch.WordTrace tailWord_2440032 prefixEnd_2440032 417636409450500865759501 := by
  unfold tailWord_2440032
  simp only [CollatzResearch.WordTrace]
  refine ⟨44497639148094131566797175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59330185530792175422396233 44497639148094131566797175)
  ·
    refine ⟨66746458722141197350195763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44497639148094131566797175 66746458722141197350195763)
    ·
      refine ⟨100119688083211796025293645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66746458722141197350195763 100119688083211796025293645)
      ·
        refine ⟨37544883031204423509485117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100119688083211796025293645 37544883031204423509485117)
        ·
          refine ⟨14079331136701658816056919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37544883031204423509485117 14079331136701658816056919)
          ·
            refine ⟨21118996705052488224085379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14079331136701658816056919 21118996705052488224085379)
            ·
              refine ⟨31678495057578732336128069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21118996705052488224085379 31678495057578732336128069)
              ·
                refine ⟨5939717823296012313024013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31678495057578732336128069 5939717823296012313024013)
                ·
                  refine ⟨2227394183736004617384005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5939717823296012313024013 2227394183736004617384005)
                  ·
                    refine ⟨417636409450500865759501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2227394183736004617384005 417636409450500865759501)
                    ·
                      rfl

theorem cell23_2440032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 4, 3, 4].length) (baseStart_2440032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2440032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2440032 prefixEnd_2440032 := by exact prefixLift 2440032
  have htrace : WordTrace (prefixWord ++ tailWord_2440032) baseStart_2440032 baseEnd_2440032 := by
    simpa [prefixWord, tailWord_2440032, baseEnd_2440032] using wordTrace_append hprefix tailTrace_2440032
  have hstable : (prefixWord ++ tailWord_2440032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2440032).length < 2 ^ (prefixWord ++ tailWord_2440032).sum := by decide
  have hdescent : baseEnd_2440032 < baseStart_2440032 := by decide
  rcases family_descends (prefixWord ++ tailWord_2440032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2440099 : List Nat := [1, 1, 1, 4, 1, 2, 3, 3, 2, 3, 2]
def baseStart_2440099 : Nat := 118140960795 + 2440099 * 2 ^ 59
def prefixEnd_2440099 : Nat := 4983230072969 + 3 ^ 40 * 2440099 * 2
def baseEnd_2440099 : Nat := 1252943631555353835140695

theorem tailTrace_2440099 : CollatzResearch.WordTrace tailWord_2440099 prefixEnd_2440099 1252943631555353835140695 := by
  unfold tailWord_2440099
  simp only [CollatzResearch.WordTrace]
  refine ⟨88997721986945533576283351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59331814657963689050855567 88997721986945533576283351)
  ·
    refine ⟨133496582980418300364425027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88997721986945533576283351 133496582980418300364425027)
    ·
      refine ⟨200244874470627450546637541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133496582980418300364425027 200244874470627450546637541)
      ·
        refine ⟨37545913963242646977494539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 200244874470627450546637541 37545913963242646977494539)
        ·
          refine ⟨56318870944863970466241809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37545913963242646977494539 56318870944863970466241809)
          ·
            refine ⟨42239153208647977849681357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56318870944863970466241809 42239153208647977849681357)
            ·
              refine ⟨15839682453242991693630509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42239153208647977849681357 15839682453242991693630509)
              ·
                refine ⟨5939880919966121885111441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15839682453242991693630509 5939880919966121885111441)
                ·
                  refine ⟨4454910689974591413833581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5939880919966121885111441 4454910689974591413833581)
                  ·
                    refine ⟨1670591508740471780187593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4454910689974591413833581 1670591508740471780187593)
                    ·
                      refine ⟨1252943631555353835140695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1670591508740471780187593 1252943631555353835140695)
                      ·
                        rfl

theorem cell23_2440099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 3, 2, 3, 2].length) (baseStart_2440099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2440099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2440099 prefixEnd_2440099 := by exact prefixLift 2440099
  have htrace : WordTrace (prefixWord ++ tailWord_2440099) baseStart_2440099 baseEnd_2440099 := by
    simpa [prefixWord, tailWord_2440099, baseEnd_2440099] using wordTrace_append hprefix tailTrace_2440099
  have hstable : (prefixWord ++ tailWord_2440099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2440099).length < 2 ^ (prefixWord ++ tailWord_2440099).sum := by decide
  have hdescent : baseEnd_2440099 < baseStart_2440099 := by decide
  rcases family_descends (prefixWord ++ tailWord_2440099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2440139 : List Nat := [1, 1, 1, 1, 3, 5, 2, 3, 2, 4]
def baseStart_2440139 : Nat := 118140960795 + 2440139 * 2 ^ 59
def prefixEnd_2440139 : Nat := 4983230072969 + 3 ^ 40 * 2440139 * 2
def baseEnd_2440139 : Nat := 417654723593844559546837

theorem tailTrace_2440139 : CollatzResearch.WordTrace tailWord_2440139 prefixEnd_2440139 417654723593844559546837 := by
  unfold tailWord_2440139
  simp only [CollatzResearch.WordTrace]
  refine ⟨88999180906800620407739471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59332787271200413605159647 88999180906800620407739471)
  ·
    refine ⟨133498771360200930611609207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88999180906800620407739471 133498771360200930611609207)
    ·
      refine ⟨200248157040301395917413811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133498771360200930611609207 200248157040301395917413811)
      ·
        refine ⟨300372235560452093876120717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200248157040301395917413811 300372235560452093876120717)
        ·
          refine ⟨112639588335169535203545269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 300372235560452093876120717 112639588335169535203545269)
          ·
            refine ⟨10559961406422143925332369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 112639588335169535203545269 10559961406422143925332369)
            ·
              refine ⟨7919971054816607943999277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10559961406422143925332369 7919971054816607943999277)
              ·
                refine ⟨2969989145556227978999729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7919971054816607943999277 2969989145556227978999729)
                ·
                  refine ⟨2227491859167170984249797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2969989145556227978999729 2227491859167170984249797)
                  ·
                    refine ⟨417654723593844559546837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2227491859167170984249797 417654723593844559546837)
                    ·
                      rfl

theorem cell23_2440139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 3, 2, 4].length) (baseStart_2440139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2440139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2440139 prefixEnd_2440139 := by exact prefixLift 2440139
  have htrace : WordTrace (prefixWord ++ tailWord_2440139) baseStart_2440139 baseEnd_2440139 := by
    simpa [prefixWord, tailWord_2440139, baseEnd_2440139] using wordTrace_append hprefix tailTrace_2440139
  have hstable : (prefixWord ++ tailWord_2440139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2440139).length < 2 ^ (prefixWord ++ tailWord_2440139).sum := by decide
  have hdescent : baseEnd_2440139 < baseStart_2440139 := by decide
  rcases family_descends (prefixWord ++ tailWord_2440139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2440150 : List Nat := [5, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2]
def baseStart_2440150 : Nat := 118140960795 + 2440150 * 2 ^ 59
def prefixEnd_2440150 : Nat := 4983230072969 + 3 ^ 40 * 2440150 * 2
def baseEnd_2440150 : Nat := 1252969819068733135602961

theorem tailTrace_2440150 : CollatzResearch.WordTrace tailWord_2440150 prefixEnd_2440150 1252969819068733135602961 := by
  unfold tailWord_2440150
  simp only [CollatzResearch.WordTrace]
  refine ⟨5562473881860048080399369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 59333054739840512857593269 5562473881860048080399369)
  ·
    refine ⟨4171855411395036060299527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5562473881860048080399369 4171855411395036060299527)
    ·
      refine ⟨6257783117092554090449291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4171855411395036060299527 6257783117092554090449291)
      ·
        refine ⟨9386674675638831135673937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6257783117092554090449291 9386674675638831135673937)
        ·
          refine ⟨7040006006729123351755453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9386674675638831135673937 7040006006729123351755453)
          ·
            refine ⟨2640002252523421256908295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7040006006729123351755453 2640002252523421256908295)
            ·
              refine ⟨3960003378785131885362443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2640002252523421256908295 3960003378785131885362443)
              ·
                refine ⟨5940005068177697828043665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3960003378785131885362443 5940005068177697828043665)
                ·
                  refine ⟨4455003801133273371032749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5940005068177697828043665 4455003801133273371032749)
                  ·
                    refine ⟨1670626425424977514137281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4455003801133273371032749 1670626425424977514137281)
                    ·
                      refine ⟨1252969819068733135602961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1670626425424977514137281 1252969819068733135602961)
                      ·
                        rfl

theorem cell23_2440150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2].length) (baseStart_2440150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2440150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2440150 prefixEnd_2440150 := by exact prefixLift 2440150
  have htrace : WordTrace (prefixWord ++ tailWord_2440150) baseStart_2440150 baseEnd_2440150 := by
    simpa [prefixWord, tailWord_2440150, baseEnd_2440150] using wordTrace_append hprefix tailTrace_2440150
  have hstable : (prefixWord ++ tailWord_2440150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2440150).length < 2 ^ (prefixWord ++ tailWord_2440150).sum := by decide
  have hdescent : baseEnd_2440150 < baseStart_2440150 := by decide
  rcases family_descends (prefixWord ++ tailWord_2440150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2440155 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 8]
def baseStart_2440155 : Nat := 118140960795 + 2440155 * 2 ^ 59
def prefixEnd_2440155 : Nat := 4983230072969 + 3 ^ 40 * 2440155 * 2
def baseEnd_2440155 : Nat := 1252972386472005616040437

theorem tailTrace_2440155 : CollatzResearch.WordTrace tailWord_2440155 prefixEnd_2440155 1252972386472005616040437 := by
  unfold tailWord_2440155
  simp only [CollatzResearch.WordTrace]
  refine ⟨88999764474742655140321919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59333176316495103426881279 88999764474742655140321919)
  ·
    refine ⟨133499646712113982710482879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88999764474742655140321919 133499646712113982710482879)
    ·
      refine ⟨200249470068170974065724319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133499646712113982710482879 200249470068170974065724319)
      ·
        refine ⟨300374205102256461098586479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200249470068170974065724319 300374205102256461098586479)
        ·
          refine ⟨450561307653384691647879719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 300374205102256461098586479 450561307653384691647879719)
          ·
            refine ⟨675841961480077037471819579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 450561307653384691647879719 675841961480077037471819579)
            ·
              refine ⟨1013762942220115556207729369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 675841961480077037471819579 1013762942220115556207729369)
              ·
                refine ⟨760322206665086667155797027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1013762942220115556207729369 760322206665086667155797027)
                ·
                  refine ⟨1140483309997630000733695541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 760322206665086667155797027 1140483309997630000733695541)
                  ·
                    refine ⟨106920310312277812568783957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1140483309997630000733695541 106920310312277812568783957)
                    ·
                      refine ⟨1252972386472005616040437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 106920310312277812568783957 1252972386472005616040437)
                      ·
                        rfl

theorem cell23_2440155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 8].length) (baseStart_2440155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2440155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2440155 prefixEnd_2440155 := by exact prefixLift 2440155
  have htrace : WordTrace (prefixWord ++ tailWord_2440155) baseStart_2440155 baseEnd_2440155 := by
    simpa [prefixWord, tailWord_2440155, baseEnd_2440155] using wordTrace_append hprefix tailTrace_2440155
  have hstable : (prefixWord ++ tailWord_2440155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2440155).length < 2 ^ (prefixWord ++ tailWord_2440155).sum := by decide
  have hdescent : baseEnd_2440155 < baseStart_2440155 := by decide
  rcases family_descends (prefixWord ++ tailWord_2440155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2440190 : List Nat := [4, 2, 2, 2, 2, 1, 3, 1, 2, 4]
def baseStart_2440190 : Nat := 118140960795 + 2440190 * 2 ^ 59
def prefixEnd_2440190 : Nat := 4983230072969 + 3 ^ 40 * 2440190 * 2
def baseEnd_2440190 : Nat := 417663452764970993034259

theorem tailTrace_2440190 : CollatzResearch.WordTrace tailWord_2440190 prefixEnd_2440190 417663452764970993034259 := by
  unfold tailWord_2440190
  simp only [CollatzResearch.WordTrace]
  refine ⟨11125130128701982014730753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59334027353077237411897349 11125130128701982014730753)
  ·
    refine ⟨8343847596526486511048065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11125130128701982014730753 8343847596526486511048065)
    ·
      refine ⟨6257885697394864883286049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8343847596526486511048065 6257885697394864883286049)
      ·
        refine ⟨4693414273046148662464537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6257885697394864883286049 4693414273046148662464537)
        ·
          refine ⟨3520060704784611496848403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4693414273046148662464537 3520060704784611496848403)
          ·
            refine ⟨5280091057176917245272605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3520060704784611496848403 5280091057176917245272605)
            ·
              refine ⟨1980034146441343966977227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5280091057176917245272605 1980034146441343966977227)
              ·
                refine ⟨2970051219662015950465841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1980034146441343966977227 2970051219662015950465841)
                ·
                  refine ⟨2227538414746511962849381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2970051219662015950465841 2227538414746511962849381)
                  ·
                    refine ⟨417663452764970993034259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2227538414746511962849381 417663452764970993034259)
                    ·
                      rfl

theorem cell23_2440190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 3, 1, 2, 4].length) (baseStart_2440190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2440190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2440190 prefixEnd_2440190 := by exact prefixLift 2440190
  have htrace : WordTrace (prefixWord ++ tailWord_2440190) baseStart_2440190 baseEnd_2440190 := by
    simpa [prefixWord, tailWord_2440190, baseEnd_2440190] using wordTrace_append hprefix tailTrace_2440190
  have hstable : (prefixWord ++ tailWord_2440190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2440190).length < 2 ^ (prefixWord ++ tailWord_2440190).sum := by decide
  have hdescent : baseEnd_2440190 < baseStart_2440190 := by decide
  rcases family_descends (prefixWord ++ tailWord_2440190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2440236 : List Nat := [2, 2, 1, 1, 1, 2, 3, 3, 4, 2, 2]
def baseStart_2440236 : Nat := 118140960795 + 2440236 * 2 ^ 59
def prefixEnd_2440236 : Nat := 4983230072969 + 3 ^ 40 * 2440236 * 2
def baseEnd_2440236 : Nat := 1253013978405019799127565

theorem tailTrace_2440236 : CollatzResearch.WordTrace tailWord_2440236 prefixEnd_2440236 1253013978405019799127565 := by
  unfold tailWord_2440236
  simp only [CollatzResearch.WordTrace]
  refine ⟨44501359393724602987010281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59335145858299470649347041 44501359393724602987010281)
  ·
    refine ⟨33376019545293452240257711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44501359393724602987010281 33376019545293452240257711)
    ·
      refine ⟨50064029317940178360386567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33376019545293452240257711 50064029317940178360386567)
      ·
        refine ⟨75096043976910267540579851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50064029317940178360386567 75096043976910267540579851)
        ·
          refine ⟨112644065965365401310869777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75096043976910267540579851 112644065965365401310869777)
          ·
            refine ⟨84483049474024050983152333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112644065965365401310869777 84483049474024050983152333)
            ·
              refine ⟨31681143552759019118682125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84483049474024050983152333 31681143552759019118682125)
              ·
                refine ⟨11880428832284632169505797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31681143552759019118682125 11880428832284632169505797)
                ·
                  refine ⟨2227580406053368531782337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11880428832284632169505797 2227580406053368531782337)
                  ·
                    refine ⟨1670685304540026398836753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2227580406053368531782337 1670685304540026398836753)
                    ·
                      refine ⟨1253013978405019799127565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1670685304540026398836753 1253013978405019799127565)
                      ·
                        rfl

theorem cell23_2440236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 2, 2].length) (baseStart_2440236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2440236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2440236 prefixEnd_2440236 := by exact prefixLift 2440236
  have htrace : WordTrace (prefixWord ++ tailWord_2440236) baseStart_2440236 baseEnd_2440236 := by
    simpa [prefixWord, tailWord_2440236, baseEnd_2440236] using wordTrace_append hprefix tailTrace_2440236
  have hstable : (prefixWord ++ tailWord_2440236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2440236).length < 2 ^ (prefixWord ++ tailWord_2440236).sum := by decide
  have hdescent : baseEnd_2440236 < baseStart_2440236 := by decide
  rcases family_descends (prefixWord ++ tailWord_2440236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2440257 : List Nat := [1, 2, 5, 1, 4, 1, 1, 2, 1, 3, 2]
def baseStart_2440257 : Nat := 118140960795 + 2440257 * 2 ^ 59
def prefixEnd_2440257 : Nat := 4983230072969 + 3 ^ 40 * 2440257 * 2
def baseEnd_2440257 : Nat := 1253024761498764216964969

theorem tailTrace_2440257 : CollatzResearch.WordTrace tailWord_2440257 prefixEnd_2440257 1253024761498764216964969 := by
  unfold tailWord_2440257
  simp only [CollatzResearch.WordTrace]
  refine ⟨89003484720373126560535025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59335656480248751040356683 89003484720373126560535025)
  ·
    refine ⟨66752613540279844920401269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89003484720373126560535025 66752613540279844920401269)
    ·
      refine ⟨6258057519401235461287619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 66752613540279844920401269 6258057519401235461287619)
      ·
        refine ⟨9387086279101853191931429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6258057519401235461287619 9387086279101853191931429)
        ·
          refine ⟨1760078677331597473487143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9387086279101853191931429 1760078677331597473487143)
          ·
            refine ⟨2640118015997396210230715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1760078677331597473487143 2640118015997396210230715)
            ·
              refine ⟨3960177023996094315346073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2640118015997396210230715 3960177023996094315346073)
              ·
                refine ⟨2970132767997070736509555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3960177023996094315346073 2970132767997070736509555)
                ·
                  refine ⟨4455199151995606104764333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2970132767997070736509555 4455199151995606104764333)
                  ·
                    refine ⟨1670699681998352289286625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4455199151995606104764333 1670699681998352289286625)
                    ·
                      refine ⟨1253024761498764216964969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1670699681998352289286625 1253024761498764216964969)
                      ·
                        rfl

theorem cell23_2440257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 2, 1, 3, 2].length) (baseStart_2440257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2440257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2440257 prefixEnd_2440257 := by exact prefixLift 2440257
  have htrace : WordTrace (prefixWord ++ tailWord_2440257) baseStart_2440257 baseEnd_2440257 := by
    simpa [prefixWord, tailWord_2440257, baseEnd_2440257] using wordTrace_append hprefix tailTrace_2440257
  have hstable : (prefixWord ++ tailWord_2440257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2440257).length < 2 ^ (prefixWord ++ tailWord_2440257).sum := by decide
  have hdescent : baseEnd_2440257 < baseStart_2440257 := by decide
  rcases family_descends (prefixWord ++ tailWord_2440257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2440272 : List Nat := [2, 1, 1, 1, 1, 3, 1, 5, 1, 7]
def baseStart_2440272 : Nat := 118140960795 + 2440272 * 2 ^ 59
def prefixEnd_2440272 : Nat := 4983230072969 + 3 ^ 40 * 2440272 * 2
def baseEnd_2440272 : Nat := 417677487902860552759133

theorem tailTrace_2440272 : CollatzResearch.WordTrace tailWord_2440272 prefixEnd_2440272 417677487902860552759133 := by
  unfold tailWord_2440272
  simp only [CollatzResearch.WordTrace]
  refine ⟨44502015907659392061165535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59336021210212522748220713 44502015907659392061165535)
  ·
    refine ⟨66753023861489088091748303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44502015907659392061165535 66753023861489088091748303)
    ·
      refine ⟨100129535792233632137622455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66753023861489088091748303 100129535792233632137622455)
      ·
        refine ⟨150194303688350448206433683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100129535792233632137622455 150194303688350448206433683)
        ·
          refine ⟨225291455532525672309650525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150194303688350448206433683 225291455532525672309650525)
          ·
            refine ⟨84484295824697127116118947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 225291455532525672309650525 84484295824697127116118947)
            ·
              refine ⟨126726443737045690674178421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84484295824697127116118947 126726443737045690674178421)
              ·
                refine ⟨11880604100348033500704227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 126726443737045690674178421 11880604100348033500704227)
                ·
                  refine ⟨17820906150522050251056341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11880604100348033500704227 17820906150522050251056341)
                  ·
                    refine ⟨417677487902860552759133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17820906150522050251056341 417677487902860552759133)
                    ·
                      rfl

theorem cell23_2440272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 5, 1, 7].length) (baseStart_2440272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2440272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2440272 prefixEnd_2440272 := by exact prefixLift 2440272
  have htrace : WordTrace (prefixWord ++ tailWord_2440272) baseStart_2440272 baseEnd_2440272 := by
    simpa [prefixWord, tailWord_2440272, baseEnd_2440272] using wordTrace_append hprefix tailTrace_2440272
  have hstable : (prefixWord ++ tailWord_2440272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2440272).length < 2 ^ (prefixWord ++ tailWord_2440272).sum := by decide
  have hdescent : baseEnd_2440272 < baseStart_2440272 := by decide
  rcases family_descends (prefixWord ++ tailWord_2440272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2440289 : List Nat := [1, 2, 3, 1, 1, 2, 4, 2, 2, 5]
def baseStart_2440289 : Nat := 118140960795 + 2440289 * 2 ^ 59
def prefixEnd_2440289 : Nat := 4983230072969 + 3 ^ 40 * 2440289 * 2
def baseEnd_2440289 : Nat := 417680397626569363921607

theorem tailTrace_2440289 : CollatzResearch.WordTrace tailWord_2440289 prefixEnd_2440289 417680397626569363921607 := by
  unfold tailWord_2440289
  simp only [CollatzResearch.WordTrace]
  refine ⟨89004651856257196025699921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59336434570838130683799947 89004651856257196025699921)
  ·
    refine ⟨66753488892192897019274941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89004651856257196025699921 66753488892192897019274941)
    ·
      refine ⟨25032558334572336382228103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66753488892192897019274941 25032558334572336382228103)
      ·
        refine ⟨37548837501858504573342155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25032558334572336382228103 37548837501858504573342155)
        ·
          refine ⟨56323256252787756860013233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37548837501858504573342155 56323256252787756860013233)
          ·
            refine ⟨42242442189590817645009925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56323256252787756860013233 42242442189590817645009925)
            ·
              refine ⟨7920457910548278308439361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42242442189590817645009925 7920457910548278308439361)
              ·
                refine ⟨5940343432911208731329521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7920457910548278308439361 5940343432911208731329521)
                ·
                  refine ⟨4455257574683406548497141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5940343432911208731329521 4455257574683406548497141)
                  ·
                    refine ⟨417680397626569363921607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4455257574683406548497141 417680397626569363921607)
                    ·
                      rfl

theorem cell23_2440289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 2, 2, 5].length) (baseStart_2440289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2440289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2440289 prefixEnd_2440289 := by exact prefixLift 2440289
  have htrace : WordTrace (prefixWord ++ tailWord_2440289) baseStart_2440289 baseEnd_2440289 := by
    simpa [prefixWord, tailWord_2440289, baseEnd_2440289] using wordTrace_append hprefix tailTrace_2440289
  have hstable : (prefixWord ++ tailWord_2440289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2440289).length < 2 ^ (prefixWord ++ tailWord_2440289).sum := by decide
  have hdescent : baseEnd_2440289 < baseStart_2440289 := by decide
  rcases family_descends (prefixWord ++ tailWord_2440289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2440349 : List Nat := [1, 4, 2, 1, 1, 2, 3, 1, 8]
def baseStart_2440349 : Nat := 118140960795 + 2440349 * 2 ^ 59
def prefixEnd_2440349 : Nat := 4983230072969 + 3 ^ 40 * 2440349 * 2
def baseEnd_2440349 : Nat := 139230222413219761890505

theorem tailTrace_2440349 : CollatzResearch.WordTrace tailWord_2440349 prefixEnd_2440349 139230222413219761890505 := by
  unfold tailWord_2440349
  simp only [CollatzResearch.WordTrace]
  refine ⟨89006840236039826272884101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59337893490693217515256067 89006840236039826272884101)
  ·
    refine ⟨16688782544257467426165769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89006840236039826272884101 16688782544257467426165769)
    ·
      refine ⟨12516586908193100569624327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16688782544257467426165769 12516586908193100569624327)
      ·
        refine ⟨18774880362289650854436491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12516586908193100569624327 18774880362289650854436491)
        ·
          refine ⟨28162320543434476281654737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18774880362289650854436491 28162320543434476281654737)
          ·
            refine ⟨21121740407575857211241053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28162320543434476281654737 21121740407575857211241053)
            ·
              refine ⟨7920652652840946454215395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21121740407575857211241053 7920652652840946454215395)
              ·
                refine ⟨11880978979261419681323093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7920652652840946454215395 11880978979261419681323093)
                ·
                  refine ⟨139230222413219761890505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11880978979261419681323093 139230222413219761890505)
                  ·
                    rfl

theorem cell23_2440349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 1, 8].length) (baseStart_2440349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2440349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2440349 prefixEnd_2440349 := by exact prefixLift 2440349
  have htrace : WordTrace (prefixWord ++ tailWord_2440349) baseStart_2440349 baseEnd_2440349 := by
    simpa [prefixWord, tailWord_2440349, baseEnd_2440349] using wordTrace_append hprefix tailTrace_2440349
  have hstable : (prefixWord ++ tailWord_2440349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2440349).length < 2 ^ (prefixWord ++ tailWord_2440349).sum := by decide
  have hdescent : baseEnd_2440349 < baseStart_2440349 := by decide
  rcases family_descends (prefixWord ++ tailWord_2440349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2440353 : List Nat := [1, 2, 3, 3, 1, 1, 1, 6, 1, 4]
def baseStart_2440353 : Nat := 118140960795 + 2440353 * 2 ^ 59
def prefixEnd_2440353 : Nat := 4983230072969 + 3 ^ 40 * 2440353 * 2
def baseEnd_2440353 : Nat := 417691351880531947121509

theorem tailTrace_2440353 : CollatzResearch.WordTrace tailWord_2440353 prefixEnd_2440353 417691351880531947121509 := by
  unfold tailWord_2440353
  simp only [CollatzResearch.WordTrace]
  refine ⟨89006986128025334956029713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59337990752016889970686475 89006986128025334956029713)
  ·
    refine ⟨66755239596019001217022285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89006986128025334956029713 66755239596019001217022285)
    ·
      refine ⟨25033214848507125456383357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66755239596019001217022285 25033214848507125456383357)
      ·
        refine ⟨9387455568190172046143759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25033214848507125456383357 9387455568190172046143759)
        ·
          refine ⟨14081183352285258069215639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9387455568190172046143759 14081183352285258069215639)
          ·
            refine ⟨21121775028427887103823459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14081183352285258069215639 21121775028427887103823459)
            ·
              refine ⟨31682662542641830655735189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21121775028427887103823459 31682662542641830655735189)
              ·
                refine ⟨1485124806686335811987587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 31682662542641830655735189 1485124806686335811987587)
                ·
                  refine ⟨2227687210029503717981381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1485124806686335811987587 2227687210029503717981381)
                  ·
                    refine ⟨417691351880531947121509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2227687210029503717981381 417691351880531947121509)
                    ·
                      rfl

theorem cell23_2440353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 6, 1, 4].length) (baseStart_2440353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2440353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2440353 prefixEnd_2440353 := by exact prefixLift 2440353
  have htrace : WordTrace (prefixWord ++ tailWord_2440353) baseStart_2440353 baseEnd_2440353 := by
    simpa [prefixWord, tailWord_2440353, baseEnd_2440353] using wordTrace_append hprefix tailTrace_2440353
  have hstable : (prefixWord ++ tailWord_2440353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2440353).length < 2 ^ (prefixWord ++ tailWord_2440353).sum := by decide
  have hdescent : baseEnd_2440353 < baseStart_2440353 := by decide
  rcases family_descends (prefixWord ++ tailWord_2440353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2440376 : List Nat := [2, 1, 2, 1, 2, 1, 2, 3, 5, 1, 3]
def baseStart_2440376 : Nat := 118140960795 + 2440376 * 2 ^ 59
def prefixEnd_2440376 : Nat := 4983230072969 + 3 ^ 40 * 2440376 * 2
def baseEnd_2440376 : Nat := 1253085865696649251376921

theorem tailTrace_2440376 : CollatzResearch.WordTrace tailWord_2440376 prefixEnd_2440376 1253085865696649251376921 := by
  unfold tailWord_2440376
  simp only [CollatzResearch.WordTrace]
  refine ⟨44503912503471004942058491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59338550004628006589411321 44503912503471004942058491)
  ·
    refine ⟨66755868755206507413087737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44503912503471004942058491 66755868755206507413087737)
    ·
      refine ⟨50066901566404880559815803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66755868755206507413087737 50066901566404880559815803)
      ·
        refine ⟨75100352349607320839723705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50066901566404880559815803 75100352349607320839723705)
        ·
          refine ⟨56325264262205490629792779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75100352349607320839723705 56325264262205490629792779)
          ·
            refine ⟨84487896393308235944689169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56325264262205490629792779 84487896393308235944689169)
            ·
              refine ⟨63365922294981176958516877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84487896393308235944689169 63365922294981176958516877)
              ·
                refine ⟨23762220860617941359443829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63365922294981176958516877 23762220860617941359443829)
                ·
                  refine ⟨2227708205682932002447859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23762220860617941359443829 2227708205682932002447859)
                  ·
                    refine ⟨3341562308524398003671789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2227708205682932002447859 3341562308524398003671789)
                    ·
                      refine ⟨1253085865696649251376921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3341562308524398003671789 1253085865696649251376921)
                      ·
                        rfl

theorem cell23_2440376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 5, 1, 3].length) (baseStart_2440376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2440376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2440376 prefixEnd_2440376 := by exact prefixLift 2440376
  have htrace : WordTrace (prefixWord ++ tailWord_2440376) baseStart_2440376 baseEnd_2440376 := by
    simpa [prefixWord, tailWord_2440376, baseEnd_2440376] using wordTrace_append hprefix tailTrace_2440376
  have hstable : (prefixWord ++ tailWord_2440376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2440376).length < 2 ^ (prefixWord ++ tailWord_2440376).sum := by decide
  have hdescent : baseEnd_2440376 < baseStart_2440376 := by decide
  rcases family_descends (prefixWord ++ tailWord_2440376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2440397 : List Nat := [1, 6, 2, 2, 1, 1, 1, 2, 2, 2, 3]
def baseStart_2440397 : Nat := 118140960795 + 2440397 * 2 ^ 59
def prefixEnd_2440397 : Nat := 4983230072969 + 3 ^ 40 * 2440397 * 2
def baseEnd_2440397 : Nat := 1253096648790393669214325

theorem tailTrace_2440397 : CollatzResearch.WordTrace tailWord_2440397 prefixEnd_2440397 1253096648790393669214325 := by
  unfold tailWord_2440397
  simp only [CollatzResearch.WordTrace]
  refine ⟨89008590939865930470631445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59339060626577286980420963 89008590939865930470631445)
  ·
    refine ⟨4172277700306215490810849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 89008590939865930470631445 4172277700306215490810849)
    ·
      refine ⟨3129208275229661618108137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4172277700306215490810849 3129208275229661618108137)
      ·
        refine ⟨2346906206422246213581103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3129208275229661618108137 2346906206422246213581103)
        ·
          refine ⟨3520359309633369320371655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2346906206422246213581103 3520359309633369320371655)
          ·
            refine ⟨5280538964450053980557483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3520359309633369320371655 5280538964450053980557483)
            ·
              refine ⟨7920808446675080970836225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5280538964450053980557483 7920808446675080970836225)
              ·
                refine ⟨5940606335006310728127169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7920808446675080970836225 5940606335006310728127169)
                ·
                  refine ⟨4455454751254733046095377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5940606335006310728127169 4455454751254733046095377)
                  ·
                    refine ⟨3341591063441049784571533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4455454751254733046095377 3341591063441049784571533)
                    ·
                      refine ⟨1253096648790393669214325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3341591063441049784571533 1253096648790393669214325)
                      ·
                        rfl

theorem cell23_2440397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_2440397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2440397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2440397 prefixEnd_2440397 := by exact prefixLift 2440397
  have htrace : WordTrace (prefixWord ++ tailWord_2440397) baseStart_2440397 baseEnd_2440397 := by
    simpa [prefixWord, tailWord_2440397, baseEnd_2440397] using wordTrace_append hprefix tailTrace_2440397
  have hstable : (prefixWord ++ tailWord_2440397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2440397).length < 2 ^ (prefixWord ++ tailWord_2440397).sum := by decide
  have hdescent : baseEnd_2440397 < baseStart_2440397 := by decide
  rcases family_descends (prefixWord ++ tailWord_2440397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2440404 : List Nat := [2, 4, 1, 4, 1, 1, 3, 2, 1, 4]
def baseStart_2440404 : Nat := 118140960795 + 2440404 * 2 ^ 59
def prefixEnd_2440404 : Nat := 4983230072969 + 3 ^ 40 * 2440404 * 2
def baseEnd_2440404 : Nat := 417700081051658380608931

theorem tailTrace_2440404 : CollatzResearch.WordTrace tailWord_2440404 prefixEnd_2440404 417700081051658380608931 := by
  unfold tailWord_2440404
  simp only [CollatzResearch.WordTrace]
  refine ⟨44504423125420285333068133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59339230833893713777424177 44504423125420285333068133)
  ·
    refine ⟨8344579336016303499950275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44504423125420285333068133 8344579336016303499950275)
    ·
      refine ⟨12516869004024455249925413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8344579336016303499950275 12516869004024455249925413)
      ·
        refine ⟨2346912938254585359361015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12516869004024455249925413 2346912938254585359361015)
        ·
          refine ⟨3520369407381878039041523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2346912938254585359361015 3520369407381878039041523)
          ·
            refine ⟨5280554111072817058562285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3520369407381878039041523 5280554111072817058562285)
            ·
              refine ⟨1980207791652306396960857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5280554111072817058562285 1980207791652306396960857)
              ·
                refine ⟨1485155843739229797720643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1980207791652306396960857 1485155843739229797720643)
                ·
                  refine ⟨2227733765608844696580965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1485155843739229797720643 2227733765608844696580965)
                  ·
                    refine ⟨417700081051658380608931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2227733765608844696580965 417700081051658380608931)
                    ·
                      rfl

theorem cell23_2440404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 3, 2, 1, 4].length) (baseStart_2440404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2440404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2440404 prefixEnd_2440404 := by exact prefixLift 2440404
  have htrace : WordTrace (prefixWord ++ tailWord_2440404) baseStart_2440404 baseEnd_2440404 := by
    simpa [prefixWord, tailWord_2440404, baseEnd_2440404] using wordTrace_append hprefix tailTrace_2440404
  have hstable : (prefixWord ++ tailWord_2440404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2440404).length < 2 ^ (prefixWord ++ tailWord_2440404).sum := by decide
  have hdescent : baseEnd_2440404 < baseStart_2440404 := by decide
  rcases family_descends (prefixWord ++ tailWord_2440404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2440433 : List Nat := [1, 2, 2, 2, 2, 1, 1, 3, 5, 2, 2]
def baseStart_2440433 : Nat := 118140960795 + 2440433 * 2 ^ 59
def prefixEnd_2440433 : Nat := 4983230072969 + 3 ^ 40 * 2440433 * 2
def baseEnd_2440433 : Nat := 1253115134093955528364159

theorem tailTrace_2440433 : CollatzResearch.WordTrace tailWord_2440433 prefixEnd_2440433 1253115134093955528364159 := by
  unfold tailWord_2440433
  simp only [CollatzResearch.WordTrace]
  refine ⟨89009903967735508618941953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59339935978490339079294635 89009903967735508618941953)
  ·
    refine ⟨66757427975801631464206465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89009903967735508618941953 66757427975801631464206465)
    ·
      refine ⟨50068070981851223598154849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66757427975801631464206465 50068070981851223598154849)
      ·
        refine ⟨37551053236388417698616137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50068070981851223598154849 37551053236388417698616137)
        ·
          refine ⟨28163289927291313273962103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37551053236388417698616137 28163289927291313273962103)
          ·
            refine ⟨42244934890936969910943155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28163289927291313273962103 42244934890936969910943155)
            ·
              refine ⟨63367402336405454866414733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42244934890936969910943155 63367402336405454866414733)
              ·
                refine ⟨23762775876152045574905525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63367402336405454866414733 23762775876152045574905525)
                ·
                  refine ⟨2227760238389254272647393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23762775876152045574905525 2227760238389254272647393)
                  ·
                    refine ⟨1670820178791940704485545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2227760238389254272647393 1670820178791940704485545)
                    ·
                      refine ⟨1253115134093955528364159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1670820178791940704485545 1253115134093955528364159)
                      ·
                        rfl

theorem cell23_2440433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 3, 5, 2, 2].length) (baseStart_2440433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2440433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2440433 prefixEnd_2440433 := by exact prefixLift 2440433
  have htrace : WordTrace (prefixWord ++ tailWord_2440433) baseStart_2440433 baseEnd_2440433 := by
    simpa [prefixWord, tailWord_2440433, baseEnd_2440433] using wordTrace_append hprefix tailTrace_2440433
  have hstable : (prefixWord ++ tailWord_2440433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2440433).length < 2 ^ (prefixWord ++ tailWord_2440433).sum := by decide
  have hdescent : baseEnd_2440433 < baseStart_2440433 := by decide
  rcases family_descends (prefixWord ++ tailWord_2440433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2440456 : List Nat := [2, 1, 3, 2, 5, 10]
def baseStart_2440456 : Nat := 118140960795 + 2440456 * 2 ^ 59
def prefixEnd_2440456 : Nat := 4983230072969 + 3 ^ 40 * 2440456 * 2
def baseEnd_2440456 : Nat := 5156901004728431845171

theorem tailTrace_2440456 : CollatzResearch.WordTrace tailWord_2440456 prefixEnd_2440456 5156901004728431845171 := by
  unfold tailWord_2440456
  simp only [CollatzResearch.WordTrace]
  refine ⟨44505371423326091773514611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59340495231101455698019481 44505371423326091773514611)
  ·
    refine ⟨66758057134989137660271917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44505371423326091773514611 66758057134989137660271917)
    ·
      refine ⟨25034271425620926622601969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66758057134989137660271917 25034271425620926622601969)
      ·
        refine ⟨18775703569215694966951477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25034271425620926622601969 18775703569215694966951477)
        ·
          refine ⟨1760222209613971403151701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18775703569215694966951477 1760222209613971403151701)
          ·
            refine ⟨5156901004728431845171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1760222209613971403151701 5156901004728431845171)
            ·
              rfl

theorem cell23_2440456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 10].length) (baseStart_2440456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2440456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2440456 prefixEnd_2440456 := by exact prefixLift 2440456
  have htrace : WordTrace (prefixWord ++ tailWord_2440456) baseStart_2440456 baseEnd_2440456 := by
    simpa [prefixWord, tailWord_2440456, baseEnd_2440456] using wordTrace_append hprefix tailTrace_2440456
  have hstable : (prefixWord ++ tailWord_2440456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2440456).length < 2 ^ (prefixWord ++ tailWord_2440456).sum := by decide
  have hdescent : baseEnd_2440456 < baseStart_2440456 := by decide
  rcases family_descends (prefixWord ++ tailWord_2440456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2440483 : List Nat := [1, 1, 1, 4, 2, 4, 2, 1, 1, 3, 3]
def baseStart_2440483 : Nat := 118140960795 + 2440483 * 2 ^ 59
def prefixEnd_2440483 : Nat := 4983230072969 + 3 ^ 40 * 2440483 * 2
def baseEnd_2440483 : Nat := 1253140808126680332738929

theorem tailTrace_2440483 : CollatzResearch.WordTrace tailWord_2440483 prefixEnd_2440483 1253140808126680332738929 := by
  unfold tailWord_2440483
  simp only [CollatzResearch.WordTrace]
  refine ⟨89011727617554367158262103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59341151745036244772174735 89011727617554367158262103)
  ·
    refine ⟨133517591426331550737393155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89011727617554367158262103 133517591426331550737393155)
    ·
      refine ⟨200276387139497326106089733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133517591426331550737393155 200276387139497326106089733)
      ·
        refine ⟨37551822588655748644891825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 200276387139497326106089733 37551822588655748644891825)
        ·
          refine ⟨28163866941491811483668869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37551822588655748644891825 28163866941491811483668869)
          ·
            refine ⟨5280725051529714653187913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28163866941491811483668869 5280725051529714653187913)
            ·
              refine ⟨3960543788647285989890935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5280725051529714653187913 3960543788647285989890935)
              ·
                refine ⟨5940815682970928984836403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3960543788647285989890935 5940815682970928984836403)
                ·
                  refine ⟨8911223524456393477254605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5940815682970928984836403 8911223524456393477254605)
                  ·
                    refine ⟨3341708821671147553970477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8911223524456393477254605 3341708821671147553970477)
                    ·
                      refine ⟨1253140808126680332738929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3341708821671147553970477 1253140808126680332738929)
                      ·
                        rfl

theorem cell23_2440483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 1, 1, 3, 3].length) (baseStart_2440483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2440483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2440483 prefixEnd_2440483 := by exact prefixLift 2440483
  have htrace : WordTrace (prefixWord ++ tailWord_2440483) baseStart_2440483 baseEnd_2440483 := by
    simpa [prefixWord, tailWord_2440483, baseEnd_2440483] using wordTrace_append hprefix tailTrace_2440483
  have hstable : (prefixWord ++ tailWord_2440483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2440483).length < 2 ^ (prefixWord ++ tailWord_2440483).sum := by decide
  have hdescent : baseEnd_2440483 < baseStart_2440483 := by decide
  rcases family_descends (prefixWord ++ tailWord_2440483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2440500 : List Nat := [2, 5, 1, 1, 1, 1, 2, 2, 4, 1, 3]
def baseStart_2440500 : Nat := 118140960795 + 2440500 * 2 ^ 59
def prefixEnd_2440500 : Nat := 4983230072969 + 3 ^ 40 * 2440500 * 2
def baseEnd_2440500 : Nat := 1253149537297806766226351

theorem tailTrace_2440500 : CollatzResearch.WordTrace tailWord_2440500 prefixEnd_2440500 1253149537297806766226351 := by
  unfold tailWord_2440500
  simp only [CollatzResearch.WordTrace]
  refine ⟨44506173829246389530815477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59341565105661852707753969 44506173829246389530815477)
  ·
    refine ⟨4172453796491849018513951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 44506173829246389530815477 4172453796491849018513951)
    ·
      refine ⟨6258680694737773527770927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4172453796491849018513951 6258680694737773527770927)
      ·
        refine ⟨9388021042106660291656391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6258680694737773527770927 9388021042106660291656391)
        ·
          refine ⟨14082031563159990437484587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9388021042106660291656391 14082031563159990437484587)
          ·
            refine ⟨21123047344739985656226881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14082031563159990437484587 21123047344739985656226881)
            ·
              refine ⟨15842285508554989242170161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21123047344739985656226881 15842285508554989242170161)
              ·
                refine ⟨11881714131416241931627621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15842285508554989242170161 11881714131416241931627621)
                ·
                  refine ⟨2227821399640545362180179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11881714131416241931627621 2227821399640545362180179)
                  ·
                    refine ⟨3341732099460818043270269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2227821399640545362180179 3341732099460818043270269)
                    ·
                      refine ⟨1253149537297806766226351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3341732099460818043270269 1253149537297806766226351)
                      ·
                        rfl

theorem cell23_2440500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 2, 4, 1, 3].length) (baseStart_2440500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2440500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2440500 prefixEnd_2440500 := by exact prefixLift 2440500
  have htrace : WordTrace (prefixWord ++ tailWord_2440500) baseStart_2440500 baseEnd_2440500 := by
    simpa [prefixWord, tailWord_2440500, baseEnd_2440500] using wordTrace_append hprefix tailTrace_2440500
  have hstable : (prefixWord ++ tailWord_2440500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2440500).length < 2 ^ (prefixWord ++ tailWord_2440500).sum := by decide
  have hdescent : baseEnd_2440500 < baseStart_2440500 := by decide
  rcases family_descends (prefixWord ++ tailWord_2440500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2440536 : List Nat := [2, 1, 2, 2, 1, 1, 3, 3, 2, 2, 4]
def baseStart_2440536 : Nat := 118140960795 + 2440536 * 2 ^ 59
def prefixEnd_2440536 : Nat := 4983230072969 + 3 ^ 40 * 2440536 * 2
def baseEnd_2440536 : Nat := 1253168022601368625376185

theorem tailTrace_2440536 : CollatzResearch.WordTrace tailWord_2440536 prefixEnd_2440536 1253168022601368625376185 := by
  unfold tailWord_2440536
  simp only [CollatzResearch.WordTrace]
  refine ⟨44506830343181178604970731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59342440457574904806627641 44506830343181178604970731)
  ·
    refine ⟨66760245514771767907456097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44506830343181178604970731 66760245514771767907456097)
    ·
      refine ⟨50070184136078825930592073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66760245514771767907456097 50070184136078825930592073)
      ·
        refine ⟨37552638102059119447944055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50070184136078825930592073 37552638102059119447944055)
        ·
          refine ⟨56328957153088679171916083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37552638102059119447944055 56328957153088679171916083)
          ·
            refine ⟨84493435729633018757874125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56328957153088679171916083 84493435729633018757874125)
            ·
              refine ⟨31685038398612382034202797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84493435729633018757874125 31685038398612382034202797)
              ·
                refine ⟨11881889399479643262826049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31685038398612382034202797 11881889399479643262826049)
                ·
                  refine ⟨8911417049609732447119537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11881889399479643262826049 8911417049609732447119537)
                  ·
                    refine ⟨6683562787207299335339653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8911417049609732447119537 6683562787207299335339653)
                    ·
                      refine ⟨1253168022601368625376185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6683562787207299335339653 1253168022601368625376185)
                      ·
                        rfl

theorem cell23_2440536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 3, 2, 2, 4].length) (baseStart_2440536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2440536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2440536 prefixEnd_2440536 := by exact prefixLift 2440536
  have htrace : WordTrace (prefixWord ++ tailWord_2440536) baseStart_2440536 baseEnd_2440536 := by
    simpa [prefixWord, tailWord_2440536, baseEnd_2440536] using wordTrace_append hprefix tailTrace_2440536
  have hstable : (prefixWord ++ tailWord_2440536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2440536).length < 2 ^ (prefixWord ++ tailWord_2440536).sum := by decide
  have hdescent : baseEnd_2440536 < baseStart_2440536 := by decide
  rcases family_descends (prefixWord ++ tailWord_2440536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2440610 : List Nat := [3, 3, 1, 2, 1, 3, 2, 1, 2, 5]
def baseStart_2440610 : Nat := 118140960795 + 2440610 * 2 ^ 59
def prefixEnd_2440610 : Nat := 4983230072969 + 3 ^ 40 * 2440610 * 2
def baseEnd_2440610 : Nat := 417735340056600445283615

theorem tailTrace_2440610 : CollatzResearch.WordTrace tailWord_2440610 prefixEnd_2440610 417735340056600445283615 := by
  unfold tailWord_2440610
  simp only [CollatzResearch.WordTrace]
  refine ⟨22254089922023566962033821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59344239792062845232090189 22254089922023566962033821)
  ·
    refine ⟨8345283720758837610762683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22254089922023566962033821 8345283720758837610762683)
    ·
      refine ⟨12517925581138256416144025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8345283720758837610762683 12517925581138256416144025)
      ·
        refine ⟨9388444185853692312108019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12517925581138256416144025 9388444185853692312108019)
        ·
          refine ⟨14082666278780538468162029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9388444185853692312108019 14082666278780538468162029)
          ·
            refine ⟨5280999854542701925560761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14082666278780538468162029 5280999854542701925560761)
            ·
              refine ⟨3960749890907026444170571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5280999854542701925560761 3960749890907026444170571)
              ·
                refine ⟨5941124836360539666255857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3960749890907026444170571 5941124836360539666255857)
                ·
                  refine ⟨4455843627270404749691893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5941124836360539666255857 4455843627270404749691893)
                  ·
                    refine ⟨417735340056600445283615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4455843627270404749691893 417735340056600445283615)
                    ·
                      rfl

theorem cell23_2440610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 1, 2, 5].length) (baseStart_2440610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2440610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2440610 prefixEnd_2440610 := by exact prefixLift 2440610
  have htrace : WordTrace (prefixWord ++ tailWord_2440610) baseStart_2440610 baseEnd_2440610 := by
    simpa [prefixWord, tailWord_2440610, baseEnd_2440610] using wordTrace_append hprefix tailTrace_2440610
  have hstable : (prefixWord ++ tailWord_2440610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2440610).length < 2 ^ (prefixWord ++ tailWord_2440610).sum := by decide
  have hdescent : baseEnd_2440610 < baseStart_2440610 := by decide
  rcases family_descends (prefixWord ++ tailWord_2440610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2440613 : List Nat := [1, 3, 1, 2, 1, 1, 2, 1, 3, 6, 2]
def baseStart_2440613 : Nat := 118140960795 + 2440613 * 2 ^ 59
def prefixEnd_2440613 : Nat := 4983230072969 + 3 ^ 40 * 2440613 * 2
def baseEnd_2440613 : Nat := 1253207560611764824113331

theorem tailTrace_2440613 : CollatzResearch.WordTrace tailWord_2440613 prefixEnd_2440613 1253207560611764824113331 := by
  unfold tailWord_2440613
  simp only [CollatzResearch.WordTrace]
  refine ⟨89016469107083399360494493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59344312738055599573662995 89016469107083399360494493)
  ·
    refine ⟨33381175915156274760185435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89016469107083399360494493 33381175915156274760185435)
    ·
      refine ⟨50071763872734412140278153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33381175915156274760185435 50071763872734412140278153)
      ·
        refine ⟨37553822904550809105208615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50071763872734412140278153 37553822904550809105208615)
        ·
          refine ⟨56330734356826213657812923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37553822904550809105208615 56330734356826213657812923)
          ·
            refine ⟨84496101535239320486719385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56330734356826213657812923 84496101535239320486719385)
            ·
              refine ⟨63372076151429490365039539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84496101535239320486719385 63372076151429490365039539)
              ·
                refine ⟨95058114227144235547559309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63372076151429490365039539 95058114227144235547559309)
                ·
                  refine ⟨35646792835179088330334741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 95058114227144235547559309 35646792835179088330334741)
                  ·
                    refine ⟨1670943414149019765484441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 35646792835179088330334741 1670943414149019765484441)
                    ·
                      refine ⟨1253207560611764824113331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1670943414149019765484441 1253207560611764824113331)
                      ·
                        rfl

theorem cell23_2440613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 3, 6, 2].length) (baseStart_2440613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2440613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2440613 prefixEnd_2440613 := by exact prefixLift 2440613
  have htrace : WordTrace (prefixWord ++ tailWord_2440613) baseStart_2440613 baseEnd_2440613 := by
    simpa [prefixWord, tailWord_2440613, baseEnd_2440613] using wordTrace_append hprefix tailTrace_2440613
  have hstable : (prefixWord ++ tailWord_2440613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2440613).length < 2 ^ (prefixWord ++ tailWord_2440613).sum := by decide
  have hdescent : baseEnd_2440613 < baseStart_2440613 := by decide
  rcases family_descends (prefixWord ++ tailWord_2440613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2440656 : List Nat := [2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 6]
def baseStart_2440656 : Nat := 118140960795 + 2440656 * 2 ^ 59
def prefixEnd_2440656 : Nat := 4983230072969 + 3 ^ 40 * 2440656 * 2
def baseEnd_2440656 : Nat := 1253229640279908155875633

theorem tailTrace_2440656 : CollatzResearch.WordTrace tailWord_2440656 prefixEnd_2440656 1253229640279908155875633 := by
  unfold tailWord_2440656
  simp only [CollatzResearch.WordTrace]
  refine ⟨44509018722963808852154911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59345358297285078469539881 44509018722963808852154911)
  ·
    refine ⟨66763528084445713278232367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44509018722963808852154911 66763528084445713278232367)
    ·
      refine ⟨100145292126668569917348551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66763528084445713278232367 100145292126668569917348551)
      ·
        refine ⟨150217938190002854876022827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100145292126668569917348551 150217938190002854876022827)
        ·
          refine ⟨225326907285004282314034241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150217938190002854876022827 225326907285004282314034241)
          ·
            refine ⟨168995180463753211735525681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 225326907285004282314034241 168995180463753211735525681)
            ·
              refine ⟨126746385347814908801644261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 168995180463753211735525681 126746385347814908801644261)
              ·
                refine ⟨23764947252715295400308299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 126746385347814908801644261 23764947252715295400308299)
                ·
                  refine ⟨35647420879072943100462449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23764947252715295400308299 35647420879072943100462449)
                  ·
                    refine ⟨26735565659304707325346837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35647420879072943100462449 26735565659304707325346837)
                    ·
                      refine ⟨1253229640279908155875633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26735565659304707325346837 1253229640279908155875633)
                      ·
                        rfl

theorem cell23_2440656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 6].length) (baseStart_2440656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2440656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2440656 prefixEnd_2440656 := by exact prefixLift 2440656
  have htrace : WordTrace (prefixWord ++ tailWord_2440656) baseStart_2440656 baseEnd_2440656 := by
    simpa [prefixWord, tailWord_2440656, baseEnd_2440656] using wordTrace_append hprefix tailTrace_2440656
  have hstable : (prefixWord ++ tailWord_2440656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2440656).length < 2 ^ (prefixWord ++ tailWord_2440656).sum := by decide
  have hdescent : baseEnd_2440656 < baseStart_2440656 := by decide
  rcases family_descends (prefixWord ++ tailWord_2440656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2440680 : List Nat := [2, 1, 4, 1, 1, 2, 1, 2, 5, 1, 3]
def baseStart_2440680 : Nat := 118140960795 + 2440680 * 2 ^ 59
def prefixEnd_2440680 : Nat := 4983230072969 + 3 ^ 40 * 2440680 * 2
def baseEnd_2440680 : Nat := 1253241963815616061975523

theorem tailTrace_2440680 : CollatzResearch.WordTrace tailWord_2440680 prefixEnd_2440680 1253241963815616061975523 := by
  unfold tailWord_2440680
  simp only [CollatzResearch.WordTrace]
  refine ⟨44509456398920334901591747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59345941865227113202122329 44509456398920334901591747)
  ·
    refine ⟨66764184598380502352387621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44509456398920334901591747 66764184598380502352387621)
    ·
      refine ⟨12518284612196344191072679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66764184598380502352387621 12518284612196344191072679)
      ·
        refine ⟨18777426918294516286609019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12518284612196344191072679 18777426918294516286609019)
        ·
          refine ⟨28166140377441774429913529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18777426918294516286609019 28166140377441774429913529)
          ·
            refine ⟨21124605283081330822435147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28166140377441774429913529 21124605283081330822435147)
            ·
              refine ⟨31686907924621996233652721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21124605283081330822435147 31686907924621996233652721)
              ·
                refine ⟨23765180943466497175239541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31686907924621996233652721 23765180943466497175239541)
                ·
                  refine ⟨2227985713449984110178707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23765180943466497175239541 2227985713449984110178707)
                  ·
                    refine ⟨3341978570174976165268061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2227985713449984110178707 3341978570174976165268061)
                    ·
                      refine ⟨1253241963815616061975523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3341978570174976165268061 1253241963815616061975523)
                      ·
                        rfl

theorem cell23_2440680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 2, 5, 1, 3].length) (baseStart_2440680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2440680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2440680 prefixEnd_2440680 := by exact prefixLift 2440680
  have htrace : WordTrace (prefixWord ++ tailWord_2440680) baseStart_2440680 baseEnd_2440680 := by
    simpa [prefixWord, tailWord_2440680, baseEnd_2440680] using wordTrace_append hprefix tailTrace_2440680
  have hstable : (prefixWord ++ tailWord_2440680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2440680).length < 2 ^ (prefixWord ++ tailWord_2440680).sum := by decide
  have hdescent : baseEnd_2440680 < baseStart_2440680 := by decide
  rcases family_descends (prefixWord ++ tailWord_2440680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2440703 : List Nat := [1, 1, 2, 2, 1, 2, 2, 4, 3, 1, 4]
def baseStart_2440703 : Nat := 118140960795 + 2440703 * 2 ^ 59
def prefixEnd_2440703 : Nat := 4983230072969 + 3 ^ 40 * 2440703 * 2
def baseEnd_2440703 : Nat := 1253253773870669471987917

theorem tailTrace_2440703 : CollatzResearch.WordTrace tailWord_2440703 prefixEnd_2440703 1253253773870669471987917 := by
  unfold tailWord_2440703
  simp only [CollatzResearch.WordTrace]
  refine ⟨89019751676757344731270763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59346501117838229820847175 89019751676757344731270763)
  ·
    refine ⟨133529627515136017096906145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89019751676757344731270763 133529627515136017096906145)
    ·
      refine ⟨100147220636352012822679609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133529627515136017096906145 100147220636352012822679609)
      ·
        refine ⟨75110415477264009617009707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100147220636352012822679609 75110415477264009617009707)
        ·
          refine ⟨112665623215896014425514561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75110415477264009617009707 112665623215896014425514561)
          ·
            refine ⟨84499217411922010819135921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112665623215896014425514561 84499217411922010819135921)
            ·
              refine ⟨63374413058941508114351941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84499217411922010819135921 63374413058941508114351941)
              ·
                refine ⟨11882702448551532771440989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63374413058941508114351941 11882702448551532771440989)
                ·
                  refine ⟨4456013418206824789290371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11882702448551532771440989 4456013418206824789290371)
                  ·
                    refine ⟨6684020127310237183935557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4456013418206824789290371 6684020127310237183935557)
                    ·
                      refine ⟨1253253773870669471987917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6684020127310237183935557 1253253773870669471987917)
                      ·
                        rfl

theorem cell23_2440703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 4, 3, 1, 4].length) (baseStart_2440703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2440703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2440703 prefixEnd_2440703 := by exact prefixLift 2440703
  have htrace : WordTrace (prefixWord ++ tailWord_2440703) baseStart_2440703 baseEnd_2440703 := by
    simpa [prefixWord, tailWord_2440703, baseEnd_2440703] using wordTrace_append hprefix tailTrace_2440703
  have hstable : (prefixWord ++ tailWord_2440703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2440703).length < 2 ^ (prefixWord ++ tailWord_2440703).sum := by decide
  have hdescent : baseEnd_2440703 < baseStart_2440703 := by decide
  rcases family_descends (prefixWord ++ tailWord_2440703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2440750 : List Nat := [4, 1, 3, 1, 2, 1, 1, 2, 1, 1, 6]
def baseStart_2440750 : Nat := 118140960795 + 2440750 * 2 ^ 59
def prefixEnd_2440750 : Nat := 4983230072969 + 3 ^ 40 * 2440750 * 2
def baseEnd_2440750 : Nat := 1253277907461430788100201

theorem tailTrace_2440750 : CollatzResearch.WordTrace tailWord_2440750 prefixEnd_2440750 1253277907461430788100201 := by
  unfold tailWord_2440750
  simp only [CollatzResearch.WordTrace]
  refine ⟨11127683238448383969778963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59347643938391381172154469 11127683238448383969778963)
  ·
    refine ⟨16691524857672575954668445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11127683238448383969778963 16691524857672575954668445)
    ·
      refine ⟨6259321821627215983000667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16691524857672575954668445 6259321821627215983000667)
      ·
        refine ⟨9388982732440823974501001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6259321821627215983000667 9388982732440823974501001)
        ·
          refine ⟨7041737049330617980875751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9388982732440823974501001 7041737049330617980875751)
          ·
            refine ⟨10562605573995926971313627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7041737049330617980875751 10562605573995926971313627)
            ·
              refine ⟨15843908360993890456970441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10562605573995926971313627 15843908360993890456970441)
              ·
                refine ⟨11882931270745417842727831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15843908360993890456970441 11882931270745417842727831)
                ·
                  refine ⟨17824396906118126764091747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11882931270745417842727831 17824396906118126764091747)
                  ·
                    refine ⟨26736595359177190146137621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17824396906118126764091747 26736595359177190146137621)
                    ·
                      refine ⟨1253277907461430788100201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26736595359177190146137621 1253277907461430788100201)
                      ·
                        rfl

theorem cell23_2440750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_2440750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2440750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2440750 prefixEnd_2440750 := by exact prefixLift 2440750
  have htrace : WordTrace (prefixWord ++ tailWord_2440750) baseStart_2440750 baseEnd_2440750 := by
    simpa [prefixWord, tailWord_2440750, baseEnd_2440750] using wordTrace_append hprefix tailTrace_2440750
  have hstable : (prefixWord ++ tailWord_2440750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2440750).length < 2 ^ (prefixWord ++ tailWord_2440750).sum := by decide
  have hdescent : baseEnd_2440750 < baseStart_2440750 := by decide
  rcases family_descends (prefixWord ++ tailWord_2440750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2440793 : List Nat := [1, 2, 1, 2, 2, 1, 1, 2, 4, 3, 4]
def baseStart_2440793 : Nat := 118140960795 + 2440793 * 2 ^ 59
def prefixEnd_2440793 : Nat := 4983230072969 + 3 ^ 40 * 2440793 * 2
def baseEnd_2440793 : Nat := 1253299987129574119862503

theorem tailTrace_2440793 : CollatzResearch.WordTrace tailWord_2440793 prefixEnd_2440793 1253299987129574119862503 := by
  unfold tailWord_2440793
  simp only [CollatzResearch.WordTrace]
  refine ⟨89023034246431290102047033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59348689497620860068031355 89023034246431290102047033)
  ·
    refine ⟨66767275684823467576535275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89023034246431290102047033 66767275684823467576535275)
    ·
      refine ⟨100150913527235201364802913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66767275684823467576535275 100150913527235201364802913)
      ·
        refine ⟨75113185145426401023602185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100150913527235201364802913 75113185145426401023602185)
        ·
          refine ⟨56334888859069800767701639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75113185145426401023602185 56334888859069800767701639)
          ·
            refine ⟨84502333288604701151552459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56334888859069800767701639 84502333288604701151552459)
            ·
              refine ⟨126753499932907051727328689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84502333288604701151552459 126753499932907051727328689)
              ·
                refine ⟨95065124949680288795496517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 126753499932907051727328689 95065124949680288795496517)
                ·
                  refine ⟨17824710928065054149155597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 95065124949680288795496517 17824710928065054149155597)
                  ·
                    refine ⟨6684266598024395305933349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17824710928065054149155597 6684266598024395305933349)
                    ·
                      refine ⟨1253299987129574119862503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6684266598024395305933349 1253299987129574119862503)
                      ·
                        rfl

theorem cell23_2440793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 4, 3, 4].length) (baseStart_2440793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2440793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2440793 prefixEnd_2440793 := by exact prefixLift 2440793
  have htrace : WordTrace (prefixWord ++ tailWord_2440793) baseStart_2440793 baseEnd_2440793 := by
    simpa [prefixWord, tailWord_2440793, baseEnd_2440793] using wordTrace_append hprefix tailTrace_2440793
  have hstable : (prefixWord ++ tailWord_2440793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2440793).length < 2 ^ (prefixWord ++ tailWord_2440793).sum := by decide
  have hdescent : baseEnd_2440793 < baseStart_2440793 := by decide
  rcases family_descends (prefixWord ++ tailWord_2440793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2440804 : List Nat := [2, 3, 1, 1, 2, 4, 2, 2, 2, 1, 3]
def baseStart_2440804 : Nat := 118140960795 + 2440804 * 2 ^ 59
def prefixEnd_2440804 : Nat := 4983230072969 + 3 ^ 40 * 2440804 * 2
def baseEnd_2440804 : Nat := 1253305635416773576824953

theorem tailTrace_2440804 : CollatzResearch.WordTrace tailWord_2440804 prefixEnd_2440804 1253305635416773576824953 := by
  unfold tailWord_2440804
  simp only [CollatzResearch.WordTrace]
  refine ⟨44511717724695719490348733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59348956966260959320464977 44511717724695719490348733)
  ·
    refine ⟨16691894146760894808880775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44511717724695719490348733 16691894146760894808880775)
    ·
      refine ⟨25037841220141342213321163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16691894146760894808880775 25037841220141342213321163)
      ·
        refine ⟨37556761830212013319981745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25037841220141342213321163 37556761830212013319981745)
        ·
          refine ⟨28167571372659009989986309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37556761830212013319981745 28167571372659009989986309)
          ·
            refine ⟨5281419632373564373122433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28167571372659009989986309 5281419632373564373122433)
            ·
              refine ⟨3961064724280173279841825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5281419632373564373122433 3961064724280173279841825)
              ·
                refine ⟨2970798543210129959881369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3961064724280173279841825 2970798543210129959881369)
                ·
                  refine ⟨2228098907407597469911027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2970798543210129959881369 2228098907407597469911027)
                  ·
                    refine ⟨3342148361111396204866541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2228098907407597469911027 3342148361111396204866541)
                    ·
                      refine ⟨1253305635416773576824953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3342148361111396204866541 1253305635416773576824953)
                      ·
                        rfl

theorem cell23_2440804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 2, 2, 1, 3].length) (baseStart_2440804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2440804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2440804 prefixEnd_2440804 := by exact prefixLift 2440804
  have htrace : WordTrace (prefixWord ++ tailWord_2440804) baseStart_2440804 baseEnd_2440804 := by
    simpa [prefixWord, tailWord_2440804, baseEnd_2440804] using wordTrace_append hprefix tailTrace_2440804
  have hstable : (prefixWord ++ tailWord_2440804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2440804).length < 2 ^ (prefixWord ++ tailWord_2440804).sum := by decide
  have hdescent : baseEnd_2440804 < baseStart_2440804 := by decide
  rcases family_descends (prefixWord ++ tailWord_2440804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2440810 : List Nat := [3, 1, 3, 2, 1, 2, 1, 1, 2, 3, 4]
def baseStart_2440810 : Nat := 118140960795 + 2440810 * 2 ^ 59
def prefixEnd_2440810 : Nat := 4983230072969 + 3 ^ 40 * 2440810 * 2
def baseEnd_2440810 : Nat := 1253308716300700553349925

theorem tailTrace_2440810 : CollatzResearch.WordTrace tailWord_2440810 prefixEnd_2440810 1253308716300700553349925 := by
  unfold tailWord_2440810
  simp only [CollatzResearch.WordTrace]
  refine ⟨22255913571842425501353971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59349102858246468003610589 22255913571842425501353971)
  ·
    refine ⟨33383870357763638252030957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22255913571842425501353971 33383870357763638252030957)
    ·
      refine ⟨12518951384161364344511609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33383870357763638252030957 12518951384161364344511609)
      ·
        refine ⟨9389213538121023258383707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12518951384161364344511609 9389213538121023258383707)
        ·
          refine ⟨14083820307181534887575561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9389213538121023258383707 14083820307181534887575561)
          ·
            refine ⟨10562865230386151165681671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14083820307181534887575561 10562865230386151165681671)
            ·
              refine ⟨15844297845579226748522507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10562865230386151165681671 15844297845579226748522507)
              ·
                refine ⟨23766446768368840122783761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15844297845579226748522507 23766446768368840122783761)
                ·
                  refine ⟨17824835076276630092087821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23766446768368840122783761 17824835076276630092087821)
                  ·
                    refine ⟨6684313153603736284532933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17824835076276630092087821 6684313153603736284532933)
                    ·
                      refine ⟨1253308716300700553349925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6684313153603736284532933 1253308716300700553349925)
                      ·
                        rfl

theorem cell23_2440810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_2440810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2440810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2440810 prefixEnd_2440810 := by exact prefixLift 2440810
  have htrace : WordTrace (prefixWord ++ tailWord_2440810) baseStart_2440810 baseEnd_2440810 := by
    simpa [prefixWord, tailWord_2440810, baseEnd_2440810] using wordTrace_append hprefix tailTrace_2440810
  have hstable : (prefixWord ++ tailWord_2440810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2440810).length < 2 ^ (prefixWord ++ tailWord_2440810).sum := by decide
  have hdescent : baseEnd_2440810 < baseStart_2440810 := by decide
  rcases family_descends (prefixWord ++ tailWord_2440810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2440827 : List Nat := [1, 1, 1, 1, 1, 4, 6, 1, 1, 4, 2]
def baseStart_2440827 : Nat := 118140960795 + 2440827 * 2 ^ 59
def prefixEnd_2440827 : Nat := 4983230072969 + 3 ^ 40 * 2440827 * 2
def baseEnd_2440827 : Nat := 1253317445471826986837347

theorem tailTrace_2440827 : CollatzResearch.WordTrace tailWord_2440827 prefixEnd_2440827 1253317445471826986837347 := by
  unfold tailWord_2440827
  simp only [CollatzResearch.WordTrace]
  refine ⟨89024274328308113908784735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59349516218872075939189823 89024274328308113908784735)
  ·
    refine ⟨133536411492462170863177103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89024274328308113908784735 133536411492462170863177103)
    ·
      refine ⟨200304617238693256294765655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133536411492462170863177103 200304617238693256294765655)
      ·
        refine ⟨300456925858039884442148483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200304617238693256294765655 300456925858039884442148483)
        ·
          refine ⟨450685388787059826663222725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 300456925858039884442148483 450685388787059826663222725)
          ·
            refine ⟨84503510397573717499354261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 450685388787059826663222725 84503510397573717499354261)
            ·
              refine ⟨3961102049886268007782231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 84503510397573717499354261 3961102049886268007782231)
              ·
                refine ⟨5941653074829402011673347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3961102049886268007782231 5941653074829402011673347)
                ·
                  refine ⟨8912479612244103017510021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5941653074829402011673347 8912479612244103017510021)
                  ·
                    refine ⟨1671089927295769315783129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8912479612244103017510021 1671089927295769315783129)
                    ·
                      refine ⟨1253317445471826986837347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1671089927295769315783129 1253317445471826986837347)
                      ·
                        rfl

theorem cell23_2440827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 1, 1, 4, 2].length) (baseStart_2440827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2440827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2440827 prefixEnd_2440827 := by exact prefixLift 2440827
  have htrace : WordTrace (prefixWord ++ tailWord_2440827) baseStart_2440827 baseEnd_2440827 := by
    simpa [prefixWord, tailWord_2440827, baseEnd_2440827] using wordTrace_append hprefix tailTrace_2440827
  have hstable : (prefixWord ++ tailWord_2440827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2440827).length < 2 ^ (prefixWord ++ tailWord_2440827).sum := by decide
  have hdescent : baseEnd_2440827 < baseStart_2440827 := by decide
  rcases family_descends (prefixWord ++ tailWord_2440827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2440877 : List Nat := [1, 5, 2, 1, 1, 1, 1, 3, 2, 3, 3]
def baseStart_2440877 : Nat := 118140960795 + 2440877 * 2 ^ 59
def prefixEnd_2440877 : Nat := 4983230072969 + 3 ^ 40 * 2440877 * 2
def baseEnd_2440877 : Nat := 1253343119504551791212117

theorem tailTrace_2440877 : CollatzResearch.WordTrace tailWord_2440877 prefixEnd_2440877 1253343119504551791212117 := by
  unfold tailWord_2440877
  simp only [CollatzResearch.WordTrace]
  refine ⟨89026097978126972448104885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59350731985417981632069923 89026097978126972448104885)
  ·
    refine ⟨8346196685449403667009833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 89026097978126972448104885 8346196685449403667009833)
    ·
      refine ⟨6259647514087052750257375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8346196685449403667009833 6259647514087052750257375)
      ·
        refine ⟨9389471271130579125386063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6259647514087052750257375 9389471271130579125386063)
        ·
          refine ⟨14084206906695868688079095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9389471271130579125386063 14084206906695868688079095)
          ·
            refine ⟨21126310360043803032118643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14084206906695868688079095 21126310360043803032118643)
            ·
              refine ⟨31689465540065704548177965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21126310360043803032118643 31689465540065704548177965)
              ·
                refine ⟨11883549577524639205566737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31689465540065704548177965 11883549577524639205566737)
                ·
                  refine ⟨8912662183143479404175053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11883549577524639205566737 8912662183143479404175053)
                  ·
                    refine ⟨3342248318678804776565645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8912662183143479404175053 3342248318678804776565645)
                    ·
                      refine ⟨1253343119504551791212117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3342248318678804776565645 1253343119504551791212117)
                      ·
                        rfl

theorem cell23_2440877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 3, 2, 3, 3].length) (baseStart_2440877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2440877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2440877 prefixEnd_2440877 := by exact prefixLift 2440877
  have htrace : WordTrace (prefixWord ++ tailWord_2440877) baseStart_2440877 baseEnd_2440877 := by
    simpa [prefixWord, tailWord_2440877, baseEnd_2440877] using wordTrace_append hprefix tailTrace_2440877
  have hstable : (prefixWord ++ tailWord_2440877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2440877).length < 2 ^ (prefixWord ++ tailWord_2440877).sum := by decide
  have hdescent : baseEnd_2440877 < baseStart_2440877 := by decide
  rcases family_descends (prefixWord ++ tailWord_2440877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2440878 : List Nat := [4, 1, 4, 1, 2, 2, 1, 1, 1, 4, 2]
def baseStart_2440878 : Nat := 118140960795 + 2440878 * 2 ^ 59
def prefixEnd_2440878 : Nat := 4983230072969 + 3 ^ 40 * 2440878 * 2
def baseEnd_2440878 : Nat := 1253343632985206287299613

theorem tailTrace_2440878 : CollatzResearch.WordTrace tailWord_2440878 prefixEnd_2440878 1253343632985206287299613 := by
  unfold tailWord_2440878
  simp only [CollatzResearch.WordTrace]
  refine ⟨11128266806390418702361411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59350756300748899745927525 11128266806390418702361411)
  ·
    refine ⟨16692400209585628053542117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11128266806390418702361411 16692400209585628053542117)
    ·
      refine ⟨3129825039297305260039147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16692400209585628053542117 3129825039297305260039147)
      ·
        refine ⟨4694737558945957890058721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3129825039297305260039147 4694737558945957890058721)
        ·
          refine ⟨3521053169209468417544041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4694737558945957890058721 3521053169209468417544041)
          ·
            refine ⟨2640789876907101313158031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3521053169209468417544041 2640789876907101313158031)
            ·
              refine ⟨3961184815360651969737047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2640789876907101313158031 3961184815360651969737047)
              ·
                refine ⟨5941777223040977954605571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3961184815360651969737047 5941777223040977954605571)
                ·
                  refine ⟨8912665834561466931908357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5941777223040977954605571 8912665834561466931908357)
                  ·
                    refine ⟨1671124843980275049732817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8912665834561466931908357 1671124843980275049732817)
                    ·
                      refine ⟨1253343632985206287299613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1671124843980275049732817 1253343632985206287299613)
                      ·
                        rfl

theorem cell23_2440878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 1, 1, 4, 2].length) (baseStart_2440878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2440878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2440878 prefixEnd_2440878 := by exact prefixLift 2440878
  have htrace : WordTrace (prefixWord ++ tailWord_2440878) baseStart_2440878 baseEnd_2440878 := by
    simpa [prefixWord, tailWord_2440878, baseEnd_2440878] using wordTrace_append hprefix tailTrace_2440878
  have hstable : (prefixWord ++ tailWord_2440878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2440878).length < 2 ^ (prefixWord ++ tailWord_2440878).sum := by decide
  have hdescent : baseEnd_2440878 < baseStart_2440878 := by decide
  rcases family_descends (prefixWord ++ tailWord_2440878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2440918 : List Nat := [5, 2, 1, 3, 2, 1, 1, 1, 7]
def baseStart_2440918 : Nat := 118140960795 + 2440918 * 2 ^ 59
def prefixEnd_2440918 : Nat := 4983230072969 + 3 ^ 40 * 2440918 * 2
def baseEnd_2440918 : Nat := 139262685801265125644381

theorem tailTrace_2440918 : CollatzResearch.WordTrace tailWord_2440918 prefixEnd_2440918 139262685801265125644381 := by
  unfold tailWord_2440918
  simp only [CollatzResearch.WordTrace]
  refine ⟨5564224585686152278146713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 59351728913985624300231605 5564224585686152278146713)
  ·
    refine ⟨4173168439264614208610035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5564224585686152278146713 4173168439264614208610035)
    ·
      refine ⟨6259752658896921312915053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4173168439264614208610035 6259752658896921312915053)
      ·
        refine ⟨2347407247086345492343145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6259752658896921312915053 2347407247086345492343145)
        ·
          refine ⟨1760555435314759119257359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2347407247086345492343145 1760555435314759119257359)
          ·
            refine ⟨2640833152972138678886039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1760555435314759119257359 2640833152972138678886039)
            ·
              refine ⟨3961249729458208018329059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2640833152972138678886039 3961249729458208018329059)
              ·
                refine ⟨5941874594187312027493589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3961249729458208018329059 5941874594187312027493589)
                ·
                  refine ⟨139262685801265125644381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5941874594187312027493589 139262685801265125644381)
                  ·
                    rfl

theorem cell23_2440918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 1, 7].length) (baseStart_2440918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2440918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2440918 prefixEnd_2440918 := by exact prefixLift 2440918
  have htrace : WordTrace (prefixWord ++ tailWord_2440918) baseStart_2440918 baseEnd_2440918 := by
    simpa [prefixWord, tailWord_2440918, baseEnd_2440918] using wordTrace_append hprefix tailTrace_2440918
  have hstable : (prefixWord ++ tailWord_2440918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2440918).length < 2 ^ (prefixWord ++ tailWord_2440918).sum := by decide
  have hdescent : baseEnd_2440918 < baseStart_2440918 := by decide
  rcases family_descends (prefixWord ++ tailWord_2440918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2440924 : List Nat := [2, 2, 5, 1, 2, 1, 1, 1, 1, 2, 5]
def baseStart_2440924 : Nat := 118140960795 + 2440924 * 2 ^ 59
def prefixEnd_2440924 : Nat := 4983230072969 + 3 ^ 40 * 2440924 * 2
def baseEnd_2440924 : Nat := 1253367253095313107324401

theorem tailTrace_2440924 : CollatzResearch.WordTrace tailWord_2440924 prefixEnd_2440924 1253367253095313107324401 := by
  unfold tailWord_2440924
  simp only [CollatzResearch.WordTrace]
  refine ⟨44513906104478349737532913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59351874805971132983377217 44513906104478349737532913)
  ·
    refine ⟨33385429578358762303149685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44513906104478349737532913 33385429578358762303149685)
    ·
      refine ⟨3129884022971133965920283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33385429578358762303149685 3129884022971133965920283)
      ·
        refine ⟨4694826034456700948880425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3129884022971133965920283 4694826034456700948880425)
        ·
          refine ⟨3521119525842525711660319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4694826034456700948880425 3521119525842525711660319)
          ·
            refine ⟨5281679288763788567490479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3521119525842525711660319 5281679288763788567490479)
            ·
              refine ⟨7922518933145682851235719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5281679288763788567490479 7922518933145682851235719)
              ·
                refine ⟨11883778399718524276853579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7922518933145682851235719 11883778399718524276853579)
                ·
                  refine ⟨17825667599577786415280369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11883778399718524276853579 17825667599577786415280369)
                  ·
                    refine ⟨13369250699683339811460277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17825667599577786415280369 13369250699683339811460277)
                    ·
                      refine ⟨1253367253095313107324401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13369250699683339811460277 1253367253095313107324401)
                      ·
                        rfl

theorem cell23_2440924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_2440924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2440924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2440924 prefixEnd_2440924 := by exact prefixLift 2440924
  have htrace : WordTrace (prefixWord ++ tailWord_2440924) baseStart_2440924 baseEnd_2440924 := by
    simpa [prefixWord, tailWord_2440924, baseEnd_2440924] using wordTrace_append hprefix tailTrace_2440924
  have hstable : (prefixWord ++ tailWord_2440924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2440924).length < 2 ^ (prefixWord ++ tailWord_2440924).sum := by decide
  have hdescent : baseEnd_2440924 < baseStart_2440924 := by decide
  rcases family_descends (prefixWord ++ tailWord_2440924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2440977 : List Nat := [1, 2, 2, 1, 1, 3, 1, 2, 3, 5, 2]
def baseStart_2440977 : Nat := 118140960795 + 2440977 * 2 ^ 59
def prefixEnd_2440977 : Nat := 4983230072969 + 3 ^ 40 * 2440977 * 2
def baseEnd_2440977 : Nat := 1253394467570001399961657

theorem tailTrace_2440977 : CollatzResearch.WordTrace tailWord_2440977 prefixEnd_2440977 1253394467570001399961657 := by
  unfold tailWord_2440977
  simp only [CollatzResearch.WordTrace]
  refine ⟨89029745277764689526745185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59353163518509793017830123 89029745277764689526745185)
  ·
    refine ⟨66772308958323517145058889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89029745277764689526745185 66772308958323517145058889)
    ·
      refine ⟨50079231718742637858794167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66772308958323517145058889 50079231718742637858794167)
      ·
        refine ⟨75118847578113956788191251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50079231718742637858794167 75118847578113956788191251)
        ·
          refine ⟨112678271367170935182286877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75118847578113956788191251 112678271367170935182286877)
          ·
            refine ⟨42254351762689100693357579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 112678271367170935182286877 42254351762689100693357579)
            ·
              refine ⟨63381527644033651040036369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42254351762689100693357579 63381527644033651040036369)
              ·
                refine ⟨47536145733025238280027277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63381527644033651040036369 47536145733025238280027277)
                ·
                  refine ⟨17826054649884464355010229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47536145733025238280027277 17826054649884464355010229)
                  ·
                    refine ⟨1671192623426668533282209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17826054649884464355010229 1671192623426668533282209)
                    ·
                      refine ⟨1253394467570001399961657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1671192623426668533282209 1253394467570001399961657)
                      ·
                        rfl

theorem cell23_2440977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 5, 2].length) (baseStart_2440977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2440977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2440977 prefixEnd_2440977 := by exact prefixLift 2440977
  have htrace : WordTrace (prefixWord ++ tailWord_2440977) baseStart_2440977 baseEnd_2440977 := by
    simpa [prefixWord, tailWord_2440977, baseEnd_2440977] using wordTrace_append hprefix tailTrace_2440977
  have hstable : (prefixWord ++ tailWord_2440977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2440977).length < 2 ^ (prefixWord ++ tailWord_2440977).sum := by decide
  have hdescent : baseEnd_2440977 < baseStart_2440977 := by decide
  rcases family_descends (prefixWord ++ tailWord_2440977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2440978 : List Nat := [3, 2, 4, 1, 1, 2, 1, 4, 1, 4]
def baseStart_2440978 : Nat := 118140960795 + 2440978 * 2 ^ 59
def prefixEnd_2440978 : Nat := 4983230072969 + 3 ^ 40 * 2440978 * 2
def baseEnd_2440978 : Nat := 417798327016885298683051

theorem tailTrace_2440978 : CollatzResearch.WordTrace tailWord_2440978 prefixEnd_2440978 417798327016885298683051 := by
  unfold tailWord_2440978
  simp only [CollatzResearch.WordTrace]
  refine ⟨22257445437690266674382897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59353187833840711131687725 22257445437690266674382897)
  ·
    refine ⟨16693084078267700005787173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22257445437690266674382897 16693084078267700005787173)
    ·
      refine ⟨3129953264675193751085095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16693084078267700005787173 3129953264675193751085095)
      ·
        refine ⟨4694929897012790626627643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3129953264675193751085095 4694929897012790626627643)
        ·
          refine ⟨7042394845519185939941465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4694929897012790626627643 7042394845519185939941465)
          ·
            refine ⟨5281796134139389454956099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7042394845519185939941465 5281796134139389454956099)
            ·
              refine ⟨7922694201209084182434149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5281796134139389454956099 7922694201209084182434149)
              ·
                refine ⟨1485505162726703284206403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7922694201209084182434149 1485505162726703284206403)
                ·
                  refine ⟨2228257744090054926309605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1485505162726703284206403 2228257744090054926309605)
                  ·
                    refine ⟨417798327016885298683051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2228257744090054926309605 417798327016885298683051)
                    ·
                      rfl

theorem cell23_2440978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_2440978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2440978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2440978 prefixEnd_2440978 := by exact prefixLift 2440978
  have htrace : WordTrace (prefixWord ++ tailWord_2440978) baseStart_2440978 baseEnd_2440978 := by
    simpa [prefixWord, tailWord_2440978, baseEnd_2440978] using wordTrace_append hprefix tailTrace_2440978
  have hstable : (prefixWord ++ tailWord_2440978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2440978).length < 2 ^ (prefixWord ++ tailWord_2440978).sum := by decide
  have hdescent : baseEnd_2440978 < baseStart_2440978 := by decide
  rcases family_descends (prefixWord ++ tailWord_2440978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2440994 : List Nat := [3, 3, 1, 1, 2, 1, 2, 2, 1, 5, 2]
def baseStart_2440994 : Nat := 118140960795 + 2440994 * 2 ^ 59
def prefixEnd_2440994 : Nat := 4983230072969 + 3 ^ 40 * 2440994 * 2
def baseEnd_2440994 : Nat := 1253403196741127833449079

theorem tailTrace_2440994 : CollatzResearch.WordTrace tailWord_2440994 prefixEnd_2440994 1253403196741127833449079 := by
  unfold tailWord_2440994
  simp only [CollatzResearch.WordTrace]
  refine ⟨22257591329675775357528509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59353576879135400953409357 22257591329675775357528509)
  ·
    refine ⟨8346596748628415759073191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22257591329675775357528509 8346596748628415759073191)
    ·
      refine ⟨12519895122942623638609787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8346596748628415759073191 12519895122942623638609787)
      ·
        refine ⟨18779842684413935457914681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12519895122942623638609787 18779842684413935457914681)
        ·
          refine ⟨14084882013310451593436011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18779842684413935457914681 14084882013310451593436011)
          ·
            refine ⟨21127323019965677390154017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14084882013310451593436011 21127323019965677390154017)
            ·
              refine ⟨15845492264974258042615513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21127323019965677390154017 15845492264974258042615513)
              ·
                refine ⟨11884119198730693531961635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15845492264974258042615513 11884119198730693531961635)
                ·
                  refine ⟨17826178798096040297942453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11884119198730693531961635 17826178798096040297942453)
                  ·
                    refine ⟨1671204262321503777932105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17826178798096040297942453 1671204262321503777932105)
                    ·
                      refine ⟨1253403196741127833449079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1671204262321503777932105 1253403196741127833449079)
                      ·
                        rfl

theorem cell23_2440994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 2, 1, 5, 2].length) (baseStart_2440994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2440994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2440994 prefixEnd_2440994 := by exact prefixLift 2440994
  have htrace : WordTrace (prefixWord ++ tailWord_2440994) baseStart_2440994 baseEnd_2440994 := by
    simpa [prefixWord, tailWord_2440994, baseEnd_2440994] using wordTrace_append hprefix tailTrace_2440994
  have hstable : (prefixWord ++ tailWord_2440994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2440994).length < 2 ^ (prefixWord ++ tailWord_2440994).sum := by decide
  have hdescent : baseEnd_2440994 < baseStart_2440994 := by decide
  rcases family_descends (prefixWord ++ tailWord_2440994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2441007 : List Nat := [1, 1, 2, 1, 2, 1, 2, 3, 2, 6, 2]
def baseStart_2441007 : Nat := 118140960795 + 2441007 * 2 ^ 59
def prefixEnd_2441007 : Nat := 4983230072969 + 3 ^ 40 * 2441007 * 2
def baseEnd_2441007 : Nat := 1253409871989636282586519

theorem tailTrace_2441007 : CollatzResearch.WordTrace tailWord_2441007 prefixEnd_2441007 1253409871989636282586519 := by
  unfold tailWord_2441007
  simp only [CollatzResearch.WordTrace]
  refine ⟨89030839467656004650337275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59353892978437336433558183 89030839467656004650337275)
  ·
    refine ⟨133546259201484006975505913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89030839467656004650337275 133546259201484006975505913)
    ·
      refine ⟨100159694401113005231629435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133546259201484006975505913 100159694401113005231629435)
      ·
        refine ⟨150239541601669507847444153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100159694401113005231629435 150239541601669507847444153)
        ·
          refine ⟨112679656201252130885583115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150239541601669507847444153 112679656201252130885583115)
          ·
            refine ⟨169019484301878196328374673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112679656201252130885583115 169019484301878196328374673)
            ·
              refine ⟨126764613226408647246281005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 169019484301878196328374673 126764613226408647246281005)
              ·
                refine ⟨47536729959903242717355377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 126764613226408647246281005 47536729959903242717355377)
                ·
                  refine ⟨35652547469927432038016533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47536729959903242717355377 35652547469927432038016533)
                  ·
                    refine ⟨1671213162652848376782025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 35652547469927432038016533 1671213162652848376782025)
                    ·
                      refine ⟨1253409871989636282586519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1671213162652848376782025 1253409871989636282586519)
                      ·
                        rfl

theorem cell23_2441007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 2, 6, 2].length) (baseStart_2441007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2441007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2441007 prefixEnd_2441007 := by exact prefixLift 2441007
  have htrace : WordTrace (prefixWord ++ tailWord_2441007) baseStart_2441007 baseEnd_2441007 := by
    simpa [prefixWord, tailWord_2441007, baseEnd_2441007] using wordTrace_append hprefix tailTrace_2441007
  have hstable : (prefixWord ++ tailWord_2441007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2441007).length < 2 ^ (prefixWord ++ tailWord_2441007).sum := by decide
  have hdescent : baseEnd_2441007 < baseStart_2441007 := by decide
  rcases family_descends (prefixWord ++ tailWord_2441007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2441018 : List Nat := [3, 1, 1, 1, 5, 2, 2, 3, 1, 1, 3]
def baseStart_2441018 : Nat := 118140960795 + 2441018 * 2 ^ 59
def prefixEnd_2441018 : Nat := 4983230072969 + 3 ^ 40 * 2441018 * 2
def baseEnd_2441018 : Nat := 1253415520276835739548969

theorem tailTrace_2441018 : CollatzResearch.WordTrace tailWord_2441018 prefixEnd_2441018 1253415520276835739548969 := by
  unfold tailWord_2441018
  simp only [CollatzResearch.WordTrace]
  refine ⟨22257810167654038382246927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59354160447077435685991805 22257810167654038382246927)
  ·
    refine ⟨33386715251481057573370391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22257810167654038382246927 33386715251481057573370391)
    ·
      refine ⟨50080072877221586360055587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33386715251481057573370391 50080072877221586360055587)
      ·
        refine ⟨75120109315832379540083381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50080072877221586360055587 75120109315832379540083381)
        ·
          refine ⟨7042510248359285581882817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 75120109315832379540083381 7042510248359285581882817)
          ·
            refine ⟨5281882686269464186412113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7042510248359285581882817 5281882686269464186412113)
            ·
              refine ⟨3961412014702098139809085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5281882686269464186412113 3961412014702098139809085)
              ·
                refine ⟨1485529505513286802428407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3961412014702098139809085 1485529505513286802428407)
                ·
                  refine ⟨2228294258269930203642611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1485529505513286802428407 2228294258269930203642611)
                  ·
                    refine ⟨3342441387404895305463917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2228294258269930203642611 3342441387404895305463917)
                    ·
                      refine ⟨1253415520276835739548969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3342441387404895305463917 1253415520276835739548969)
                      ·
                        rfl

theorem cell23_2441018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 3, 1, 1, 3].length) (baseStart_2441018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2441018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2441018 prefixEnd_2441018 := by exact prefixLift 2441018
  have htrace : WordTrace (prefixWord ++ tailWord_2441018) baseStart_2441018 baseEnd_2441018 := by
    simpa [prefixWord, tailWord_2441018, baseEnd_2441018] using wordTrace_append hprefix tailTrace_2441018
  have hstable : (prefixWord ++ tailWord_2441018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2441018).length < 2 ^ (prefixWord ++ tailWord_2441018).sum := by decide
  have hdescent : baseEnd_2441018 < baseStart_2441018 := by decide
  rcases family_descends (prefixWord ++ tailWord_2441018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2441021 : List Nat := [1, 4, 1, 4, 1, 1, 4, 1, 1, 5]
def baseStart_2441021 : Nat := 118140960795 + 2441021 * 2 ^ 59
def prefixEnd_2441021 : Nat := 4983230072969 + 3 ^ 40 * 2441021 * 2
def baseEnd_2441021 : Nat := 417805686906266409270485

theorem tailTrace_2441021 : CollatzResearch.WordTrace tailWord_2441021 prefixEnd_2441021 417805686906266409270485 := by
  unfold tailWord_2441021
  simp only [CollatzResearch.WordTrace]
  refine ⟨89031350089605285041346917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59354233393070190027564611 89031350089605285041346917)
  ·
    refine ⟨16693378141800990945252547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89031350089605285041346917 16693378141800990945252547)
    ·
      refine ⟨25040067212701486417878821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16693378141800990945252547 25040067212701486417878821)
      ·
        refine ⟨4695012602381528703352279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25040067212701486417878821 4695012602381528703352279)
        ·
          refine ⟨7042518903572293055028419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4695012602381528703352279 7042518903572293055028419)
          ·
            refine ⟨10563778355358439582542629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7042518903572293055028419 10563778355358439582542629)
            ·
              refine ⟨1980708441629707421726743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10563778355358439582542629 1980708441629707421726743)
              ·
                refine ⟨2971062662444561132590115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1980708441629707421726743 2971062662444561132590115)
                ·
                  refine ⟨4456593993666841698885173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2971062662444561132590115 4456593993666841698885173)
                  ·
                    refine ⟨417805686906266409270485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4456593993666841698885173 417805686906266409270485)
                    ·
                      rfl

theorem cell23_2441021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 4, 1, 1, 5].length) (baseStart_2441021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2441021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2441021 prefixEnd_2441021 := by exact prefixLift 2441021
  have htrace : WordTrace (prefixWord ++ tailWord_2441021) baseStart_2441021 baseEnd_2441021 := by
    simpa [prefixWord, tailWord_2441021, baseEnd_2441021] using wordTrace_append hprefix tailTrace_2441021
  have hstable : (prefixWord ++ tailWord_2441021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2441021).length < 2 ^ (prefixWord ++ tailWord_2441021).sum := by decide
  have hdescent : baseEnd_2441021 < baseStart_2441021 := by decide
  rcases family_descends (prefixWord ++ tailWord_2441021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2441040 : List Nat := [2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 7]
def baseStart_2441040 : Nat := 118140960795 + 2441040 * 2 ^ 59
def prefixEnd_2441040 : Nat := 4983230072969 + 3 ^ 40 * 2441040 * 2
def baseEnd_2441040 : Nat := 1253426816851234653473867

theorem tailTrace_2441040 : CollatzResearch.WordTrace tailWord_2441040 prefixEnd_2441040 1253426816851234653473867 := by
  unfold tailWord_2441040
  simp only [CollatzResearch.WordTrace]
  refine ⟨44516021538268225643144287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59354695384357634190859049 44516021538268225643144287)
  ·
    refine ⟨66774032307402338464716431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44516021538268225643144287 66774032307402338464716431)
    ·
      refine ⟨100161048461103507697074647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66774032307402338464716431 100161048461103507697074647)
      ·
        refine ⟨150241572691655261545611971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100161048461103507697074647 150241572691655261545611971)
        ·
          refine ⟨225362359037482892318417957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150241572691655261545611971 225362359037482892318417957)
          ·
            refine ⟨42255442319528042309703367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 225362359037482892318417957 42255442319528042309703367)
            ·
              refine ⟨63383163479292063464555051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42255442319528042309703367 63383163479292063464555051)
              ·
                refine ⟨95074745218938095196832577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63383163479292063464555051 95074745218938095196832577)
                ·
                  refine ⟨71306058914203571397624433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 95074745218938095196832577 71306058914203571397624433)
                  ·
                    refine ⟨53479544185652678548218325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 71306058914203571397624433 53479544185652678548218325)
                    ·
                      refine ⟨1253426816851234653473867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 53479544185652678548218325 1253426816851234653473867)
                      ·
                        rfl

theorem cell23_2441040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 7].length) (baseStart_2441040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2441040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2441040 prefixEnd_2441040 := by exact prefixLift 2441040
  have htrace : WordTrace (prefixWord ++ tailWord_2441040) baseStart_2441040 baseEnd_2441040 := by
    simpa [prefixWord, tailWord_2441040, baseEnd_2441040] using wordTrace_append hprefix tailTrace_2441040
  have hstable : (prefixWord ++ tailWord_2441040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2441040).length < 2 ^ (prefixWord ++ tailWord_2441040).sum := by decide
  have hdescent : baseEnd_2441040 < baseStart_2441040 := by decide
  rcases family_descends (prefixWord ++ tailWord_2441040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2441041 : List Nat := [1, 2, 2, 1, 5, 1, 1, 3, 3, 2, 2]
def baseStart_2441041 : Nat := 118140960795 + 2441041 * 2 ^ 59
def prefixEnd_2441041 : Nat := 4983230072969 + 3 ^ 40 * 2441041 * 2
def baseEnd_2441041 : Nat := 1253427330331889149561363

theorem tailTrace_2441041 : CollatzResearch.WordTrace tailWord_2441041 prefixEnd_2441041 1253427330331889149561363 := by
  unfold tailWord_2441041
  simp only [CollatzResearch.WordTrace]
  refine ⟨89032079549532828457074977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59354719699688552304716651 89032079549532828457074977)
  ·
    refine ⟨66774059662149621342806233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89032079549532828457074977 66774059662149621342806233)
    ·
      refine ⟨50080544746612216007104675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66774059662149621342806233 50080544746612216007104675)
      ·
        refine ⟨75120817119918324010657013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50080544746612216007104675 75120817119918324010657013)
        ·
          refine ⟨7042576604992342875999095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 75120817119918324010657013 7042576604992342875999095)
          ·
            refine ⟨10563864907488514313998643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7042576604992342875999095 10563864907488514313998643)
            ·
              refine ⟨15845797361232771470997965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10563864907488514313998643 15845797361232771470997965)
              ·
                refine ⟨5942174010462289301624237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15845797361232771470997965 5942174010462289301624237)
                ·
                  refine ⟨2228315253923358488109089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5942174010462289301624237 2228315253923358488109089)
                  ·
                    refine ⟨1671236440442518866081817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2228315253923358488109089 1671236440442518866081817)
                    ·
                      refine ⟨1253427330331889149561363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1671236440442518866081817 1253427330331889149561363)
                      ·
                        rfl

theorem cell23_2441041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 3, 3, 2, 2].length) (baseStart_2441041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2441041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2441041 prefixEnd_2441041 := by exact prefixLift 2441041
  have htrace : WordTrace (prefixWord ++ tailWord_2441041) baseStart_2441041 baseEnd_2441041 := by
    simpa [prefixWord, tailWord_2441041, baseEnd_2441041] using wordTrace_append hprefix tailTrace_2441041
  have hstable : (prefixWord ++ tailWord_2441041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2441041).length < 2 ^ (prefixWord ++ tailWord_2441041).sum := by decide
  have hdescent : baseEnd_2441041 < baseStart_2441041 := by decide
  rcases family_descends (prefixWord ++ tailWord_2441041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2441044 : List Nat := [2, 4, 1, 1, 3, 2, 1, 2, 1, 1, 5]
def baseStart_2441044 : Nat := 118140960795 + 2441044 * 2 ^ 59
def prefixEnd_2441044 : Nat := 4983230072969 + 3 ^ 40 * 2441044 * 2
def baseEnd_2441044 : Nat := 1253428870773852637823849

theorem tailTrace_2441044 : CollatzResearch.WordTrace tailWord_2441044 prefixEnd_2441044 1253428870773852637823849 := by
  unfold tailWord_2441044
  simp only [CollatzResearch.WordTrace]
  refine ⟨44516094484260979984717093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59354792645681306646289457 44516094484260979984717093)
  ·
    refine ⟨8346767715798933747134455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44516094484260979984717093 8346767715798933747134455)
    ·
      refine ⟨12520151573698400620701683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8346767715798933747134455 12520151573698400620701683)
      ·
        refine ⟨18780227360547600931052525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12520151573698400620701683 18780227360547600931052525)
        ·
          refine ⟨7042585260205350349144697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18780227360547600931052525 7042585260205350349144697)
          ·
            refine ⟨5281938945154012761858523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7042585260205350349144697 5281938945154012761858523)
            ·
              refine ⟨7922908417731019142787785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5281938945154012761858523 7922908417731019142787785)
              ·
                refine ⟨5942181313298264357090839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7922908417731019142787785 5942181313298264357090839)
                ·
                  refine ⟨8913271969947396535636259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5942181313298264357090839 8913271969947396535636259)
                  ·
                    refine ⟨13369907954921094803454389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8913271969947396535636259 13369907954921094803454389)
                    ·
                      refine ⟨1253428870773852637823849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13369907954921094803454389 1253428870773852637823849)
                      ·
                        rfl

theorem cell23_2441044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 2, 1, 1, 5].length) (baseStart_2441044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2441044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2441044 prefixEnd_2441044 := by exact prefixLift 2441044
  have htrace : WordTrace (prefixWord ++ tailWord_2441044) baseStart_2441044 baseEnd_2441044 := by
    simpa [prefixWord, tailWord_2441044, baseEnd_2441044] using wordTrace_append hprefix tailTrace_2441044
  have hstable : (prefixWord ++ tailWord_2441044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2441044).length < 2 ^ (prefixWord ++ tailWord_2441044).sum := by decide
  have hdescent : baseEnd_2441044 < baseStart_2441044 := by decide
  rcases family_descends (prefixWord ++ tailWord_2441044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2441058 : List Nat := [3, 3, 2, 1, 2, 1, 2, 2, 3, 2, 2]
def baseStart_2441058 : Nat := 118140960795 + 2441058 * 2 ^ 59
def prefixEnd_2441058 : Nat := 4983230072969 + 3 ^ 40 * 2441058 * 2
def baseEnd_2441058 : Nat := 1253436059503015583048785

theorem tailTrace_2441058 : CollatzResearch.WordTrace tailWord_2441058 prefixEnd_2441058 1253436059503015583048785 := by
  unfold tailWord_2441058
  simp only [CollatzResearch.WordTrace]
  refine ⟨22258174897617810090110957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59355133060314160240295885 22258174897617810090110957)
  ·
    refine ⟨8346815586606678783791609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22258174897617810090110957 8346815586606678783791609)
    ·
      refine ⟨6260111689955009087843707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8346815586606678783791609 6260111689955009087843707)
      ·
        refine ⟨9390167534932513631765561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6260111689955009087843707 9390167534932513631765561)
        ·
          refine ⟨7042625651199385223824171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9390167534932513631765561 7042625651199385223824171)
          ·
            refine ⟨10563938476799077835736257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7042625651199385223824171 10563938476799077835736257)
            ·
              refine ⟨7922953857599308376802193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10563938476799077835736257 7922953857599308376802193)
              ·
                refine ⟨5942215393199481282601645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7922953857599308376802193 5942215393199481282601645)
                ·
                  refine ⟨2228330772449805480975617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5942215393199481282601645 2228330772449805480975617)
                  ·
                    refine ⟨1671248079337354110731713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2228330772449805480975617 1671248079337354110731713)
                    ·
                      refine ⟨1253436059503015583048785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1671248079337354110731713 1253436059503015583048785)
                      ·
                        rfl

theorem cell23_2441058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 2, 3, 2, 2].length) (baseStart_2441058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2441058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2441058 prefixEnd_2441058 := by exact prefixLift 2441058
  have htrace : WordTrace (prefixWord ++ tailWord_2441058) baseStart_2441058 baseEnd_2441058 := by
    simpa [prefixWord, tailWord_2441058, baseEnd_2441058] using wordTrace_append hprefix tailTrace_2441058
  have hstable : (prefixWord ++ tailWord_2441058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2441058).length < 2 ^ (prefixWord ++ tailWord_2441058).sum := by decide
  have hdescent : baseEnd_2441058 < baseStart_2441058 := by decide
  rcases family_descends (prefixWord ++ tailWord_2441058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2441084 : List Nat := [2, 2, 2, 1, 1, 1, 1, 1, 7, 3, 2]
def baseStart_2441084 : Nat := 118140960795 + 2441084 * 2 ^ 59
def prefixEnd_2441084 : Nat := 4983230072969 + 3 ^ 40 * 2441084 * 2
def baseEnd_2441084 : Nat := 1253449410000032481323665

theorem tailTrace_2441084 : CollatzResearch.WordTrace tailWord_2441084 prefixEnd_2441084 1253449410000032481323665 := by
  unfold tailWord_2441084
  simp only [CollatzResearch.WordTrace]
  refine ⟨44516823944188523400445153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59355765258918031200593537 44516823944188523400445153)
  ·
    refine ⟨33387617958141392550333865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44516823944188523400445153 33387617958141392550333865)
    ·
      refine ⟨25040713468606044412750399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33387617958141392550333865 25040713468606044412750399)
      ·
        refine ⟨37561070202909066619125599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25040713468606044412750399 37561070202909066619125599)
        ·
          refine ⟨56341605304363599928688399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37561070202909066619125599 56341605304363599928688399)
          ·
            refine ⟨84512407956545399893032599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56341605304363599928688399 84512407956545399893032599)
            ·
              refine ⟨126768611934818099839548899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84512407956545399893032599 126768611934818099839548899)
              ·
                refine ⟨190152917902227149759323349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126768611934818099839548899 190152917902227149759323349)
                ·
                  refine ⟨4456709013333448822484141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 190152917902227149759323349 4456709013333448822484141)
                  ·
                    refine ⟨1671265880000043308431553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4456709013333448822484141 1671265880000043308431553)
                    ·
                      refine ⟨1253449410000032481323665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1671265880000043308431553 1253449410000032481323665)
                      ·
                        rfl

theorem cell23_2441084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 7, 3, 2].length) (baseStart_2441084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2441084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2441084 prefixEnd_2441084 := by exact prefixLift 2441084
  have htrace : WordTrace (prefixWord ++ tailWord_2441084) baseStart_2441084 baseEnd_2441084 := by
    simpa [prefixWord, tailWord_2441084, baseEnd_2441084] using wordTrace_append hprefix tailTrace_2441084
  have hstable : (prefixWord ++ tailWord_2441084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2441084).length < 2 ^ (prefixWord ++ tailWord_2441084).sum := by decide
  have hdescent : baseEnd_2441084 < baseStart_2441084 := by decide
  rcases family_descends (prefixWord ++ tailWord_2441084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2441097 : List Nat := [1, 2, 1, 1, 5, 1, 2, 1, 2, 3, 4]
def baseStart_2441097 : Nat := 118140960795 + 2441097 * 2 ^ 59
def prefixEnd_2441097 : Nat := 4983230072969 + 3 ^ 40 * 2441097 * 2
def baseEnd_2441097 : Nat := 1253456085248540930461105

theorem tailTrace_2441097 : CollatzResearch.WordTrace tailWord_2441097 prefixEnd_2441097 1253456085248540930461105 := by
  unfold tailWord_2441097
  simp only [CollatzResearch.WordTrace]
  refine ⟨89034122037329950021113545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59356081358219966680742363 89034122037329950021113545)
  ·
    refine ⟨66775591527997462515835159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89034122037329950021113545 66775591527997462515835159)
    ·
      refine ⟨100163387291996193773752739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66775591527997462515835159 100163387291996193773752739)
      ·
        refine ⟨150245080937994290660629109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100163387291996193773752739 150245080937994290660629109)
        ·
          refine ⟨14085476337936964749433979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 150245080937994290660629109 14085476337936964749433979)
          ·
            refine ⟨21128214506905447124150969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14085476337936964749433979 21128214506905447124150969)
            ·
              refine ⟨15846160880179085343113227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21128214506905447124150969 15846160880179085343113227)
              ·
                refine ⟨23769241320268628014669841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15846160880179085343113227 23769241320268628014669841)
                ·
                  refine ⟨17826930990201471011002381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23769241320268628014669841 17826930990201471011002381)
                  ·
                    refine ⟨6685099121325551629125893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17826930990201471011002381 6685099121325551629125893)
                    ·
                      refine ⟨1253456085248540930461105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6685099121325551629125893 1253456085248540930461105)
                      ·
                        rfl

theorem cell23_2441097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 1, 2, 3, 4].length) (baseStart_2441097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2441097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2441097 prefixEnd_2441097 := by exact prefixLift 2441097
  have htrace : WordTrace (prefixWord ++ tailWord_2441097) baseStart_2441097 baseEnd_2441097 := by
    simpa [prefixWord, tailWord_2441097, baseEnd_2441097] using wordTrace_append hprefix tailTrace_2441097
  have hstable : (prefixWord ++ tailWord_2441097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2441097).length < 2 ^ (prefixWord ++ tailWord_2441097).sum := by decide
  have hdescent : baseEnd_2441097 < baseStart_2441097 := by decide
  rcases family_descends (prefixWord ++ tailWord_2441097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2441102 : List Nat := [4, 1, 1, 5, 2, 1, 2, 1, 2, 4]
def baseStart_2441102 : Nat := 118140960795 + 2441102 * 2 ^ 59
def prefixEnd_2441102 : Nat := 4983230072969 + 3 ^ 40 * 2441102 * 2
def baseEnd_2441102 : Nat := 417819550883937803632861

theorem tailTrace_2441102 : CollatzResearch.WordTrace tailWord_2441102 prefixEnd_2441102 417819550883937803632861 := by
  unfold tailWord_2441102
  simp only [CollatzResearch.WordTrace]
  refine ⟨11129288050288979484380695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59356202934874557250030373 11129288050288979484380695)
  ·
    refine ⟨16693932075433469226571043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11129288050288979484380695 16693932075433469226571043)
    ·
      refine ⟨25040898113150203839856565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16693932075433469226571043 25040898113150203839856565)
      ·
        refine ⟨2347584198107831609986553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25040898113150203839856565 2347584198107831609986553)
        ·
          refine ⟨1760688148580873707489915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2347584198107831609986553 1760688148580873707489915)
          ·
            refine ⟨2641032222871310561234873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1760688148580873707489915 2641032222871310561234873)
            ·
              refine ⟨1980774167153482920926155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2641032222871310561234873 1980774167153482920926155)
              ·
                refine ⟨2971161250730224381389233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1980774167153482920926155 2971161250730224381389233)
                ·
                  refine ⟨2228370938047668286041925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2971161250730224381389233 2228370938047668286041925)
                  ·
                    refine ⟨417819550883937803632861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2228370938047668286041925 417819550883937803632861)
                    ·
                      rfl

theorem cell23_2441102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 2, 1, 2, 4].length) (baseStart_2441102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2441102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2441102 prefixEnd_2441102 := by exact prefixLift 2441102
  have htrace : WordTrace (prefixWord ++ tailWord_2441102) baseStart_2441102 baseEnd_2441102 := by
    simpa [prefixWord, tailWord_2441102, baseEnd_2441102] using wordTrace_append hprefix tailTrace_2441102
  have hstable : (prefixWord ++ tailWord_2441102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2441102).length < 2 ^ (prefixWord ++ tailWord_2441102).sum := by decide
  have hdescent : baseEnd_2441102 < baseStart_2441102 := by decide
  rcases family_descends (prefixWord ++ tailWord_2441102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2441108 : List Nat := [2, 4, 2, 1, 1, 3, 1, 3, 2, 1, 3]
def baseStart_2441108 : Nat := 118140960795 + 2441108 * 2 ^ 59
def prefixEnd_2441108 : Nat := 4983230072969 + 3 ^ 40 * 2441108 * 2
def baseEnd_2441108 : Nat := 1253461733535740387423555

theorem tailTrace_2441108 : CollatzResearch.WordTrace tailWord_2441108 prefixEnd_2441108 1253461733535740387423555 := by
  unfold tailWord_2441108
  simp only [CollatzResearch.WordTrace]
  refine ⟨44517261620145049449881989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59356348826860065933175985 44517261620145049449881989)
  ·
    refine ⟨8346986553777196771852873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44517261620145049449881989 8346986553777196771852873)
    ·
      refine ⟨6260239915332897578889655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8346986553777196771852873 6260239915332897578889655)
      ·
        refine ⟨9390359872999346368334483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6260239915332897578889655 9390359872999346368334483)
        ·
          refine ⟨14085539809499019552501725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9390359872999346368334483 14085539809499019552501725)
          ·
            refine ⟨5282077428562132332188147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14085539809499019552501725 5282077428562132332188147)
            ·
              refine ⟨7923116142843198498282221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5282077428562132332188147 7923116142843198498282221)
              ·
                refine ⟨2971168553566199436855833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7923116142843198498282221 2971168553566199436855833)
                ·
                  refine ⟨2228376415174649577641875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2971168553566199436855833 2228376415174649577641875)
                  ·
                    refine ⟨3342564622761974366462813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2228376415174649577641875 3342564622761974366462813)
                    ·
                      refine ⟨1253461733535740387423555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3342564622761974366462813 1253461733535740387423555)
                      ·
                        rfl

theorem cell23_2441108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 3, 2, 1, 3].length) (baseStart_2441108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2441108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2441108 prefixEnd_2441108 := by exact prefixLift 2441108
  have htrace : WordTrace (prefixWord ++ tailWord_2441108) baseStart_2441108 baseEnd_2441108 := by
    simpa [prefixWord, tailWord_2441108, baseEnd_2441108] using wordTrace_append hprefix tailTrace_2441108
  have hstable : (prefixWord ++ tailWord_2441108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2441108).length < 2 ^ (prefixWord ++ tailWord_2441108).sum := by decide
  have hdescent : baseEnd_2441108 < baseStart_2441108 := by decide
  rcases family_descends (prefixWord ++ tailWord_2441108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2441164 : List Nat := [2, 2, 1, 4, 1, 2, 1, 1, 1, 5, 3]
def baseStart_2441164 : Nat := 118140960795 + 2441164 * 2 ^ 59
def prefixEnd_2441164 : Nat := 4983230072969 + 3 ^ 40 * 2441164 * 2
def baseEnd_2441164 : Nat := 1253490488452392168323297

theorem tailTrace_2441164 : CollatzResearch.WordTrace tailWord_2441164 prefixEnd_2441164 1253490488452392168323297 := by
  unfold tailWord_2441164
  simp only [CollatzResearch.WordTrace]
  refine ⟨44518282864043610231901273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59357710485391480309201697 44518282864043610231901273)
  ·
    refine ⟨33388712148032707673925955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44518282864043610231901273 33388712148032707673925955)
    ·
      refine ⟨50083068222049061510888933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33388712148032707673925955 50083068222049061510888933)
      ·
        refine ⟨9390575291634199033291675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50083068222049061510888933 9390575291634199033291675)
        ·
          refine ⟨14085862937451298549937513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9390575291634199033291675 14085862937451298549937513)
          ·
            refine ⟨10564397203088473912453135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14085862937451298549937513 10564397203088473912453135)
            ·
              refine ⟨15846595804632710868679703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10564397203088473912453135 15846595804632710868679703)
              ·
                refine ⟨23769893706949066303019555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15846595804632710868679703 23769893706949066303019555)
                ·
                  refine ⟨35654840560423599454529333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23769893706949066303019555 35654840560423599454529333)
                  ·
                    refine ⟨3342641302539712448862125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35654840560423599454529333 3342641302539712448862125)
                    ·
                      refine ⟨1253490488452392168323297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3342641302539712448862125 1253490488452392168323297)
                      ·
                        rfl

theorem cell23_2441164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 1, 1, 5, 3].length) (baseStart_2441164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2441164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2441164 prefixEnd_2441164 := by exact prefixLift 2441164
  have htrace : WordTrace (prefixWord ++ tailWord_2441164) baseStart_2441164 baseEnd_2441164 := by
    simpa [prefixWord, tailWord_2441164, baseEnd_2441164] using wordTrace_append hprefix tailTrace_2441164
  have hstable : (prefixWord ++ tailWord_2441164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2441164).length < 2 ^ (prefixWord ++ tailWord_2441164).sum := by decide
  have hdescent : baseEnd_2441164 < baseStart_2441164 := by decide
  rcases family_descends (prefixWord ++ tailWord_2441164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2441167 : List Nat := [1, 1, 2, 1, 1, 5, 2, 2, 1, 7]
def baseStart_2441167 : Nat := 118140960795 + 2441167 * 2 ^ 59
def prefixEnd_2441167 : Nat := 4983230072969 + 3 ^ 40 * 2441167 * 2
def baseEnd_2441167 : Nat := 417830676298118552195261

theorem tailTrace_2441167 : CollatzResearch.WordTrace tailWord_2441167 prefixEnd_2441167 417830676298118552195261 := by
  unfold tailWord_2441167
  simp only [CollatzResearch.WordTrace]
  refine ⟨89036675147076351976161755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59357783431384234650774503 89036675147076351976161755)
  ·
    refine ⟨133555012720614527964242633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89036675147076351976161755 133555012720614527964242633)
    ·
      refine ⟨100166259540460895973181975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133555012720614527964242633 100166259540460895973181975)
      ·
        refine ⟨150249389310691343959772963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100166259540460895973181975 150249389310691343959772963)
        ·
          refine ⟨225374083966037015939659445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150249389310691343959772963 225374083966037015939659445)
          ·
            refine ⟨21128820371815970244343073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 225374083966037015939659445 21128820371815970244343073)
            ·
              refine ⟨15846615278861977683257305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21128820371815970244343073 15846615278861977683257305)
              ·
                refine ⟨11884961459146483262442979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15846615278861977683257305 11884961459146483262442979)
                ·
                  refine ⟨17827442188719724893664469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11884961459146483262442979 17827442188719724893664469)
                  ·
                    refine ⟨417830676298118552195261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17827442188719724893664469 417830676298118552195261)
                    ·
                      rfl

theorem cell23_2441167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 2, 1, 7].length) (baseStart_2441167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2441167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2441167 prefixEnd_2441167 := by exact prefixLift 2441167
  have htrace : WordTrace (prefixWord ++ tailWord_2441167) baseStart_2441167 baseEnd_2441167 := by
    simpa [prefixWord, tailWord_2441167, baseEnd_2441167] using wordTrace_append hprefix tailTrace_2441167
  have hstable : (prefixWord ++ tailWord_2441167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2441167).length < 2 ^ (prefixWord ++ tailWord_2441167).sum := by decide
  have hdescent : baseEnd_2441167 < baseStart_2441167 := by decide
  rcases family_descends (prefixWord ++ tailWord_2441167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2441221 : List Nat := [1, 3, 1, 1, 2, 4, 2, 1, 2, 4, 2]
def baseStart_2441221 : Nat := 118140960795 + 2441221 * 2 ^ 59
def prefixEnd_2441221 : Nat := 4983230072969 + 3 ^ 40 * 2441221 * 2
def baseEnd_2441221 : Nat := 1253519756849698445310535

theorem tailTrace_2441221 : CollatzResearch.WordTrace tailWord_2441221 prefixEnd_2441221 1253519756849698445310535 := by
  unfold tailWord_2441221
  simp only [CollatzResearch.WordTrace]
  refine ⟨89038644688880719198627517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59359096459253812799085011 89038644688880719198627517)
  ·
    refine ⟨33389491758330269699485319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89038644688880719198627517 33389491758330269699485319)
    ·
      refine ⟨50084237637495404549227979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33389491758330269699485319 50084237637495404549227979)
      ·
        refine ⟨75126356456243106823841969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50084237637495404549227979 75126356456243106823841969)
        ·
          refine ⟨56344767342182330117881477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75126356456243106823841969 56344767342182330117881477)
          ·
            refine ⟨10564643876659186897102777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56344767342182330117881477 10564643876659186897102777)
            ·
              refine ⟨7923482907494390172827083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10564643876659186897102777 7923482907494390172827083)
              ·
                refine ⟨11885224361241585259240625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7923482907494390172827083 11885224361241585259240625)
                ·
                  refine ⟨8913918270931188944430469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11885224361241585259240625 8913918270931188944430469)
                  ·
                    refine ⟨1671359675799597927080713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8913918270931188944430469 1671359675799597927080713)
                    ·
                      refine ⟨1253519756849698445310535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1671359675799597927080713 1253519756849698445310535)
                      ·
                        rfl

theorem cell23_2441221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 1, 2, 4, 2].length) (baseStart_2441221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2441221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2441221 prefixEnd_2441221 := by exact prefixLift 2441221
  have htrace : WordTrace (prefixWord ++ tailWord_2441221) baseStart_2441221 baseEnd_2441221 := by
    simpa [prefixWord, tailWord_2441221, baseEnd_2441221] using wordTrace_append hprefix tailTrace_2441221
  have hstable : (prefixWord ++ tailWord_2441221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2441221).length < 2 ^ (prefixWord ++ tailWord_2441221).sum := by decide
  have hdescent : baseEnd_2441221 < baseStart_2441221 := by decide
  rcases family_descends (prefixWord ++ tailWord_2441221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2441224 : List Nat := [2, 1, 3, 2, 1, 2, 1, 1, 3, 4, 3]
def baseStart_2441224 : Nat := 118140960795 + 2441224 * 2 ^ 59
def prefixEnd_2441224 : Nat := 4983230072969 + 3 ^ 40 * 2441224 * 2
def baseEnd_2441224 : Nat := 1253521297291661933573021

theorem tailTrace_2441224 : CollatzResearch.WordTrace tailWord_2441224 prefixEnd_2441224 1253521297291661933573021 := by
  unfold tailWord_2441224
  simp only [CollatzResearch.WordTrace]
  refine ⟨44519377053934925355493363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59359169405246567140657817 44519377053934925355493363)
  ·
    refine ⟨66779065580902388033240045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44519377053934925355493363 66779065580902388033240045)
    ·
      refine ⟨25042149592838395512465017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66779065580902388033240045 25042149592838395512465017)
      ·
        refine ⟨18781612194628796634348763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25042149592838395512465017 18781612194628796634348763)
        ·
          refine ⟨28172418291943194951523145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18781612194628796634348763 28172418291943194951523145)
          ·
            refine ⟨21129313718957396213642359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28172418291943194951523145 21129313718957396213642359)
            ·
              refine ⟨31693970578436094320463539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21129313718957396213642359 31693970578436094320463539)
              ·
                refine ⟨47540955867654141480695309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31693970578436094320463539 47540955867654141480695309)
                ·
                  refine ⟨17827858450370303055260741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47540955867654141480695309 17827858450370303055260741)
                  ·
                    refine ⟨3342723459444431822861389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17827858450370303055260741 3342723459444431822861389)
                    ·
                      refine ⟨1253521297291661933573021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3342723459444431822861389 1253521297291661933573021)
                      ·
                        rfl

theorem cell23_2441224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 3, 4, 3].length) (baseStart_2441224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2441224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2441224 prefixEnd_2441224 := by exact prefixLift 2441224
  have htrace : WordTrace (prefixWord ++ tailWord_2441224) baseStart_2441224 baseEnd_2441224 := by
    simpa [prefixWord, tailWord_2441224, baseEnd_2441224] using wordTrace_append hprefix tailTrace_2441224
  have hstable : (prefixWord ++ tailWord_2441224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2441224).length < 2 ^ (prefixWord ++ tailWord_2441224).sum := by decide
  have hdescent : baseEnd_2441224 < baseStart_2441224 := by decide
  rcases family_descends (prefixWord ++ tailWord_2441224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2441244 : List Nat := [2, 2, 3, 1, 3, 1, 1, 2, 8]
def baseStart_2441244 : Nat := 118140960795 + 2441244 * 2 ^ 59
def prefixEnd_2441244 : Nat := 4983230072969 + 3 ^ 40 * 2441244 * 2
def baseEnd_2441244 : Nat := 139281285211639095035881

theorem tailTrace_2441244 : CollatzResearch.WordTrace tailWord_2441244 prefixEnd_2441244 139281285211639095035881 := by
  unfold tailWord_2441244
  simp only [CollatzResearch.WordTrace]
  refine ⟨44519741783898697063357393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59359655711864929417809857 44519741783898697063357393)
  ·
    refine ⟨33389806337924022797518045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44519741783898697063357393 33389806337924022797518045)
    ·
      refine ⟨12521177376721508549069267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33389806337924022797518045 12521177376721508549069267)
      ·
        refine ⟨18781766065082262823603901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12521177376721508549069267 18781766065082262823603901)
        ·
          refine ⟨7043162274405848558851463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18781766065082262823603901 7043162274405848558851463)
          ·
            refine ⟨10564743411608772838277195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7043162274405848558851463 10564743411608772838277195)
            ·
              refine ⟨15847115117413159257415793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10564743411608772838277195 15847115117413159257415793)
              ·
                refine ⟨11885336338059869443061845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15847115117413159257415793 11885336338059869443061845)
                ·
                  refine ⟨139281285211639095035881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11885336338059869443061845 139281285211639095035881)
                  ·
                    rfl

theorem cell23_2441244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 2, 8].length) (baseStart_2441244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2441244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2441244 prefixEnd_2441244 := by exact prefixLift 2441244
  have htrace : WordTrace (prefixWord ++ tailWord_2441244) baseStart_2441244 baseEnd_2441244 := by
    simpa [prefixWord, tailWord_2441244, baseEnd_2441244] using wordTrace_append hprefix tailTrace_2441244
  have hstable : (prefixWord ++ tailWord_2441244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2441244).length < 2 ^ (prefixWord ++ tailWord_2441244).sum := by decide
  have hdescent : baseEnd_2441244 < baseStart_2441244 := by decide
  rcases family_descends (prefixWord ++ tailWord_2441244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2441257 : List Nat := [1, 2, 1, 1, 1, 1, 1, 1, 3, 11]
def baseStart_2441257 : Nat := 118140960795 + 2441257 * 2 ^ 59
def prefixEnd_2441257 : Nat := 4983230072969 + 3 ^ 40 * 2441257 * 2
def baseEnd_2441257 : Nat := 417846080717753434820123

theorem tailTrace_2441257 : CollatzResearch.WordTrace tailWord_2441257 prefixEnd_2441257 417846080717753434820123 := by
  unfold tailWord_2441257
  simp only [CollatzResearch.WordTrace]
  refine ⟨89039957716750297346938025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59359971811166864897958683 89039957716750297346938025)
  ·
    refine ⟨66779968287562723010203519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89039957716750297346938025 66779968287562723010203519)
    ·
      refine ⟨100169952431344084515305279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66779968287562723010203519 100169952431344084515305279)
      ·
        refine ⟨150254928647016126772957919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100169952431344084515305279 150254928647016126772957919)
        ·
          refine ⟨225382392970524190159436879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150254928647016126772957919 225382392970524190159436879)
          ·
            refine ⟨338073589455786285239155319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 225382392970524190159436879 338073589455786285239155319)
            ·
              refine ⟨507110384183679427858732979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 338073589455786285239155319 507110384183679427858732979)
              ·
                refine ⟨760665576275519141788099469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 507110384183679427858732979 760665576275519141788099469)
                ·
                  refine ⟨285249591103319678170537301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 760665576275519141788099469 285249591103319678170537301)
                  ·
                    refine ⟨417846080717753434820123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 285249591103319678170537301 417846080717753434820123)
                    ·
                      rfl

theorem cell23_2441257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 11].length) (baseStart_2441257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2441257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2441257 prefixEnd_2441257 := by exact prefixLift 2441257
  have htrace : WordTrace (prefixWord ++ tailWord_2441257) baseStart_2441257 baseEnd_2441257 := by
    simpa [prefixWord, tailWord_2441257, baseEnd_2441257] using wordTrace_append hprefix tailTrace_2441257
  have hstable : (prefixWord ++ tailWord_2441257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2441257).length < 2 ^ (prefixWord ++ tailWord_2441257).sum := by decide
  have hdescent : baseEnd_2441257 < baseStart_2441257 := by decide
  rcases family_descends (prefixWord ++ tailWord_2441257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2441258 : List Nat := [3, 1, 4, 1, 2, 2, 1, 2, 2, 2, 3]
def baseStart_2441258 : Nat := 118140960795 + 2441258 * 2 ^ 59
def prefixEnd_2441258 : Nat := 4983230072969 + 3 ^ 40 * 2441258 * 2
def baseEnd_2441258 : Nat := 1253538755633914800547865

theorem tailTrace_2441258 : CollatzResearch.WordTrace tailWord_2441258 prefixEnd_2441258 1253538755633914800547865 := by
  unfold tailWord_2441258
  simp only [CollatzResearch.WordTrace]
  refine ⟨22259998547436668629431107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59359996126497783011816285 22259998547436668629431107)
  ·
    refine ⟨33389997821155002944146661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22259998547436668629431107 33389997821155002944146661)
    ·
      refine ⟨6260624591466563052027499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33389997821155002944146661 6260624591466563052027499)
      ·
        refine ⟨9390936887199844578041249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6260624591466563052027499 9390936887199844578041249)
        ·
          refine ⟨7043202665399883433530937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9390936887199844578041249 7043202665399883433530937)
          ·
            refine ⟨5282401999049912575148203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7043202665399883433530937 5282401999049912575148203)
            ·
              refine ⟨7923602998574868862722305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5282401999049912575148203 7923602998574868862722305)
              ·
                refine ⟨5942702248931151647041729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7923602998574868862722305 5942702248931151647041729)
                ·
                  refine ⟨4457026686698363735281297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5942702248931151647041729 4457026686698363735281297)
                  ·
                    refine ⟨3342770015023772801460973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4457026686698363735281297 3342770015023772801460973)
                    ·
                      refine ⟨1253538755633914800547865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3342770015023772801460973 1253538755633914800547865)
                      ·
                        rfl

theorem cell23_2441258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 2, 2, 2, 3].length) (baseStart_2441258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2441258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2441258 prefixEnd_2441258 := by exact prefixLift 2441258
  have htrace : WordTrace (prefixWord ++ tailWord_2441258) baseStart_2441258 baseEnd_2441258 := by
    simpa [prefixWord, tailWord_2441258, baseEnd_2441258] using wordTrace_append hprefix tailTrace_2441258
  have hstable : (prefixWord ++ tailWord_2441258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2441258).length < 2 ^ (prefixWord ++ tailWord_2441258).sum := by decide
  have hdescent : baseEnd_2441258 < baseStart_2441258 := by decide
  rcases family_descends (prefixWord ++ tailWord_2441258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2441265 : List Nat := [1, 2, 2, 3, 1, 4, 3, 2, 1, 4]
def baseStart_2441265 : Nat := 118140960795 + 2441265 * 2 ^ 59
def prefixEnd_2441265 : Nat := 4983230072969 + 3 ^ 40 * 2441265 * 2
def baseEnd_2441265 : Nat := 417847449999498757720111

theorem tailTrace_2441265 : CollatzResearch.WordTrace tailWord_2441265 prefixEnd_2441265 417847449999498757720111 := by
  unfold tailWord_2441265
  simp only [CollatzResearch.WordTrace]
  refine ⟨89040249500721314713229249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59360166333814209808819499 89040249500721314713229249)
  ·
    refine ⟨66780187125540986034921937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89040249500721314713229249 66780187125540986034921937)
    ·
      refine ⟨50085140344155739526191453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66780187125540986034921937 50085140344155739526191453)
      ·
        refine ⟨18781927629058402322321795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50085140344155739526191453 18781927629058402322321795)
        ·
          refine ⟨28172891443587603483482693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18781927629058402322321795 28172891443587603483482693)
          ·
            refine ⟨5282417145672675653153005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28172891443587603483482693 5282417145672675653153005)
            ·
              refine ⟨1980906429627253369932377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5282417145672675653153005 1980906429627253369932377)
              ·
                refine ⟨1485679822220440027449283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1980906429627253369932377 1485679822220440027449283)
                ·
                  refine ⟨2228519733330660041173925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1485679822220440027449283 2228519733330660041173925)
                  ·
                    refine ⟨417847449999498757720111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2228519733330660041173925 417847449999498757720111)
                    ·
                      rfl

theorem cell23_2441265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 3, 2, 1, 4].length) (baseStart_2441265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2441265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2441265 prefixEnd_2441265 := by exact prefixLift 2441265
  have htrace : WordTrace (prefixWord ++ tailWord_2441265) baseStart_2441265 baseEnd_2441265 := by
    simpa [prefixWord, tailWord_2441265, baseEnd_2441265] using wordTrace_append hprefix tailTrace_2441265
  have hstable : (prefixWord ++ tailWord_2441265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2441265).length < 2 ^ (prefixWord ++ tailWord_2441265).sum := by decide
  have hdescent : baseEnd_2441265 < baseStart_2441265 := by decide
  rcases family_descends (prefixWord ++ tailWord_2441265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2441274 : List Nat := [3, 1, 1, 1, 3, 1, 1, 4, 3, 5]
def baseStart_2441274 : Nat := 118140960795 + 2441274 * 2 ^ 59
def prefixEnd_2441274 : Nat := 4983230072969 + 3 ^ 40 * 2441274 * 2
def baseEnd_2441274 : Nat := 417848990441462245982597

theorem tailTrace_2441274 : CollatzResearch.WordTrace tailWord_2441274 prefixEnd_2441274 417848990441462245982597 := by
  unfold tailWord_2441274
  simp only [CollatzResearch.WordTrace]
  refine ⟨22260144439422177312576719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59360385171792472833537917 22260144439422177312576719)
  ·
    refine ⟨33390216659133265968865079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22260144439422177312576719 33390216659133265968865079)
    ·
      refine ⟨50085324988699898953297619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33390216659133265968865079 50085324988699898953297619)
      ·
        refine ⟨75127987483049848429946429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50085324988699898953297619 75127987483049848429946429)
        ·
          refine ⟨28172995306143693161229911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75127987483049848429946429 28172995306143693161229911)
          ·
            refine ⟨42259492959215539741844867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28172995306143693161229911 42259492959215539741844867)
            ·
              refine ⟨63389239438823309612767301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42259492959215539741844867 63389239438823309612767301)
              ·
                refine ⟨11885482394779370552393869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63389239438823309612767301 11885482394779370552393869)
                ·
                  refine ⟨4457055898042263957147701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11885482394779370552393869 4457055898042263957147701)
                  ·
                    refine ⟨417848990441462245982597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4457055898042263957147701 417848990441462245982597)
                    ·
                      rfl

theorem cell23_2441274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 4, 3, 5].length) (baseStart_2441274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2441274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2441274 prefixEnd_2441274 := by exact prefixLift 2441274
  have htrace : WordTrace (prefixWord ++ tailWord_2441274) baseStart_2441274 baseEnd_2441274 := by
    simpa [prefixWord, tailWord_2441274, baseEnd_2441274] using wordTrace_append hprefix tailTrace_2441274
  have hstable : (prefixWord ++ tailWord_2441274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2441274).length < 2 ^ (prefixWord ++ tailWord_2441274).sum := by decide
  have hdescent : baseEnd_2441274 < baseStart_2441274 := by decide
  rcases family_descends (prefixWord ++ tailWord_2441274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2441278 : List Nat := [4, 2, 1, 3, 2, 1, 1, 3, 6]
def baseStart_2441278 : Nat := 118140960795 + 2441278 * 2 ^ 59
def prefixEnd_2441278 : Nat := 4983230072969 + 3 ^ 40 * 2441278 * 2
def baseEnd_2441278 : Nat := 139283225027444969144197

theorem tailTrace_2441278 : CollatzResearch.WordTrace tailWord_2441278 prefixEnd_2441278 139283225027444969144197 := by
  unfold tailWord_2441278
  simp only [CollatzResearch.WordTrace]
  refine ⟨11130090456209277241681561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59360482433116145288968325 11130090456209277241681561)
  ·
    refine ⟨8347567842156957931261171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11130090456209277241681561 8347567842156957931261171)
    ·
      refine ⟨12521351763235436896891757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8347567842156957931261171 12521351763235436896891757)
      ·
        refine ⟨4695506911213288836334409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12521351763235436896891757 4695506911213288836334409)
        ·
          refine ⟨3521630183409966627250807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4695506911213288836334409 3521630183409966627250807)
          ·
            refine ⟨5282445275114949940876211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3521630183409966627250807 5282445275114949940876211)
            ·
              refine ⟨7923667912672424911314317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5282445275114949940876211 7923667912672424911314317)
              ·
                refine ⟨2971375467252159341742869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7923667912672424911314317 2971375467252159341742869)
                ·
                  refine ⟨139283225027444969144197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2971375467252159341742869 139283225027444969144197)
                  ·
                    rfl

theorem cell23_2441278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 3, 6].length) (baseStart_2441278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2441278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2441278 prefixEnd_2441278 := by exact prefixLift 2441278
  have htrace : WordTrace (prefixWord ++ tailWord_2441278) baseStart_2441278 baseEnd_2441278 := by
    simpa [prefixWord, tailWord_2441278, baseEnd_2441278] using wordTrace_append hprefix tailTrace_2441278
  have hstable : (prefixWord ++ tailWord_2441278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2441278).length < 2 ^ (prefixWord ++ tailWord_2441278).sum := by decide
  have hdescent : baseEnd_2441278 < baseStart_2441278 := by decide
  rcases family_descends (prefixWord ++ tailWord_2441278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2441304 : List Nat := [2, 1, 2, 2, 1, 4, 1, 1, 3, 6]
def baseStart_2441304 : Nat := 118140960795 + 2441304 * 2 ^ 59
def prefixEnd_2441304 : Nat := 4983230072969 + 3 ^ 40 * 2441304 * 2
def baseEnd_2441304 : Nat := 417854125248007206857551

theorem tailTrace_2441304 : CollatzResearch.WordTrace tailWord_2441304 prefixEnd_2441304 417854125248007206857551 := by
  unfold tailWord_2441304
  simp only [CollatzResearch.WordTrace]
  refine ⟨44520835973790012186949483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59361114631720016249265977 44520835973790012186949483)
  ·
    refine ⟨66781253960685018280424225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44520835973790012186949483 66781253960685018280424225)
    ·
      refine ⟨50085940470513763710318169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66781253960685018280424225 50085940470513763710318169)
      ·
        refine ⟨37564455352885322782738627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50085940470513763710318169 37564455352885322782738627)
        ·
          refine ⟨56346683029327984174107941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37564455352885322782738627 56346683029327984174107941)
          ·
            refine ⟨10565003067998997032645239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56346683029327984174107941 10565003067998997032645239)
            ·
              refine ⟨15847504601998495548967859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10565003067998997032645239 15847504601998495548967859)
              ·
                refine ⟨23771256902997743323451789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15847504601998495548967859 23771256902997743323451789)
                ·
                  refine ⟨8914221338624153746294421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23771256902997743323451789 8914221338624153746294421)
                  ·
                    refine ⟨417854125248007206857551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8914221338624153746294421 417854125248007206857551)
                    ·
                      rfl

theorem cell23_2441304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 1, 3, 6].length) (baseStart_2441304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2441304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2441304 prefixEnd_2441304 := by exact prefixLift 2441304
  have htrace : WordTrace (prefixWord ++ tailWord_2441304) baseStart_2441304 baseEnd_2441304 := by
    simpa [prefixWord, tailWord_2441304, baseEnd_2441304] using wordTrace_append hprefix tailTrace_2441304
  have hstable : (prefixWord ++ tailWord_2441304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2441304).length < 2 ^ (prefixWord ++ tailWord_2441304).sum := by decide
  have hdescent : baseEnd_2441304 < baseStart_2441304 := by decide
  rcases family_descends (prefixWord ++ tailWord_2441304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2441322 : List Nat := [3, 1, 3, 2, 3, 1, 1, 4, 1, 1, 3]
def baseStart_2441322 : Nat := 118140960795 + 2441322 * 2 ^ 59
def prefixEnd_2441322 : Nat := 4983230072969 + 3 ^ 40 * 2441322 * 2
def baseEnd_2441322 : Nat := 1253571618395802550147571

theorem tailTrace_2441322 : CollatzResearch.WordTrace tailWord_2441322 prefixEnd_2441322 1253571618395802550147571 := by
  unfold tailWord_2441322
  simp only [CollatzResearch.WordTrace]
  refine ⟨22260582115378703362013555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59361552307676542298702813 22260582115378703362013555)
  ·
    refine ⟨33390873173068055043020333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22260582115378703362013555 33390873173068055043020333)
    ·
      refine ⟨12521577439900520641132625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33390873173068055043020333 12521577439900520641132625)
      ·
        refine ⟨9391183079925390480849469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12521577439900520641132625 9391183079925390480849469)
        ·
          refine ⟨3521693654972021430318551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9391183079925390480849469 3521693654972021430318551)
          ·
            refine ⟨5282540482458032145477827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3521693654972021430318551 5282540482458032145477827)
            ·
              refine ⟨7923810723687048218216741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5282540482458032145477827 7923810723687048218216741)
              ·
                refine ⟨1485714510691321540915639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7923810723687048218216741 1485714510691321540915639)
                ·
                  refine ⟨2228571766036982311373459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1485714510691321540915639 2228571766036982311373459)
                  ·
                    refine ⟨3342857649055473467060189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2228571766036982311373459 3342857649055473467060189)
                    ·
                      refine ⟨1253571618395802550147571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3342857649055473467060189 1253571618395802550147571)
                      ·
                        rfl

theorem cell23_2441322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 4, 1, 1, 3].length) (baseStart_2441322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2441322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2441322 prefixEnd_2441322 := by exact prefixLift 2441322
  have htrace : WordTrace (prefixWord ++ tailWord_2441322) baseStart_2441322 baseEnd_2441322 := by
    simpa [prefixWord, tailWord_2441322, baseEnd_2441322] using wordTrace_append hprefix tailTrace_2441322
  have hstable : (prefixWord ++ tailWord_2441322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2441322).length < 2 ^ (prefixWord ++ tailWord_2441322).sum := by decide
  have hdescent : baseEnd_2441322 < baseStart_2441322 := by decide
  rcases family_descends (prefixWord ++ tailWord_2441322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2441341 : List Nat := [1, 4, 1, 1, 3, 2, 1, 3, 1, 2, 4]
def baseStart_2441341 : Nat := 118140960795 + 2441341 * 2 ^ 59
def prefixEnd_2441341 : Nat := 4983230072969 + 3 ^ 40 * 2441341 * 2
def baseEnd_2441341 : Nat := 1253581374528237975809983

theorem tailTrace_2441341 : CollatzResearch.WordTrace tailWord_2441341 prefixEnd_2441341 1253581374528237975809983 := by
  unfold tailWord_2441341
  simp only [CollatzResearch.WordTrace]
  refine ⟨89043021448445979692995877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59362014298963986461997251 89043021448445979692995877)
  ·
    refine ⟨16695566521583621192436727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89043021448445979692995877 16695566521583621192436727)
    ·
      refine ⟨25043349782375431788655091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16695566521583621192436727 25043349782375431788655091)
      ·
        refine ⟨37565024673563147682982637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25043349782375431788655091 37565024673563147682982637)
        ·
          refine ⟨14086884252586180381118489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37565024673563147682982637 14086884252586180381118489)
          ·
            refine ⟨10565163189439635285838867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14086884252586180381118489 10565163189439635285838867)
            ·
              refine ⟨15847744784159452928758301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10565163189439635285838867 15847744784159452928758301)
              ·
                refine ⟨5942904294059794848284363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15847744784159452928758301 5942904294059794848284363)
                ·
                  refine ⟨8914356441089692272426545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5942904294059794848284363 8914356441089692272426545)
                  ·
                    refine ⟨6685767330817269204319909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8914356441089692272426545 6685767330817269204319909)
                    ·
                      refine ⟨1253581374528237975809983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6685767330817269204319909 1253581374528237975809983)
                      ·
                        rfl

theorem cell23_2441341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 3, 1, 2, 4].length) (baseStart_2441341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2441341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2441341 prefixEnd_2441341 := by exact prefixLift 2441341
  have htrace : WordTrace (prefixWord ++ tailWord_2441341) baseStart_2441341 baseEnd_2441341 := by
    simpa [prefixWord, tailWord_2441341, baseEnd_2441341] using wordTrace_append hprefix tailTrace_2441341
  have hstable : (prefixWord ++ tailWord_2441341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2441341).length < 2 ^ (prefixWord ++ tailWord_2441341).sum := by decide
  have hdescent : baseEnd_2441341 < baseStart_2441341 := by decide
  rcases family_descends (prefixWord ++ tailWord_2441341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2441348 : List Nat := [2, 3, 2, 1, 2, 1, 2, 4, 1, 2, 3]
def baseStart_2441348 : Nat := 118140960795 + 2441348 * 2 ^ 59
def prefixEnd_2441348 : Nat := 4983230072969 + 3 ^ 40 * 2441348 * 2
def baseEnd_2441348 : Nat := 1253584968892819448422451

theorem tailTrace_2441348 : CollatzResearch.WordTrace tailWord_2441348 prefixEnd_2441348 1253584968892819448422451 := by
  unfold tailWord_2441348
  simp only [CollatzResearch.WordTrace]
  refine ⟨44521638379710309944250349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59362184506280413259000465 44521638379710309944250349)
  ·
    refine ⟨16695614392391366229093881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44521638379710309944250349 16695614392391366229093881)
    ·
      refine ⟨12521710794293524671820411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16695614392391366229093881 12521710794293524671820411)
      ·
        refine ⟨18782566191440287007730617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12521710794293524671820411 18782566191440287007730617)
        ·
          refine ⟨14086924643580215255797963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18782566191440287007730617 14086924643580215255797963)
          ·
            refine ⟨21130386965370322883696945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14086924643580215255797963 21130386965370322883696945)
            ·
              refine ⟨15847790224027742162772709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21130386965370322883696945 15847790224027742162772709)
              ·
                refine ⟨2971460667005201655519883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15847790224027742162772709 2971460667005201655519883)
                ·
                  refine ⟨4457191000507802483279825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2971460667005201655519883 4457191000507802483279825)
                  ·
                    refine ⟨3342893250380851862459869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4457191000507802483279825 3342893250380851862459869)
                    ·
                      refine ⟨1253584968892819448422451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3342893250380851862459869 1253584968892819448422451)
                      ·
                        rfl

theorem cell23_2441348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 4, 1, 2, 3].length) (baseStart_2441348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2441348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2441348 prefixEnd_2441348 := by exact prefixLift 2441348
  have htrace : WordTrace (prefixWord ++ tailWord_2441348) baseStart_2441348 baseEnd_2441348 := by
    simpa [prefixWord, tailWord_2441348, baseEnd_2441348] using wordTrace_append hprefix tailTrace_2441348
  have hstable : (prefixWord ++ tailWord_2441348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2441348).length < 2 ^ (prefixWord ++ tailWord_2441348).sum := by decide
  have hdescent : baseEnd_2441348 < baseStart_2441348 := by decide
  rcases family_descends (prefixWord ++ tailWord_2441348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2441418 : List Nat := [3, 1, 2, 1, 3, 1, 2, 1, 3, 4, 2]
def baseStart_2441418 : Nat := 118140960795 + 2441418 * 2 ^ 59
def prefixEnd_2441418 : Nat := 4983230072969 + 3 ^ 40 * 2441418 * 2
def baseEnd_2441418 : Nat := 1253620912538634174547129

theorem tailTrace_2441418 : CollatzResearch.WordTrace tailWord_2441418 prefixEnd_2441418 1253620912538634174547129 := by
  unfold tailWord_2441418
  simp only [CollatzResearch.WordTrace]
  refine ⟨22261457467291755460887227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59363886579444681229032605 22261457467291755460887227)
  ·
    refine ⟨33392186200937633191330841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22261457467291755460887227 33392186200937633191330841)
    ·
      refine ⟨25044139650703224893498131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33392186200937633191330841 25044139650703224893498131)
      ·
        refine ⟨37566209476054837340247197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25044139650703224893498131 37566209476054837340247197)
        ·
          refine ⟨14087328553520564002592699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37566209476054837340247197 14087328553520564002592699)
          ·
            refine ⟨21130992830280846003889049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14087328553520564002592699 21130992830280846003889049)
            ·
              refine ⟨15848244622710634502916787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21130992830280846003889049 15848244622710634502916787)
              ·
                refine ⟨23772366934065951754375181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15848244622710634502916787 23772366934065951754375181)
                ·
                  refine ⟨8914637600274731907890693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23772366934065951754375181 8914637600274731907890693)
                  ·
                    refine ⟨1671494550051512232729505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8914637600274731907890693 1671494550051512232729505)
                    ·
                      refine ⟨1253620912538634174547129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1671494550051512232729505 1253620912538634174547129)
                      ·
                        rfl

theorem cell23_2441418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 4, 2].length) (baseStart_2441418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2441418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2441418 prefixEnd_2441418 := by exact prefixLift 2441418
  have htrace : WordTrace (prefixWord ++ tailWord_2441418) baseStart_2441418 baseEnd_2441418 := by
    simpa [prefixWord, tailWord_2441418, baseEnd_2441418] using wordTrace_append hprefix tailTrace_2441418
  have hstable : (prefixWord ++ tailWord_2441418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2441418).length < 2 ^ (prefixWord ++ tailWord_2441418).sum := by decide
  have hdescent : baseEnd_2441418 < baseStart_2441418 := by decide
  rcases family_descends (prefixWord ++ tailWord_2441418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2441451 : List Nat := [1, 1, 1, 1, 2, 5, 2, 1, 1, 5, 3]
def baseStart_2441451 : Nat := 118140960795 + 2441451 * 2 ^ 59
def prefixEnd_2441451 : Nat := 4983230072969 + 3 ^ 40 * 2441451 * 2
def baseEnd_2441451 : Nat := 1253637857400232545434477

theorem tailTrace_2441451 : CollatzResearch.WordTrace tailWord_2441451 prefixEnd_2441451 1253637857400232545434477 := by
  unfold tailWord_2441451
  simp only [CollatzResearch.WordTrace]
  refine ⟨89047033478047468479500207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59364688985364978986333471 89047033478047468479500207)
  ·
    refine ⟨133570550217071202719250311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89047033478047468479500207 133570550217071202719250311)
    ·
      refine ⟨200355825325606804078875467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133570550217071202719250311 200355825325606804078875467)
      ·
        refine ⟨300533737988410206118313201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200355825325606804078875467 300533737988410206118313201)
        ·
          refine ⟨225400303491307654588734901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 300533737988410206118313201 225400303491307654588734901)
          ·
            refine ⟨21131278452310092617693897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 225400303491307654588734901 21131278452310092617693897)
            ·
              refine ⟨15848458839232569463270423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21131278452310092617693897 15848458839232569463270423)
              ·
                refine ⟨23772688258848854194905635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15848458839232569463270423 23772688258848854194905635)
                ·
                  refine ⟨35659032388273281292358453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23772688258848854194905635 35659032388273281292358453)
                  ·
                    refine ⟨3343034286400620121158605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35659032388273281292358453 3343034286400620121158605)
                    ·
                      refine ⟨1253637857400232545434477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3343034286400620121158605 1253637857400232545434477)
                      ·
                        rfl

theorem cell23_2441451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 1, 1, 5, 3].length) (baseStart_2441451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2441451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2441451 prefixEnd_2441451 := by exact prefixLift 2441451
  have htrace : WordTrace (prefixWord ++ tailWord_2441451) baseStart_2441451 baseEnd_2441451 := by
    simpa [prefixWord, tailWord_2441451, baseEnd_2441451] using wordTrace_append hprefix tailTrace_2441451
  have hstable : (prefixWord ++ tailWord_2441451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2441451).length < 2 ^ (prefixWord ++ tailWord_2441451).sum := by decide
  have hdescent : baseEnd_2441451 < baseStart_2441451 := by decide
  rcases family_descends (prefixWord ++ tailWord_2441451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2441481 : List Nat := [1, 2, 1, 1, 3, 4, 1, 2, 1, 2, 5]
def baseStart_2441481 : Nat := 118140960795 + 2441481 * 2 ^ 59
def prefixEnd_2441481 : Nat := 4983230072969 + 3 ^ 40 * 2441481 * 2
def baseEnd_2441481 : Nat := 1253653261819867428059339

theorem tailTrace_2441481 : CollatzResearch.WordTrace tailWord_2441481 prefixEnd_2441481 1253653261819867428059339 := by
  unfold tailWord_2441481
  simp only [CollatzResearch.WordTrace]
  refine ⟨89048127667938783603092297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59365418445292522402061531 89048127667938783603092297)
  ·
    refine ⟨66786095750954087702319223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89048127667938783603092297 66786095750954087702319223)
    ·
      refine ⟨100179143626431131553478835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66786095750954087702319223 100179143626431131553478835)
      ·
        refine ⟨150268715439646697330218253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100179143626431131553478835 150268715439646697330218253)
        ·
          refine ⟨56350768289867511498831845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 150268715439646697330218253 56350768289867511498831845)
          ·
            refine ⟨10565769054350158406030971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56350768289867511498831845 10565769054350158406030971)
            ·
              refine ⟨15848653581525237609046457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10565769054350158406030971 15848653581525237609046457)
              ·
                refine ⟨11886490186143928206784843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15848653581525237609046457 11886490186143928206784843)
                ·
                  refine ⟨17829735279215892310177265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11886490186143928206784843 17829735279215892310177265)
                  ·
                    refine ⟨13372301459411919232632949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17829735279215892310177265 13372301459411919232632949)
                    ·
                      refine ⟨1253653261819867428059339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13372301459411919232632949 1253653261819867428059339)
                      ·
                        rfl

theorem cell23_2441481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 2, 1, 2, 5].length) (baseStart_2441481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2441481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2441481 prefixEnd_2441481 := by exact prefixLift 2441481
  have htrace : WordTrace (prefixWord ++ tailWord_2441481) baseStart_2441481 baseEnd_2441481 := by
    simpa [prefixWord, tailWord_2441481, baseEnd_2441481] using wordTrace_append hprefix tailTrace_2441481
  have hstable : (prefixWord ++ tailWord_2441481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2441481).length < 2 ^ (prefixWord ++ tailWord_2441481).sum := by decide
  have hdescent : baseEnd_2441481 < baseStart_2441481 := by decide
  rcases family_descends (prefixWord ++ tailWord_2441481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2441502 : List Nat := [4, 3, 2, 1, 1, 2, 1, 1, 2, 3, 3]
def baseStart_2441502 : Nat := 118140960795 + 2441502 * 2 ^ 59
def prefixEnd_2441502 : Nat := 4983230072969 + 3 ^ 40 * 2441502 * 2
def baseEnd_2441502 : Nat := 1253664044913611845896743

theorem tailTrace_2441502 : CollatzResearch.WordTrace tailWord_2441502 prefixEnd_2441502 1253664044913611845896743 := by
  unfold tailWord_2441502
  simp only [CollatzResearch.WordTrace]
  refine ⟨11131111700107838023700845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59365929067241802793071173 11131111700107838023700845)
  ·
    refine ⟨4174166887540439258887817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11131111700107838023700845 4174166887540439258887817)
    ·
      refine ⟨3130625165655329444165863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4174166887540439258887817 3130625165655329444165863)
      ·
        refine ⟨4695937748482994166248795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3130625165655329444165863 4695937748482994166248795)
        ·
          refine ⟨7043906622724491249373193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4695937748482994166248795 7043906622724491249373193)
          ·
            refine ⟨5282929967043368437029895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7043906622724491249373193 5282929967043368437029895)
            ·
              refine ⟨7924394950565052655544843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5282929967043368437029895 7924394950565052655544843)
              ·
                refine ⟨11886592425847578983317265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7924394950565052655544843 11886592425847578983317265)
                ·
                  refine ⟨8914944319385684237487949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11886592425847578983317265 8914944319385684237487949)
                  ·
                    refine ⟨3343104119769631589057981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8914944319385684237487949 3343104119769631589057981)
                    ·
                      refine ⟨1253664044913611845896743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3343104119769631589057981 1253664044913611845896743)
                      ·
                        rfl

theorem cell23_2441502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_2441502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2441502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2441502 prefixEnd_2441502 := by exact prefixLift 2441502
  have htrace : WordTrace (prefixWord ++ tailWord_2441502) baseStart_2441502 baseEnd_2441502 := by
    simpa [prefixWord, tailWord_2441502, baseEnd_2441502] using wordTrace_append hprefix tailTrace_2441502
  have hstable : (prefixWord ++ tailWord_2441502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2441502).length < 2 ^ (prefixWord ++ tailWord_2441502).sum := by decide
  have hdescent : baseEnd_2441502 < baseStart_2441502 := by decide
  rcases family_descends (prefixWord ++ tailWord_2441502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2441522 : List Nat := [3, 2, 1, 1, 6, 1, 1, 1, 2, 5]
def baseStart_2441522 : Nat := 118140960795 + 2441522 * 2 ^ 59
def prefixEnd_2441522 : Nat := 4983230072969 + 3 ^ 40 * 2441522 * 2
def baseEnd_2441522 : Nat := 417891438175567255882217

theorem tailTrace_2441522 : CollatzResearch.WordTrace tailWord_2441522 prefixEnd_2441522 417891438175567255882217 := by
  unfold tailWord_2441522
  simp only [CollatzResearch.WordTrace]
  refine ⟨22262405765197561901333705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59366415373860165070223213 22262405765197561901333705)
  ·
    refine ⟨16696804323898171426000279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22262405765197561901333705 16696804323898171426000279)
    ·
      refine ⟨25045206485847257139000419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16696804323898171426000279 25045206485847257139000419)
      ·
        refine ⟨37567809728770885708500629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25045206485847257139000419 37567809728770885708500629)
        ·
          refine ⟨1760991081036135267585967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 37567809728770885708500629 1760991081036135267585967)
          ·
            refine ⟨2641486621554202901378951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1760991081036135267585967 2641486621554202901378951)
            ·
              refine ⟨3962229932331304352068427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2641486621554202901378951 3962229932331304352068427)
              ·
                refine ⟨5943344898496956528102641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3962229932331304352068427 5943344898496956528102641)
                ·
                  refine ⟨4457508673872717396076981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5943344898496956528102641 4457508673872717396076981)
                  ·
                    refine ⟨417891438175567255882217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4457508673872717396076981 417891438175567255882217)
                    ·
                      rfl

theorem cell23_2441522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 1, 2, 5].length) (baseStart_2441522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2441522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2441522 prefixEnd_2441522 := by exact prefixLift 2441522
  have htrace : WordTrace (prefixWord ++ tailWord_2441522) baseStart_2441522 baseEnd_2441522 := by
    simpa [prefixWord, tailWord_2441522, baseEnd_2441522] using wordTrace_append hprefix tailTrace_2441522
  have hstable : (prefixWord ++ tailWord_2441522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2441522).length < 2 ^ (prefixWord ++ tailWord_2441522).sum := by decide
  have hdescent : baseEnd_2441522 < baseStart_2441522 := by decide
  rcases family_descends (prefixWord ++ tailWord_2441522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2441585 : List Nat := [1, 2, 2, 2, 1, 2, 1, 5, 2, 3, 2]
def baseStart_2441585 : Nat := 118140960795 + 2441585 * 2 ^ 59
def prefixEnd_2441585 : Nat := 4983230072969 + 3 ^ 40 * 2441585 * 2
def baseEnd_2441585 : Nat := 1253706663807935021158861

theorem tailTrace_2441585 : CollatzResearch.WordTrace tailWord_2441585 prefixEnd_2441585 1253706663807935021158861 := by
  unfold tailWord_2441585
  simp only [CollatzResearch.WordTrace]
  refine ⟨89051920859562009364878209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59367947239708006243252139 89051920859562009364878209)
  ·
    refine ⟨66788940644671507023658657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89051920859562009364878209 66788940644671507023658657)
    ·
      refine ⟨50091705483503630267743993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66788940644671507023658657 50091705483503630267743993)
      ·
        refine ⟨37568779112627722700807995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50091705483503630267743993 37568779112627722700807995)
        ·
          refine ⟨56353168668941584051211993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37568779112627722700807995 56353168668941584051211993)
          ·
            refine ⟨42264876501706188038408995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56353168668941584051211993 42264876501706188038408995)
            ·
              refine ⟨63397314752559282057613493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42264876501706188038408995 63397314752559282057613493)
              ·
                refine ⟨5943498258052432692901265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 63397314752559282057613493 5943498258052432692901265)
                ·
                  refine ⟨4457623693539324519675949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5943498258052432692901265 4457623693539324519675949)
                  ·
                    refine ⟨1671608885077246694878481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4457623693539324519675949 1671608885077246694878481)
                    ·
                      refine ⟨1253706663807935021158861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1671608885077246694878481 1253706663807935021158861)
                      ·
                        rfl

theorem cell23_2441585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 5, 2, 3, 2].length) (baseStart_2441585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2441585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2441585 prefixEnd_2441585 := by exact prefixLift 2441585
  have htrace : WordTrace (prefixWord ++ tailWord_2441585) baseStart_2441585 baseEnd_2441585 := by
    simpa [prefixWord, tailWord_2441585, baseEnd_2441585] using wordTrace_append hprefix tailTrace_2441585
  have hstable : (prefixWord ++ tailWord_2441585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2441585).length < 2 ^ (prefixWord ++ tailWord_2441585).sum := by decide
  have hdescent : baseEnd_2441585 < baseStart_2441585 := by decide
  rcases family_descends (prefixWord ++ tailWord_2441585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2441625 : List Nat := [1, 2, 1, 2, 1, 4, 3, 3, 2, 4]
def baseStart_2441625 : Nat := 118140960795 + 2441625 * 2 ^ 59
def prefixEnd_2441625 : Nat := 4983230072969 + 3 ^ 40 * 2441625 * 2
def baseEnd_2441625 : Nat := 417909067678038288219559

theorem tailTrace_2441625 : CollatzResearch.WordTrace tailWord_2441625 prefixEnd_2441625 417909067678038288219559 := by
  unfold tailWord_2441625
  simp only [CollatzResearch.WordTrace]
  refine ⟨89053379779417096196334329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59368919852944730797556219 89053379779417096196334329)
  ·
    refine ⟨66790034834562822147250747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89053379779417096196334329 66790034834562822147250747)
    ·
      refine ⟨100185052251844233220876121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66790034834562822147250747 100185052251844233220876121)
      ·
        refine ⟨75138789188883174915657091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100185052251844233220876121 75138789188883174915657091)
        ·
          refine ⟨112708183783324762373485637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75138789188883174915657091 112708183783324762373485637)
          ·
            refine ⟨21132784459373392945028557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 112708183783324762373485637 21132784459373392945028557)
            ·
              refine ⟨7924794172265022354385709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21132784459373392945028557 7924794172265022354385709)
              ·
                refine ⟨2971797814599383382894641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7924794172265022354385709 2971797814599383382894641)
                ·
                  refine ⟨2228848360949537537170981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2971797814599383382894641 2228848360949537537170981)
                  ·
                    refine ⟨417909067678038288219559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2228848360949537537170981 417909067678038288219559)
                    ·
                      rfl

theorem cell23_2441625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 3, 2, 4].length) (baseStart_2441625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2441625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2441625 prefixEnd_2441625 := by exact prefixLift 2441625
  have htrace : WordTrace (prefixWord ++ tailWord_2441625) baseStart_2441625 baseEnd_2441625 := by
    simpa [prefixWord, tailWord_2441625, baseEnd_2441625] using wordTrace_append hprefix tailTrace_2441625
  have hstable : (prefixWord ++ tailWord_2441625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2441625).length < 2 ^ (prefixWord ++ tailWord_2441625).sum := by decide
  have hdescent : baseEnd_2441625 < baseStart_2441625 := by decide
  rcases family_descends (prefixWord ++ tailWord_2441625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2441629 : List Nat := [1, 4, 2, 1, 5, 1, 1, 2, 1, 5]
def baseStart_2441629 : Nat := 118140960795 + 2441629 * 2 ^ 59
def prefixEnd_2441629 : Nat := 4983230072969 + 3 ^ 40 * 2441629 * 2
def baseEnd_2441629 : Nat := 417909752318910949669553

theorem tailTrace_2441629 : CollatzResearch.WordTrace tailWord_2441629 prefixEnd_2441629 417909752318910949669553 := by
  unfold tailWord_2441629
  simp only [CollatzResearch.WordTrace]
  refine ⟨89053525671402604879479941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59369017114268403252986627 89053525671402604879479941)
  ·
    refine ⟨16697536063387988414902489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89053525671402604879479941 16697536063387988414902489)
    ·
      refine ⟨12523152047540991311176867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16697536063387988414902489 12523152047540991311176867)
      ·
        refine ⟨18784728071311486966765301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12523152047540991311176867 18784728071311486966765301)
        ·
          refine ⟨1761068256685451903134247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18784728071311486966765301 1761068256685451903134247)
          ·
            refine ⟨2641602385028177854701371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1761068256685451903134247 2641602385028177854701371)
            ·
              refine ⟨3962403577542266782052057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2641602385028177854701371 3962403577542266782052057)
              ·
                refine ⟨2971802683156700086539043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3962403577542266782052057 2971802683156700086539043)
                ·
                  refine ⟨4457704024735050129808565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2971802683156700086539043 4457704024735050129808565)
                  ·
                    refine ⟨417909752318910949669553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4457704024735050129808565 417909752318910949669553)
                    ·
                      rfl

theorem cell23_2441629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 2, 1, 5].length) (baseStart_2441629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2441629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2441629 prefixEnd_2441629 := by exact prefixLift 2441629
  have htrace : WordTrace (prefixWord ++ tailWord_2441629) baseStart_2441629 baseEnd_2441629 := by
    simpa [prefixWord, tailWord_2441629, baseEnd_2441629] using wordTrace_append hprefix tailTrace_2441629
  have hstable : (prefixWord ++ tailWord_2441629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2441629).length < 2 ^ (prefixWord ++ tailWord_2441629).sum := by decide
  have hdescent : baseEnd_2441629 < baseStart_2441629 := by decide
  rcases family_descends (prefixWord ++ tailWord_2441629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2441632 : List Nat := [2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 4]
def baseStart_2441632 : Nat := 118140960795 + 2441632 * 2 ^ 59
def prefixEnd_2441632 : Nat := 4983230072969 + 3 ^ 40 * 2441632 * 2
def baseEnd_2441632 : Nat := 1253730797398696337271145

theorem tailTrace_2441632 : CollatzResearch.WordTrace tailWord_2441632 prefixEnd_2441632 1253730797398696337271145 := by
  unfold tailWord_2441632
  simp only [CollatzResearch.WordTrace]
  refine ⟨44526817545195868195919575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59369090060261157594559433 44526817545195868195919575)
  ·
    refine ⟨66790226317793802293879363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44526817545195868195919575 66790226317793802293879363)
    ·
      refine ⟨100185339476690703440819045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66790226317793802293879363 100185339476690703440819045)
      ·
        refine ⟨18784751151879506895153571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 100185339476690703440819045 18784751151879506895153571)
        ·
          refine ⟨28177126727819260342730357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18784751151879506895153571 28177126727819260342730357)
          ·
            refine ⟨2641605630733055657130971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28177126727819260342730357 2641605630733055657130971)
            ·
              refine ⟨3962408446099583485696457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2641605630733055657130971 3962408446099583485696457)
              ·
                refine ⟨2971806334574687614272343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3962408446099583485696457 2971806334574687614272343)
                ·
                  refine ⟨4457709501862031421408515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2971806334574687614272343 4457709501862031421408515)
                  ·
                    refine ⟨6686564252793047132112773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4457709501862031421408515 6686564252793047132112773)
                    ·
                      refine ⟨1253730797398696337271145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6686564252793047132112773 1253730797398696337271145)
                      ·
                        rfl

theorem cell23_2441632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 4].length) (baseStart_2441632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2441632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2441632 prefixEnd_2441632 := by exact prefixLift 2441632
  have htrace : WordTrace (prefixWord ++ tailWord_2441632) baseStart_2441632 baseEnd_2441632 := by
    simpa [prefixWord, tailWord_2441632, baseEnd_2441632] using wordTrace_append hprefix tailTrace_2441632
  have hstable : (prefixWord ++ tailWord_2441632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2441632).length < 2 ^ (prefixWord ++ tailWord_2441632).sum := by decide
  have hdescent : baseEnd_2441632 < baseStart_2441632 := by decide
  rcases family_descends (prefixWord ++ tailWord_2441632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2441635 : List Nat := [1, 1, 1, 4, 1, 5, 1, 1, 3, 2, 3]
def baseStart_2441635 : Nat := 118140960795 + 2441635 * 2 ^ 59
def prefixEnd_2441635 : Nat := 4983230072969 + 3 ^ 40 * 2441635 * 2
def baseEnd_2441635 : Nat := 1253732337840659825533631

theorem tailTrace_2441635 : CollatzResearch.WordTrace tailWord_2441635 prefixEnd_2441635 1253732337840659825533631 := by
  unfold tailWord_2441635
  simp only [CollatzResearch.WordTrace]
  refine ⟨89053744509380867904198359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59369163006253911936132239 89053744509380867904198359)
  ·
    refine ⟨133580616764071301856297539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89053744509380867904198359 133580616764071301856297539)
    ·
      refine ⟨200370925146106952784446309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133580616764071301856297539 200370925146106952784446309)
      ·
        refine ⟨37569548464895053647083683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 200370925146106952784446309 37569548464895053647083683)
        ·
          refine ⟨56354322697342580470625525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37569548464895053647083683 56354322697342580470625525)
          ·
            refine ⟨5283217752875866919121143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 56354322697342580470625525 5283217752875866919121143)
            ·
              refine ⟨7924826629313800378681715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5283217752875866919121143 7924826629313800378681715)
              ·
                refine ⟨11887239943970700568022573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7924826629313800378681715 11887239943970700568022573)
                ·
                  refine ⟨4457714978989012713008465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11887239943970700568022573 4457714978989012713008465)
                  ·
                    refine ⟨3343286234241759534756349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4457714978989012713008465 3343286234241759534756349)
                    ·
                      refine ⟨1253732337840659825533631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3343286234241759534756349 1253732337840659825533631)
                      ·
                        rfl

theorem cell23_2441635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 1, 3, 2, 3].length) (baseStart_2441635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2441635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2441635 prefixEnd_2441635 := by exact prefixLift 2441635
  have htrace : WordTrace (prefixWord ++ tailWord_2441635) baseStart_2441635 baseEnd_2441635 := by
    simpa [prefixWord, tailWord_2441635, baseEnd_2441635] using wordTrace_append hprefix tailTrace_2441635
  have hstable : (prefixWord ++ tailWord_2441635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2441635).length < 2 ^ (prefixWord ++ tailWord_2441635).sum := by decide
  have hdescent : baseEnd_2441635 < baseStart_2441635 := by decide
  rcases family_descends (prefixWord ++ tailWord_2441635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2441678 : List Nat := [4, 1, 1, 1, 2, 1, 1, 2, 1, 4, 5]
def baseStart_2441678 : Nat := 118140960795 + 2441678 * 2 ^ 59
def prefixEnd_2441678 : Nat := 4983230072969 + 3 ^ 40 * 2441678 * 2
def baseEnd_2441678 : Nat := 1253754417508803157295933

theorem tailTrace_2441678 : CollatzResearch.WordTrace tailWord_2441678 prefixEnd_2441678 1253754417508803157295933 := by
  unfold tailWord_2441678
  simp only [CollatzResearch.WordTrace]
  refine ⟨11131914106028135781001711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59370208565483390832009125 11131914106028135781001711)
  ·
    refine ⟨16697871159042203671502567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11131914106028135781001711 16697871159042203671502567)
    ·
      refine ⟨25046806738563305507253851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16697871159042203671502567 25046806738563305507253851)
      ·
        refine ⟨37570210107844958260880777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25046806738563305507253851 37570210107844958260880777)
        ·
          refine ⟨28177657580883718695660583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37570210107844958260880777 28177657580883718695660583)
          ·
            refine ⟨42266486371325578043490875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28177657580883718695660583 42266486371325578043490875)
            ·
              refine ⟨63399729556988367065236313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42266486371325578043490875 63399729556988367065236313)
              ·
                refine ⟨47549797167741275298927235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63399729556988367065236313 47549797167741275298927235)
                ·
                  refine ⟨71324695751611912948390853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47549797167741275298927235 71324695751611912948390853)
                  ·
                    refine ⟨13373380453427233677823285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 71324695751611912948390853 13373380453427233677823285)
                    ·
                      refine ⟨1253754417508803157295933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13373380453427233677823285 1253754417508803157295933)
                      ·
                        rfl

theorem cell23_2441678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 1, 4, 5].length) (baseStart_2441678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2441678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2441678 prefixEnd_2441678 := by exact prefixLift 2441678
  have htrace : WordTrace (prefixWord ++ tailWord_2441678) baseStart_2441678 baseEnd_2441678 := by
    simpa [prefixWord, tailWord_2441678, baseEnd_2441678] using wordTrace_append hprefix tailTrace_2441678
  have hstable : (prefixWord ++ tailWord_2441678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2441678).length < 2 ^ (prefixWord ++ tailWord_2441678).sum := by decide
  have hdescent : baseEnd_2441678 < baseStart_2441678 := by decide
  rcases family_descends (prefixWord ++ tailWord_2441678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2441688 : List Nat := [2, 1, 2, 2, 2, 1, 1, 1, 4, 3, 4]
def baseStart_2441688 : Nat := 118140960795 + 2441688 * 2 ^ 59
def prefixEnd_2441688 : Nat := 4983230072969 + 3 ^ 40 * 2441688 * 2
def baseEnd_2441688 : Nat := 1253759552315348118170887

theorem tailTrace_2441688 : CollatzResearch.WordTrace tailWord_2441688 prefixEnd_2441688 1253759552315348118170887 := by
  unfold tailWord_2441688
  simp only [CollatzResearch.WordTrace]
  refine ⟨44527838789094428977938859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59370451718792571970585145 44527838789094428977938859)
  ·
    refine ⟨66791758183641643466908289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44527838789094428977938859 66791758183641643466908289)
    ·
      refine ⟨50093818637731232600181217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66791758183641643466908289 50093818637731232600181217)
      ·
        refine ⟨37570363978298424450135913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50093818637731232600181217 37570363978298424450135913)
        ·
          refine ⟨28177772983723818337601935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37570363978298424450135913 28177772983723818337601935)
          ·
            refine ⟨42266659475585727506402903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28177772983723818337601935 42266659475585727506402903)
            ·
              refine ⟨63399989213378591259604355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42266659475585727506402903 63399989213378591259604355)
              ·
                refine ⟨95099983820067886889406533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63399989213378591259604355 95099983820067886889406533)
                ·
                  refine ⟨17831246966262728791763725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 95099983820067886889406533 17831246966262728791763725)
                  ·
                    refine ⟨6686717612348523296911397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17831246966262728791763725 6686717612348523296911397)
                    ·
                      refine ⟨1253759552315348118170887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6686717612348523296911397 1253759552315348118170887)
                      ·
                        rfl

theorem cell23_2441688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 4, 3, 4].length) (baseStart_2441688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2441688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2441688 prefixEnd_2441688 := by exact prefixLift 2441688
  have htrace : WordTrace (prefixWord ++ tailWord_2441688) baseStart_2441688 baseEnd_2441688 := by
    simpa [prefixWord, tailWord_2441688, baseEnd_2441688] using wordTrace_append hprefix tailTrace_2441688
  have hstable : (prefixWord ++ tailWord_2441688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2441688).length < 2 ^ (prefixWord ++ tailWord_2441688).sum := by decide
  have hdescent : baseEnd_2441688 < baseStart_2441688 := by decide
  rcases family_descends (prefixWord ++ tailWord_2441688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
