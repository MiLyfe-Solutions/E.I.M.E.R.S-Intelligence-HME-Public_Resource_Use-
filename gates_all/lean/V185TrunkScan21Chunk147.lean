import V185TrunkScan21Chunk146

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_1793673 : List Nat := [1, 2, 1, 1, 4, 1, 4, 2, 5]
def baseStart_1793673 : Nat := 118140960795 + 1793673 * 2 ^ 59
def prefixEnd_1793673 : Nat := 4983230072969 + 3 ^ 40 * 1793673 * 2
def baseEnd_1793673 : Nat := 409340615996473768817135

theorem tailTrace_1793673 : CollatzResearch.WordTrace tailWord_1793673 prefixEnd_1793673 409340615996473768817135 := by
  unfold tailWord_1793673
  simp only [CollatzResearch.WordTrace]
  refine ⟨65420628830836530804937673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43613752553891020536625115 65420628830836530804937673)
  ·
    refine ⟨49065471623127398103703255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65420628830836530804937673 49065471623127398103703255)
    ·
      refine ⟨73598207434691097155554883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49065471623127398103703255 73598207434691097155554883)
      ·
        refine ⟨110397311152036645733332325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73598207434691097155554883 110397311152036645733332325)
        ·
          refine ⟨20699495841006871074999811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110397311152036645733332325 20699495841006871074999811)
          ·
            refine ⟨31049243761510306612499717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20699495841006871074999811 31049243761510306612499717)
            ·
              refine ⟨5821733205283182489843697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31049243761510306612499717 5821733205283182489843697)
              ·
                refine ⟨4366299903962386867382773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5821733205283182489843697 4366299903962386867382773)
                ·
                  refine ⟨409340615996473768817135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4366299903962386867382773 409340615996473768817135)
                  ·
                    rfl

theorem cell21_1793673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 2, 5].length) (baseStart_1793673 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1793673 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1793673 prefixEnd_1793673 := by exact prefixLift 1793673
  have htrace : WordTrace (prefixWord ++ tailWord_1793673) baseStart_1793673 baseEnd_1793673 := by
    simpa [prefixWord, tailWord_1793673, baseEnd_1793673] using wordTrace_append hprefix tailTrace_1793673
  have hstable : (prefixWord ++ tailWord_1793673).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1793673).length < 2 ^ (prefixWord ++ tailWord_1793673).sum := by decide
  have hdescent : baseEnd_1793673 < baseStart_1793673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1793673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1793721 : List Nat := [1, 2, 1, 4, 1, 1, 6, 1, 4]
def baseStart_1793721 : Nat := 118140960795 + 1793721 * 2 ^ 59
def prefixEnd_1793721 : Nat := 4983230072969 + 3 ^ 40 * 1793721 * 2
def baseEnd_1793721 : Nat := 409351570250436352017037

theorem tailTrace_1793721 : CollatzResearch.WordTrace tailWord_1793721 prefixEnd_1793721 409351570250436352017037 := by
  unfold tailWord_1793721
  simp only [CollatzResearch.WordTrace]
  refine ⟨65422379534662635002685017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43614919689775090001790011 65422379534662635002685017)
  ·
    refine ⟨49066784650996976252013763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65422379534662635002685017 49066784650996976252013763)
    ·
      refine ⟨73600176976495464378020645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49066784650996976252013763 73600176976495464378020645)
      ·
        refine ⟨13800033183092899570878871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73600176976495464378020645 13800033183092899570878871)
        ·
          refine ⟨20700049774639349356318307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13800033183092899570878871 20700049774639349356318307)
          ·
            refine ⟨31050074661959024034477461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20700049774639349356318307 31050074661959024034477461)
            ·
              refine ⟨1455472249779329251616131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 31050074661959024034477461 1455472249779329251616131)
              ·
                refine ⟨2183208374668993877424197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1455472249779329251616131 2183208374668993877424197)
                ·
                  refine ⟨409351570250436352017037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2183208374668993877424197 409351570250436352017037)
                  ·
                    rfl

theorem cell21_1793721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 6, 1, 4].length) (baseStart_1793721 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1793721 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1793721 prefixEnd_1793721 := by exact prefixLift 1793721
  have htrace : WordTrace (prefixWord ++ tailWord_1793721) baseStart_1793721 baseEnd_1793721 := by
    simpa [prefixWord, tailWord_1793721, baseEnd_1793721] using wordTrace_append hprefix tailTrace_1793721
  have hstable : (prefixWord ++ tailWord_1793721).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1793721).length < 2 ^ (prefixWord ++ tailWord_1793721).sum := by decide
  have hdescent : baseEnd_1793721 < baseStart_1793721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1793721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1793825 : List Nat := [1, 2, 3, 2, 1, 3, 1, 3, 5]
def baseStart_1793825 : Nat := 118140960795 + 1793825 * 2 ^ 59
def prefixEnd_1793825 : Nat := 4983230072969 + 3 ^ 40 * 1793825 * 2
def baseEnd_1793825 : Nat := 409375304467355282283491

theorem tailTrace_1793825 : CollatzResearch.WordTrace tailWord_1793825 prefixEnd_1793825 409375304467355282283491 := by
  unfold tailWord_1793825
  simp only [CollatzResearch.WordTrace]
  refine ⟨65426172726285860764470929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43617448484190573842980619 65426172726285860764470929)
  ·
    refine ⟨49069629544714395573353197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65426172726285860764470929 49069629544714395573353197)
    ·
      refine ⟨18401111079267898340007449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49069629544714395573353197 18401111079267898340007449)
      ·
        refine ⟨13800833309450923755005587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18401111079267898340007449 13800833309450923755005587)
        ·
          refine ⟨20701249964176385632508381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13800833309450923755005587 20701249964176385632508381)
          ·
            refine ⟨7762968736566144612190643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20701249964176385632508381 7762968736566144612190643)
            ·
              refine ⟨11644453104849216918285965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7762968736566144612190643 11644453104849216918285965)
              ·
                refine ⟨4366669914318456344357237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11644453104849216918285965 4366669914318456344357237)
                ·
                  refine ⟨409375304467355282283491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4366669914318456344357237 409375304467355282283491)
                  ·
                    rfl

theorem cell21_1793825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 3, 5].length) (baseStart_1793825 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1793825 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1793825 prefixEnd_1793825 := by exact prefixLift 1793825
  have htrace : WordTrace (prefixWord ++ tailWord_1793825) baseStart_1793825 baseEnd_1793825 := by
    simpa [prefixWord, tailWord_1793825, baseEnd_1793825] using wordTrace_append hprefix tailTrace_1793825
  have hstable : (prefixWord ++ tailWord_1793825).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1793825).length < 2 ^ (prefixWord ++ tailWord_1793825).sum := by decide
  have hdescent : baseEnd_1793825 < baseStart_1793825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1793825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1793845 : List Nat := [1, 3, 3, 1, 5, 1, 2, 5]
def baseStart_1793845 : Nat := 118140960795 + 1793845 * 2 ^ 59
def prefixEnd_1793845 : Nat := 4983230072969 + 3 ^ 40 * 1793845 * 2
def baseEnd_1793845 : Nat := 136459956246613230650039

theorem tailTrace_1793845 : CollatzResearch.WordTrace tailWord_1793845 prefixEnd_1793845 136459956246613230650039 := by
  unfold tailWord_1793845
  simp only [CollatzResearch.WordTrace]
  refine ⟨65426902186213404180198989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43617934790808936120132659 65426902186213404180198989)
  ·
    refine ⟨24535088319830026567574621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65426902186213404180198989 24535088319830026567574621)
    ·
      refine ⟨9200658119936259962840483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24535088319830026567574621 9200658119936259962840483)
      ·
        refine ⟨13800987179904389944260725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9200658119936259962840483 13800987179904389944260725)
        ·
          refine ⟨1293842548116036557274443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13800987179904389944260725 1293842548116036557274443)
          ·
            refine ⟨1940763822174054835911665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1293842548116036557274443 1940763822174054835911665)
            ·
              refine ⟨1455572866630541126933749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1940763822174054835911665 1455572866630541126933749)
              ·
                refine ⟨136459956246613230650039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1455572866630541126933749 136459956246613230650039)
                ·
                  rfl

theorem cell21_1793845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 2, 5].length) (baseStart_1793845 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1793845 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1793845 prefixEnd_1793845 := by exact prefixLift 1793845
  have htrace : WordTrace (prefixWord ++ tailWord_1793845) baseStart_1793845 baseEnd_1793845 := by
    simpa [prefixWord, tailWord_1793845, baseEnd_1793845] using wordTrace_append hprefix tailTrace_1793845
  have hstable : (prefixWord ++ tailWord_1793845).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1793845).length < 2 ^ (prefixWord ++ tailWord_1793845).sum := by decide
  have hdescent : baseEnd_1793845 < baseStart_1793845 := by decide
  rcases family_descends (prefixWord ++ tailWord_1793845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1793859 : List Nat := [1, 1, 1, 3, 1, 7, 1, 3, 3]
def baseStart_1793859 : Nat := 118140960795 + 1793859 * 2 ^ 59
def prefixEnd_1793859 : Nat := 4983230072969 + 3 ^ 40 * 1793859 * 2
def baseEnd_1793859 : Nat := 409383063730578778716755

theorem tailTrace_1793859 : CollatzResearch.WordTrace tailWord_1793859 prefixEnd_1793859 409383063730578778716755 := by
  unfold tailWord_1793859
  simp only [CollatzResearch.WordTrace]
  refine ⟨65427412808162684571208631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43618275205441789714139087 65427412808162684571208631)
  ·
    refine ⟨98141119212244026856812947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65427412808162684571208631 98141119212244026856812947)
    ·
      refine ⟨147211678818366040285219421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98141119212244026856812947 147211678818366040285219421)
      ·
        refine ⟨55204379556887265106957283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147211678818366040285219421 55204379556887265106957283)
        ·
          refine ⟨82806569335330897660435925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55204379556887265106957283 82806569335330897660435925)
          ·
            refine ⟨1940778968796817913916467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 82806569335330897660435925 1940778968796817913916467)
            ·
              refine ⟨2911168453195226870874701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1940778968796817913916467 2911168453195226870874701)
              ·
                refine ⟨1091688169948210076578013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2911168453195226870874701 1091688169948210076578013)
                ·
                  refine ⟨409383063730578778716755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1091688169948210076578013 409383063730578778716755)
                  ·
                    rfl

theorem cell21_1793859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 3, 3].length) (baseStart_1793859 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1793859 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1793859 prefixEnd_1793859 := by exact prefixLift 1793859
  have htrace : WordTrace (prefixWord ++ tailWord_1793859) baseStart_1793859 baseEnd_1793859 := by
    simpa [prefixWord, tailWord_1793859, baseEnd_1793859] using wordTrace_append hprefix tailTrace_1793859
  have hstable : (prefixWord ++ tailWord_1793859).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1793859).length < 2 ^ (prefixWord ++ tailWord_1793859).sum := by decide
  have hdescent : baseEnd_1793859 < baseStart_1793859 := by decide
  rcases family_descends (prefixWord ++ tailWord_1793859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1793876 : List Nat := [2, 4, 1, 1, 3, 2, 3, 2, 3]
def baseStart_1793876 : Nat := 118140960795 + 1793876 * 2 ^ 59
def prefixEnd_1793876 : Nat := 4983230072969 + 3 ^ 40 * 1793876 * 2
def baseEnd_1793876 : Nat := 409386943362190526933387

theorem tailTrace_1793876 : CollatzResearch.WordTrace tailWord_1793876 prefixEnd_1793876 409386943362190526933387 := by
  unfold tailWord_1793876
  simp only [CollatzResearch.WordTrace]
  refine ⟨32714016424550548237288741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43618688566067397649718321 32714016424550548237288741)
  ·
    refine ⟨6133878079603227794491639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32714016424550548237288741 6133878079603227794491639)
    ·
      refine ⟨9200817119404841691737459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6133878079603227794491639 9200817119404841691737459)
      ·
        refine ⟨13801225679107262537606189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9200817119404841691737459 13801225679107262537606189)
        ·
          refine ⟨5175459629665223451602321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13801225679107262537606189 5175459629665223451602321)
          ·
            refine ⟨3881594722248917588701741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5175459629665223451602321 3881594722248917588701741)
            ·
              refine ⟨1455598020843344095763153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3881594722248917588701741 1455598020843344095763153)
              ·
                refine ⟨1091698515632508071822365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1455598020843344095763153 1091698515632508071822365)
                ·
                  refine ⟨409386943362190526933387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1091698515632508071822365 409386943362190526933387)
                  ·
                    rfl

theorem cell21_1793876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 3, 2, 3].length) (baseStart_1793876 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1793876 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1793876 prefixEnd_1793876 := by exact prefixLift 1793876
  have htrace : WordTrace (prefixWord ++ tailWord_1793876) baseStart_1793876 baseEnd_1793876 := by
    simpa [prefixWord, tailWord_1793876, baseEnd_1793876] using wordTrace_append hprefix tailTrace_1793876
  have hstable : (prefixWord ++ tailWord_1793876).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1793876).length < 2 ^ (prefixWord ++ tailWord_1793876).sum := by decide
  have hdescent : baseEnd_1793876 < baseStart_1793876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1793876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1793890 : List Nat := [3, 3, 2, 1, 2, 1, 4, 1, 4]
def baseStart_1793890 : Nat := 118140960795 + 1793890 * 2 ^ 59
def prefixEnd_1793890 : Nat := 4983230072969 + 3 ^ 40 * 1793890 * 2
def baseEnd_1793890 : Nat := 409390138352929613700025

theorem tailTrace_1793890 : CollatzResearch.WordTrace tailWord_1793890 prefixEnd_1793890 409390138352929613700025 := by
  unfold tailWord_1793890
  simp only [CollatzResearch.WordTrace]
  refine ⟨16357135867762594216396781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43619028980700251243724749 16357135867762594216396781)
  ·
    refine ⟨6133925950410972831148793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16357135867762594216396781 6133925950410972831148793)
    ·
      refine ⟨4600444462808229623361595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6133925950410972831148793 4600444462808229623361595)
      ·
        refine ⟨6900666694212344435042393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4600444462808229623361595 6900666694212344435042393)
        ·
          refine ⟨5175500020659258326281795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6900666694212344435042393 5175500020659258326281795)
          ·
            refine ⟨7763250030988887489422693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5175500020659258326281795 7763250030988887489422693)
            ·
              refine ⟨1455609380810416404266755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7763250030988887489422693 1455609380810416404266755)
              ·
                refine ⟨2183414071215624606400133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1455609380810416404266755 2183414071215624606400133)
                ·
                  refine ⟨409390138352929613700025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2183414071215624606400133 409390138352929613700025)
                  ·
                    rfl

theorem cell21_1793890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 4, 1, 4].length) (baseStart_1793890 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1793890 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1793890 prefixEnd_1793890 := by exact prefixLift 1793890
  have htrace : WordTrace (prefixWord ++ tailWord_1793890) baseStart_1793890 baseEnd_1793890 := by
    simpa [prefixWord, tailWord_1793890, baseEnd_1793890] using wordTrace_append hprefix tailTrace_1793890
  have hstable : (prefixWord ++ tailWord_1793890).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1793890).length < 2 ^ (prefixWord ++ tailWord_1793890).sum := by decide
  have hdescent : baseEnd_1793890 < baseStart_1793890 := by decide
  rcases family_descends (prefixWord ++ tailWord_1793890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1793901 : List Nat := [1, 5, 1, 1, 1, 1, 2, 4, 5]
def baseStart_1793901 : Nat := 118140960795 + 1793901 * 2 ^ 59
def prefixEnd_1793901 : Nat := 4983230072969 + 3 ^ 40 * 1793901 * 2
def baseEnd_1793901 : Nat := 409392648702796039016669

theorem tailTrace_1793901 : CollatzResearch.WordTrace tailWord_1793901 prefixEnd_1793901 409392648702796039016669 := by
  unfold tailWord_1793901
  simp only [CollatzResearch.WordTrace]
  refine ⟨65428944674010525744237557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43619296449340350496158371 65428944674010525744237557)
  ·
    refine ⟨6133963563188486788522271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 65428944674010525744237557 6133963563188486788522271)
    ·
      refine ⟨9200945344782730182783407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6133963563188486788522271 9200945344782730182783407)
      ·
        refine ⟨13801418017174095274175111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9200945344782730182783407 13801418017174095274175111)
        ·
          refine ⟨20702127025761142911262667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13801418017174095274175111 20702127025761142911262667)
          ·
            refine ⟨31053190538641714366894001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20702127025761142911262667 31053190538641714366894001)
            ·
              refine ⟨23289892903981285775170501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31053190538641714366894001 23289892903981285775170501)
              ·
                refine ⟨4366854919496491082844469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23289892903981285775170501 4366854919496491082844469)
                ·
                  refine ⟨409392648702796039016669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4366854919496491082844469 409392648702796039016669)
                  ·
                    rfl

theorem cell21_1793901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_1793901 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1793901 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1793901 prefixEnd_1793901 := by exact prefixLift 1793901
  have htrace : WordTrace (prefixWord ++ tailWord_1793901) baseStart_1793901 baseEnd_1793901 := by
    simpa [prefixWord, tailWord_1793901, baseEnd_1793901] using wordTrace_append hprefix tailTrace_1793901
  have hstable : (prefixWord ++ tailWord_1793901).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1793901).length < 2 ^ (prefixWord ++ tailWord_1793901).sum := by decide
  have hdescent : baseEnd_1793901 < baseStart_1793901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1793901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1793994 : List Nat := [3, 1, 2, 1, 2, 1, 4, 4, 3]
def baseStart_1793994 : Nat := 118140960795 + 1793994 * 2 ^ 59
def prefixEnd_1793994 : Nat := 4983230072969 + 3 ^ 40 * 1793994 * 2
def baseEnd_1793994 : Nat := 409413872569848543966479

theorem tailTrace_1793994 : CollatzResearch.WordTrace tailWord_1793994 prefixEnd_1793994 409413872569848543966479 := by
  unfold tailWord_1793994
  simp only [CollatzResearch.WordTrace]
  refine ⟨16358084165668400656843259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43621557775115735084915357 16358084165668400656843259)
  ·
    refine ⟨24537126248502600985264889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16358084165668400656843259 24537126248502600985264889)
    ·
      refine ⟨18402844686376950738948667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24537126248502600985264889 18402844686376950738948667)
      ·
        refine ⟨27604267029565426108423001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18402844686376950738948667 27604267029565426108423001)
        ·
          refine ⟨20703200272174069581317251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27604267029565426108423001 20703200272174069581317251)
          ·
            refine ⟨31054800408261104371975877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20703200272174069581317251 31054800408261104371975877)
            ·
              refine ⟨5822775076548957069745477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31054800408261104371975877 5822775076548957069745477)
              ·
                refine ⟨1091770326852929450577277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5822775076548957069745477 1091770326852929450577277)
                ·
                  refine ⟨409413872569848543966479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1091770326852929450577277 409413872569848543966479)
                  ·
                    rfl

theorem cell21_1793994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 4, 3].length) (baseStart_1793994 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1793994 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1793994 prefixEnd_1793994 := by exact prefixLift 1793994
  have htrace : WordTrace (prefixWord ++ tailWord_1793994) baseStart_1793994 baseEnd_1793994 := by
    simpa [prefixWord, tailWord_1793994, baseEnd_1793994] using wordTrace_append hprefix tailTrace_1793994
  have hstable : (prefixWord ++ tailWord_1793994).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1793994).length < 2 ^ (prefixWord ++ tailWord_1793994).sum := by decide
  have hdescent : baseEnd_1793994 < baseStart_1793994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1793994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794053 : List Nat := [1, 3, 1, 1, 2, 4, 3, 1, 5]
def baseStart_1794053 : Nat := 118140960795 + 1794053 * 2 ^ 59
def prefixEnd_1794053 : Nat := 4983230072969 + 3 ^ 40 * 1794053 * 2
def baseEnd_1794053 : Nat := 409427337173677552483025

theorem tailTrace_1794053 : CollatzResearch.WordTrace tailWord_1794053 prefixEnd_1794053 409427337173677552483025 := by
  unfold tailWord_1794053
  simp only [CollatzResearch.WordTrace]
  refine ⟨65434488569459855703770813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43622992379639903802513875 65434488569459855703770813)
  ·
    refine ⟨24537933213547445888914055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65434488569459855703770813 24537933213547445888914055)
    ·
      refine ⟨36806899820321168833371083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24537933213547445888914055 36806899820321168833371083)
      ·
        refine ⟨55210349730481753250056625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36806899820321168833371083 55210349730481753250056625)
        ·
          refine ⟨41407762297861314937542469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55210349730481753250056625 41407762297861314937542469)
          ·
            refine ⟨7763955430848996550789213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41407762297861314937542469 7763955430848996550789213)
            ·
              refine ⟨2911483286568373706545955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7763955430848996550789213 2911483286568373706545955)
              ·
                refine ⟨4367224929852560559818933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2911483286568373706545955 4367224929852560559818933)
                ·
                  refine ⟨409427337173677552483025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4367224929852560559818933 409427337173677552483025)
                  ·
                    rfl

theorem cell21_1794053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 5].length) (baseStart_1794053 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1794053 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1794053 prefixEnd_1794053 := by exact prefixLift 1794053
  have htrace : WordTrace (prefixWord ++ tailWord_1794053) baseStart_1794053 baseEnd_1794053 := by
    simpa [prefixWord, tailWord_1794053, baseEnd_1794053] using wordTrace_append hprefix tailTrace_1794053
  have hstable : (prefixWord ++ tailWord_1794053).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794053).length < 2 ^ (prefixWord ++ tailWord_1794053).sum := by decide
  have hdescent : baseEnd_1794053 < baseStart_1794053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794104 : List Nat := [2, 1, 2, 1, 6, 2, 2, 2, 3]
def baseStart_1794104 : Nat := 118140960795 + 1794104 * 2 ^ 59
def prefixEnd_1794104 : Nat := 4983230072969 + 3 ^ 40 * 1794104 * 2
def baseEnd_1794104 : Nat := 409438976068512797132921

theorem tailTrace_1794104 : CollatzResearch.WordTrace tailWord_1794104 prefixEnd_1794104 409438976068512797132921 := by
  unfold tailWord_1794104
  simp only [CollatzResearch.WordTrace]
  refine ⟨32718174346137545706938683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43624232461516727609251577 32718174346137545706938683)
  ·
    refine ⟨49077261519206318560408025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32718174346137545706938683 49077261519206318560408025)
    ·
      refine ⟨36807946139404738920306019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49077261519206318560408025 36807946139404738920306019)
      ·
        refine ⟨55211919209107108380459029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36807946139404738920306019 55211919209107108380459029)
        ·
          refine ⟨2588058712926895705334017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 55211919209107108380459029 2588058712926895705334017)
          ·
            refine ⟨1941044034695171779000513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2588058712926895705334017 1941044034695171779000513)
            ·
              refine ⟨1455783026021378834250385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1941044034695171779000513 1455783026021378834250385)
              ·
                refine ⟨1091837269516034125687789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1455783026021378834250385 1091837269516034125687789)
                ·
                  refine ⟨409438976068512797132921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1091837269516034125687789 409438976068512797132921)
                  ·
                    rfl

theorem cell21_1794104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 2, 2, 3].length) (baseStart_1794104 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1794104 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1794104 prefixEnd_1794104 := by exact prefixLift 1794104
  have htrace : WordTrace (prefixWord ++ tailWord_1794104) baseStart_1794104 baseEnd_1794104 := by
    simpa [prefixWord, tailWord_1794104, baseEnd_1794104] using wordTrace_append hprefix tailTrace_1794104
  have hstable : (prefixWord ++ tailWord_1794104).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794104).length < 2 ^ (prefixWord ++ tailWord_1794104).sum := by decide
  have hdescent : baseEnd_1794104 < baseStart_1794104 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794160 : List Nat := [2, 1, 1, 1, 5, 2, 3, 2, 4]
def baseStart_1794160 : Nat := 118140960795 + 1794160 * 2 ^ 59
def prefixEnd_1794160 : Nat := 4983230072969 + 3 ^ 40 * 1794160 * 2
def baseEnd_1794160 : Nat := 409451756031469144199473

theorem tailTrace_1794160 : CollatzResearch.WordTrace tailWord_1794160 prefixEnd_1794160 409451756031469144199473 := by
  unfold tailWord_1794160
  simp only [CollatzResearch.WordTrace]
  refine ⟨32719195590036106488957967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43625594120048141985277289 32719195590036106488957967)
  ·
    refine ⟨49078793385054159733436951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32719195590036106488957967 49078793385054159733436951)
    ·
      refine ⟨73618190077581239600155427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49078793385054159733436951 73618190077581239600155427)
      ·
        refine ⟨110427285116371859400233141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73618190077581239600155427 110427285116371859400233141)
        ·
          refine ⟨10352557979659861818771857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 110427285116371859400233141 10352557979659861818771857)
          ·
            refine ⟨7764418484744896364078893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10352557979659861818771857 7764418484744896364078893)
            ·
              refine ⟨2911656931779336136529585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7764418484744896364078893 2911656931779336136529585)
              ·
                refine ⟨2183742698834502102397189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2911656931779336136529585 2183742698834502102397189)
                ·
                  refine ⟨409451756031469144199473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2183742698834502102397189 409451756031469144199473)
                  ·
                    rfl

theorem cell21_1794160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 2, 4].length) (baseStart_1794160 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1794160 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1794160 prefixEnd_1794160 := by exact prefixLift 1794160
  have htrace : WordTrace (prefixWord ++ tailWord_1794160) baseStart_1794160 baseEnd_1794160 := by
    simpa [prefixWord, tailWord_1794160, baseEnd_1794160] using wordTrace_append hprefix tailTrace_1794160
  have hstable : (prefixWord ++ tailWord_1794160).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794160).length < 2 ^ (prefixWord ++ tailWord_1794160).sum := by decide
  have hdescent : baseEnd_1794160 < baseStart_1794160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794281 : List Nat := [1, 2, 1, 1, 1, 2, 2, 8, 3]
def baseStart_1794281 : Nat := 118140960795 + 1794281 * 2 ^ 59
def prefixEnd_1794281 : Nat := 4983230072969 + 3 ^ 40 * 1794281 * 2
def baseEnd_1794281 : Nat := 409479369879999822682559

theorem tailTrace_1794281 : CollatzResearch.WordTrace tailWord_1794281 prefixEnd_1794281 409479369879999822682559 := by
  unfold tailWord_1794281
  simp only [CollatzResearch.WordTrace]
  refine ⟨65442804412633850643070697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43628536275089233762047131 65442804412633850643070697)
  ·
    refine ⟨49082103309475387982303023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65442804412633850643070697 49082103309475387982303023)
    ·
      refine ⟨73623154964213081973454535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49082103309475387982303023 73623154964213081973454535)
      ·
        refine ⟨110434732446319622960181803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73623154964213081973454535 110434732446319622960181803)
        ·
          refine ⟨165652098669479434440272705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110434732446319622960181803 165652098669479434440272705)
          ·
            refine ⟨124239074002109575830204529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165652098669479434440272705 124239074002109575830204529)
            ·
              refine ⟨93179305501582181872653397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124239074002109575830204529 93179305501582181872653397)
              ·
                refine ⟨1091944986346666193820157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 93179305501582181872653397 1091944986346666193820157)
                ·
                  refine ⟨409479369879999822682559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1091944986346666193820157 409479369879999822682559)
                  ·
                    rfl

theorem cell21_1794281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 8, 3].length) (baseStart_1794281 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1794281 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1794281 prefixEnd_1794281 := by exact prefixLift 1794281
  have htrace : WordTrace (prefixWord ++ tailWord_1794281) baseStart_1794281 baseEnd_1794281 := by
    simpa [prefixWord, tailWord_1794281, baseEnd_1794281] using wordTrace_append hprefix tailTrace_1794281
  have hstable : (prefixWord ++ tailWord_1794281).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794281).length < 2 ^ (prefixWord ++ tailWord_1794281).sum := by decide
  have hdescent : baseEnd_1794281 < baseStart_1794281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794346 : List Nat := [3, 1, 4, 2, 2, 1, 3, 1, 4]
def baseStart_1794346 : Nat := 118140960795 + 1794346 * 2 ^ 59
def prefixEnd_1794346 : Nat := 4983230072969 + 3 ^ 40 * 1794346 * 2
def baseEnd_1794346 : Nat := 409494203765574154099093

theorem tailTrace_1794346 : CollatzResearch.WordTrace tailWord_1794346 prefixEnd_1794346 409494203765574154099093 := by
  unfold tailWord_1794346
  simp only [CollatzResearch.WordTrace]
  refine ⟨16361293789349591686046723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43630116771598911162791261 16361293789349591686046723)
  ·
    refine ⟨24541940684024387529070085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16361293789349591686046723 24541940684024387529070085)
    ·
      refine ⟨4601613878254572661700641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24541940684024387529070085 4601613878254572661700641)
      ·
        refine ⟨3451210408690929496275481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4601613878254572661700641 3451210408690929496275481)
        ·
          refine ⟨2588407806518197122206611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3451210408690929496275481 2588407806518197122206611)
          ·
            refine ⟨3882611709777295683309917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2588407806518197122206611 3882611709777295683309917)
            ·
              refine ⟨1455979391166485881241219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3882611709777295683309917 1455979391166485881241219)
              ·
                refine ⟨2183969086749728821861829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1455979391166485881241219 2183969086749728821861829)
                ·
                  refine ⟨409494203765574154099093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2183969086749728821861829 409494203765574154099093)
                  ·
                    rfl

theorem cell21_1794346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 3, 1, 4].length) (baseStart_1794346 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1794346 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1794346 prefixEnd_1794346 := by exact prefixLift 1794346
  have htrace : WordTrace (prefixWord ++ tailWord_1794346) baseStart_1794346 baseEnd_1794346 := by
    simpa [prefixWord, tailWord_1794346, baseEnd_1794346] using wordTrace_append hprefix tailTrace_1794346
  have hstable : (prefixWord ++ tailWord_1794346).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794346).length < 2 ^ (prefixWord ++ tailWord_1794346).sum := by decide
  have hdescent : baseEnd_1794346 < baseStart_1794346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794385 : List Nat := [1, 2, 2, 1, 4, 2, 9]
def baseStart_1794385 : Nat := 118140960795 + 1794385 * 2 ^ 59
def prefixEnd_1794385 : Nat := 4983230072969 + 3 ^ 40 * 1794385 * 2
def baseEnd_1794385 : Nat := 45500344899657639216557

theorem tailTrace_1794385 : CollatzResearch.WordTrace tailWord_1794385 prefixEnd_1794385 45500344899657639216557 := by
  unfold tailWord_1794385
  simp only [CollatzResearch.WordTrace]
  refine ⟨65446597604257076404856609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43631065069504717603237739 65446597604257076404856609)
  ·
    refine ⟨49084948203192807303642457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65446597604257076404856609 49084948203192807303642457)
    ·
      refine ⟨36813711152394605477731843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49084948203192807303642457 36813711152394605477731843)
      ·
        refine ⟨55220566728591908216597765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36813711152394605477731843 55220566728591908216597765)
        ·
          refine ⟨10353856261610982790612081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55220566728591908216597765 10353856261610982790612081)
          ·
            refine ⟨7765392196208237092959061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10353856261610982790612081 7765392196208237092959061)
            ·
              refine ⟨45500344899657639216557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7765392196208237092959061 45500344899657639216557)
              ·
                rfl

theorem cell21_1794385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 9].length) (baseStart_1794385 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1794385 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1794385 prefixEnd_1794385 := by exact prefixLift 1794385
  have htrace : WordTrace (prefixWord ++ tailWord_1794385) baseStart_1794385 baseEnd_1794385 := by
    simpa [prefixWord, tailWord_1794385, baseEnd_1794385] using wordTrace_append hprefix tailTrace_1794385
  have hstable : (prefixWord ++ tailWord_1794385).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794385).length < 2 ^ (prefixWord ++ tailWord_1794385).sum := by decide
  have hdescent : baseEnd_1794385 < baseStart_1794385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794402 : List Nat := [3, 3, 2, 1, 1, 2, 1, 8]
def baseStart_1794402 : Nat := 118140960795 + 1794402 * 2 ^ 59
def prefixEnd_1794402 : Nat := 4983230072969 + 3 ^ 40 * 1794402 * 2
def baseEnd_1794402 : Nat := 136502327909510167055215

theorem tailTrace_1794402 : CollatzResearch.WordTrace tailWord_1794402 prefixEnd_1794402 136502327909510167055215 := by
  unfold tailWord_1794402
  simp only [CollatzResearch.WordTrace]
  refine ⟨16361804411298872077056365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43631478430130325538816973 16361804411298872077056365)
  ·
    refine ⟨6135676654237077028896137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16361804411298872077056365 6135676654237077028896137)
    ·
      refine ⟨4601757490677807771672103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6135676654237077028896137 4601757490677807771672103)
      ·
        refine ⟨6902636236016711657508155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4601757490677807771672103 6902636236016711657508155)
        ·
          refine ⟨10353954354025067486262233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6902636236016711657508155 10353954354025067486262233)
          ·
            refine ⟨7765465765518800614696675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10353954354025067486262233 7765465765518800614696675)
            ·
              refine ⟨11648198648278200922045013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7765465765518800614696675 11648198648278200922045013)
              ·
                refine ⟨136502327909510167055215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11648198648278200922045013 136502327909510167055215)
                ·
                  rfl

theorem cell21_1794402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 8].length) (baseStart_1794402 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1794402 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1794402 prefixEnd_1794402 := by exact prefixLift 1794402
  have htrace : WordTrace (prefixWord ++ tailWord_1794402) baseStart_1794402 baseEnd_1794402 := by
    simpa [prefixWord, tailWord_1794402, baseEnd_1794402] using wordTrace_append hprefix tailTrace_1794402
  have hstable : (prefixWord ++ tailWord_1794402).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794402).length < 2 ^ (prefixWord ++ tailWord_1794402).sum := by decide
  have hdescent : baseEnd_1794402 < baseStart_1794402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794405 : List Nat := [1, 3, 1, 3, 1, 5, 2, 1, 4]
def baseStart_1794405 : Nat := 118140960795 + 1794405 * 2 ^ 59
def prefixEnd_1794405 : Nat := 4983230072969 + 3 ^ 40 * 1794405 * 2
def baseEnd_1794405 : Nat := 409507668369403162615639

theorem tailTrace_1794405 : CollatzResearch.WordTrace tailWord_1794405 prefixEnd_1794405 409507668369403162615639 := by
  unfold tailWord_1794405
  simp only [CollatzResearch.WordTrace]
  refine ⟨65447327064184619820584669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43631551376123079880389779 65447327064184619820584669)
  ·
    refine ⟨24542747649069232432719251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65447327064184619820584669 24542747649069232432719251)
    ·
      refine ⟨36814121473603848649078877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24542747649069232432719251 36814121473603848649078877)
      ·
        refine ⟨13805295552601443243404579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36814121473603848649078877 13805295552601443243404579)
        ·
          refine ⟨20707943328902164865106869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13805295552601443243404579 20707943328902164865106869)
          ·
            refine ⟨1941369687084577956103769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20707943328902164865106869 1941369687084577956103769)
            ·
              refine ⟨1456027265313433467077827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1941369687084577956103769 1456027265313433467077827)
              ·
                refine ⟨2184040897970150200616741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1456027265313433467077827 2184040897970150200616741)
                ·
                  refine ⟨409507668369403162615639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2184040897970150200616741 409507668369403162615639)
                  ·
                    rfl

theorem cell21_1794405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 2, 1, 4].length) (baseStart_1794405 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1794405 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1794405 prefixEnd_1794405 := by exact prefixLift 1794405
  have htrace : WordTrace (prefixWord ++ tailWord_1794405) baseStart_1794405 baseEnd_1794405 := by
    simpa [prefixWord, tailWord_1794405, baseEnd_1794405] using wordTrace_append hprefix tailTrace_1794405
  have hstable : (prefixWord ++ tailWord_1794405).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794405).length < 2 ^ (prefixWord ++ tailWord_1794405).sum := by decide
  have hdescent : baseEnd_1794405 < baseStart_1794405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794627 : List Nat := [1, 1, 1, 3, 1, 2, 1, 2, 9]
def baseStart_1794627 : Nat := 118140960795 + 1794627 * 2 ^ 59
def prefixEnd_1794627 : Nat := 4983230072969 + 3 ^ 40 * 1794627 * 2
def baseEnd_1794627 : Nat := 409558331793980109915185

theorem tailTrace_1794627 : CollatzResearch.WordTrace tailWord_1794627 prefixEnd_1794627 409558331793980109915185 := by
  unfold tailWord_1794627
  simp only [CollatzResearch.WordTrace]
  refine ⟨65455424069380351735166135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43636949379586901156777423 65455424069380351735166135)
  ·
    refine ⟨98183136104070527602749203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65455424069380351735166135 98183136104070527602749203)
    ·
      refine ⟨147274704156105791404123805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98183136104070527602749203 147274704156105791404123805)
      ·
        refine ⟨55228014058539671776546427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147274704156105791404123805 55228014058539671776546427)
        ·
          refine ⟨82842021087809507664819641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55228014058539671776546427 82842021087809507664819641)
          ·
            refine ⟨62131515815857130748614731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82842021087809507664819641 62131515815857130748614731)
            ·
              refine ⟨93197273723785696122922097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62131515815857130748614731 93197273723785696122922097)
              ·
                refine ⟨69897955292839272092191573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93197273723785696122922097 69897955292839272092191573)
                ·
                  refine ⟨409558331793980109915185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 69897955292839272092191573 409558331793980109915185)
                  ·
                    rfl

theorem cell21_1794627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 9].length) (baseStart_1794627 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1794627 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1794627 prefixEnd_1794627 := by exact prefixLift 1794627
  have htrace : WordTrace (prefixWord ++ tailWord_1794627) baseStart_1794627 baseEnd_1794627 := by
    simpa [prefixWord, tailWord_1794627, baseEnd_1794627] using wordTrace_append hprefix tailTrace_1794627
  have hstable : (prefixWord ++ tailWord_1794627).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794627).length < 2 ^ (prefixWord ++ tailWord_1794627).sum := by decide
  have hdescent : baseEnd_1794627 < baseStart_1794627 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794644 : List Nat := [2, 4, 1, 1, 1, 3, 1, 1, 7]
def baseStart_1794644 : Nat := 118140960795 + 1794644 * 2 ^ 59
def prefixEnd_1794644 : Nat := 4983230072969 + 3 ^ 40 * 1794644 * 2
def baseEnd_1794644 : Nat := 409562211425591858131817

theorem tailTrace_1794644 : CollatzResearch.WordTrace tailWord_1794644 prefixEnd_1794644 409562211425591858131817 := by
  unfold tailWord_1794644
  simp only [CollatzResearch.WordTrace]
  refine ⟨32728022055159381819267493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43637362740212509092356657 32728022055159381819267493)
  ·
    refine ⟨6136504135342384091112655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32728022055159381819267493 6136504135342384091112655)
    ·
      refine ⟨9204756203013576136668983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6136504135342384091112655 9204756203013576136668983)
      ·
        refine ⟨13807134304520364205003475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9204756203013576136668983 13807134304520364205003475)
        ·
          refine ⟨20710701456780546307505213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13807134304520364205003475 20710701456780546307505213)
          ·
            refine ⟨7766513046292704865314455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20710701456780546307505213 7766513046292704865314455)
            ·
              refine ⟨11649769569439057297971683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7766513046292704865314455 11649769569439057297971683)
              ·
                refine ⟨17474654354158585946957525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11649769569439057297971683 17474654354158585946957525)
                ·
                  refine ⟨409562211425591858131817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17474654354158585946957525 409562211425591858131817)
                  ·
                    rfl

theorem cell21_1794644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_1794644 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1794644 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1794644 prefixEnd_1794644 := by exact prefixLift 1794644
  have htrace : WordTrace (prefixWord ++ tailWord_1794644) baseStart_1794644 baseEnd_1794644 := by
    simpa [prefixWord, tailWord_1794644, baseEnd_1794644] using wordTrace_append hprefix tailTrace_1794644
  have hstable : (prefixWord ++ tailWord_1794644).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794644).length < 2 ^ (prefixWord ++ tailWord_1794644).sum := by decide
  have hdescent : baseEnd_1794644 < baseStart_1794644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794678 : List Nat := [5, 1, 1, 2, 3, 1, 2, 1, 5]
def baseStart_1794678 : Nat := 118140960795 + 1794678 * 2 ^ 59
def prefixEnd_1794678 : Nat := 4983230072969 + 3 ^ 40 * 1794678 * 2
def baseEnd_1794678 : Nat := 409569970688815354565081

theorem tailTrace_1794678 : CollatzResearch.WordTrace tailWord_1794678 prefixEnd_1794678 409569970688815354565081 := by
  unfold tailWord_1794678
  simp only [CollatzResearch.WordTrace]
  refine ⟨4091080262012224215329543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43638189461463724963515125 4091080262012224215329543)
  ·
    refine ⟨6136620393018336322994315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4091080262012224215329543 6136620393018336322994315)
    ·
      refine ⟨9204930589527504484491473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6136620393018336322994315 9204930589527504484491473)
      ·
        refine ⟨6903697942145628363368605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9204930589527504484491473 6903697942145628363368605)
        ·
          refine ⟨2588886728304610636263227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6903697942145628363368605 2588886728304610636263227)
          ·
            refine ⟨3883330092456915954394841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2588886728304610636263227 3883330092456915954394841)
            ·
              refine ⟨2912497569342686965796131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3883330092456915954394841 2912497569342686965796131)
              ·
                refine ⟨4368746354014030448694197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2912497569342686965796131 4368746354014030448694197)
                ·
                  refine ⟨409569970688815354565081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4368746354014030448694197 409569970688815354565081)
                  ·
                    rfl

theorem cell21_1794678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 1, 5].length) (baseStart_1794678 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1794678 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1794678 prefixEnd_1794678 := by exact prefixLift 1794678
  have htrace : WordTrace (prefixWord ++ tailWord_1794678) baseStart_1794678 baseEnd_1794678 := by
    simpa [prefixWord, tailWord_1794678, baseEnd_1794678] using wordTrace_append hprefix tailTrace_1794678
  have hstable : (prefixWord ++ tailWord_1794678).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794678).length < 2 ^ (prefixWord ++ tailWord_1794678).sum := by decide
  have hdescent : baseEnd_1794678 < baseStart_1794678 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794689 : List Nat := [1, 2, 4, 2, 1, 1, 2, 8]
def baseStart_1794689 : Nat := 118140960795 + 1794689 * 2 ^ 59
def prefixEnd_1794689 : Nat := 4983230072969 + 3 ^ 40 * 1794689 * 2
def baseEnd_1794689 : Nat := 136524160346227259960575

theorem tailTrace_1794689 : CollatzResearch.WordTrace tailWord_1794689 prefixEnd_1794689 136524160346227259960575 := by
  unfold tailWord_1794689
  simp only [CollatzResearch.WordTrace]
  refine ⟨65457685395155736323923121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43638456930103824215948747 65457685395155736323923121)
  ·
    refine ⟨49093264046366802242942341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65457685395155736323923121 49093264046366802242942341)
    ·
      refine ⟨9204987008693775420551689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49093264046366802242942341 9204987008693775420551689)
      ·
        refine ⟨6903740256520331565413767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9204987008693775420551689 6903740256520331565413767)
        ·
          refine ⟨10355610384780497348120651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6903740256520331565413767 10355610384780497348120651)
          ·
            refine ⟨15533415577170746022180977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10355610384780497348120651 15533415577170746022180977)
            ·
              refine ⟨11650061682878059516635733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15533415577170746022180977 11650061682878059516635733)
              ·
                refine ⟨136524160346227259960575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11650061682878059516635733 136524160346227259960575)
                ·
                  rfl

theorem cell21_1794689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 8].length) (baseStart_1794689 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1794689 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1794689 prefixEnd_1794689 := by exact prefixLift 1794689
  have htrace : WordTrace (prefixWord ++ tailWord_1794689) baseStart_1794689 baseEnd_1794689 := by
    simpa [prefixWord, tailWord_1794689, baseEnd_1794689] using wordTrace_append hprefix tailTrace_1794689
  have hstable : (prefixWord ++ tailWord_1794689).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794689).length < 2 ^ (prefixWord ++ tailWord_1794689).sum := by decide
  have hdescent : baseEnd_1794689 < baseStart_1794689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794706 : List Nat := [3, 2, 3, 1, 2, 2, 1, 7]
def baseStart_1794706 : Nat := 118140960795 + 1794706 * 2 ^ 59
def prefixEnd_1794706 : Nat := 4983230072969 + 3 ^ 40 * 1794706 * 2
def baseEnd_1794706 : Nat := 136525453556764509366119

theorem tailTrace_1794706 : CollatzResearch.WordTrace tailWord_1794706 prefixEnd_1794706 136525453556764509366119 := by
  unfold tailWord_1794706
  simp only [CollatzResearch.WordTrace]
  refine ⟨16364576359023537056822993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43638870290729432151527981 16364576359023537056822993)
  ·
    refine ⟨12273432269267652792617245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16364576359023537056822993 12273432269267652792617245)
    ·
      refine ⟨4602537100975369797231467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12273432269267652792617245 4602537100975369797231467)
      ·
        refine ⟨6903805651463054695847201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4602537100975369797231467 6903805651463054695847201)
        ·
          refine ⟨5177854238597291021885401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6903805651463054695847201 5177854238597291021885401)
          ·
            refine ⟨3883390678947968266414051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5177854238597291021885401 3883390678947968266414051)
            ·
              refine ⟨5825086018421952399621077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3883390678947968266414051 5825086018421952399621077)
              ·
                refine ⟨136525453556764509366119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5825086018421952399621077 136525453556764509366119)
                ·
                  rfl

theorem cell21_1794706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 7].length) (baseStart_1794706 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1794706 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1794706 prefixEnd_1794706 := by exact prefixLift 1794706
  have htrace : WordTrace (prefixWord ++ tailWord_1794706) baseStart_1794706 baseEnd_1794706 := by
    simpa [prefixWord, tailWord_1794706, baseEnd_1794706] using wordTrace_append hprefix tailTrace_1794706
  have hstable : (prefixWord ++ tailWord_1794706).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794706).length < 2 ^ (prefixWord ++ tailWord_1794706).sum := by decide
  have hdescent : baseEnd_1794706 < baseStart_1794706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794751 : List Nat := [1, 1, 2, 2, 2, 5, 1, 3, 4]
def baseStart_1794751 : Nat := 118140960795 + 1794751 * 2 ^ 59
def prefixEnd_1794751 : Nat := 4983230072969 + 3 ^ 40 * 1794751 * 2
def baseEnd_1794751 : Nat := 409586630283383449848265

theorem tailTrace_1794751 : CollatzResearch.WordTrace tailWord_1794751 prefixEnd_1794751 409586630283383449848265 := by
  unfold tailWord_1794751
  simp only [CollatzResearch.WordTrace]
  refine ⟨65459946720931120912680107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43639964480620747275120071 65459946720931120912680107)
  ·
    refine ⟨98189920081396681369020161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65459946720931120912680107 98189920081396681369020161)
    ·
      refine ⟨73642440061047511026765121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98189920081396681369020161 73642440061047511026765121)
      ·
        refine ⟨55231830045785633270073841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73642440061047511026765121 55231830045785633270073841)
        ·
          refine ⟨41423872534339224952555381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55231830045785633270073841 41423872534339224952555381)
          ·
            refine ⟨3883488050094302339302067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41423872534339224952555381 3883488050094302339302067)
            ·
              refine ⟨5825232075141453508953101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3883488050094302339302067 5825232075141453508953101)
              ·
                refine ⟨2184462028178045065857413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5825232075141453508953101 2184462028178045065857413)
                ·
                  refine ⟨409586630283383449848265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2184462028178045065857413 409586630283383449848265)
                  ·
                    rfl

theorem cell21_1794751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 3, 4].length) (baseStart_1794751 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1794751 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1794751 prefixEnd_1794751 := by exact prefixLift 1794751
  have htrace : WordTrace (prefixWord ++ tailWord_1794751) baseStart_1794751 baseEnd_1794751 := by
    simpa [prefixWord, tailWord_1794751, baseEnd_1794751] using wordTrace_append hprefix tailTrace_1794751
  have hstable : (prefixWord ++ tailWord_1794751).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794751).length < 2 ^ (prefixWord ++ tailWord_1794751).sum := by decide
  have hdescent : baseEnd_1794751 < baseStart_1794751 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794844 : List Nat := [2, 2, 3, 1, 1, 5, 1, 2, 4]
def baseStart_1794844 : Nat := 118140960795 + 1794844 * 2 ^ 59
def prefixEnd_1794844 : Nat := 4983230072969 + 3 ^ 40 * 1794844 * 2
def baseEnd_1794844 : Nat := 409607854150435954798075

theorem tailTrace_1794844 : CollatzResearch.WordTrace tailWord_1794844 prefixEnd_1794844 409607854150435954798075 := by
  unfold tailWord_1794844
  simp only [CollatzResearch.WordTrace]
  refine ⟨32731669354797098897907793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43642225806396131863877057 32731669354797098897907793)
  ·
    refine ⟨24548752016097824173430845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32731669354797098897907793 24548752016097824173430845)
    ·
      refine ⟨9205782006036684065036567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24548752016097824173430845 9205782006036684065036567)
      ·
        refine ⟨13808673009055026097554851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9205782006036684065036567 13808673009055026097554851)
        ·
          refine ⟨20713009513582539146332277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13808673009055026097554851 20713009513582539146332277)
          ·
            refine ⟨1941844641898363044968651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20713009513582539146332277 1941844641898363044968651)
            ·
              refine ⟨2912766962847544567452977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1941844641898363044968651 2912766962847544567452977)
              ·
                refine ⟨2184575222135658425589733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2912766962847544567452977 2184575222135658425589733)
                ·
                  refine ⟨409607854150435954798075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2184575222135658425589733 409607854150435954798075)
                  ·
                    rfl

theorem cell21_1794844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 2, 4].length) (baseStart_1794844 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1794844 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1794844 prefixEnd_1794844 := by exact prefixLift 1794844
  have htrace : WordTrace (prefixWord ++ tailWord_1794844) baseStart_1794844 baseEnd_1794844 := by
    simpa [prefixWord, tailWord_1794844, baseEnd_1794844] using wordTrace_append hprefix tailTrace_1794844
  have hstable : (prefixWord ++ tailWord_1794844).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794844).length < 2 ^ (prefixWord ++ tailWord_1794844).sum := by decide
  have hdescent : baseEnd_1794844 < baseStart_1794844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794889 : List Nat := [1, 2, 1, 1, 2, 5, 3, 3, 3]
def baseStart_1794889 : Nat := 118140960795 + 1794889 * 2 ^ 59
def prefixEnd_1794889 : Nat := 4983230072969 + 3 ^ 40 * 1794889 * 2
def baseEnd_1794889 : Nat := 409618123763525876547983

theorem tailTrace_1794889 : CollatzResearch.WordTrace tailWord_1794889 prefixEnd_1794889 409618123763525876547983 := by
  unfold tailWord_1794889
  simp only [CollatzResearch.WordTrace]
  refine ⟨65464979994431170481203721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43643319996287446987469147 65464979994431170481203721)
  ·
    refine ⟨49098734995823377860902791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65464979994431170481203721 49098734995823377860902791)
    ·
      refine ⟨73648102493735066791354187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49098734995823377860902791 73648102493735066791354187)
      ·
        refine ⟨110472153740602600187031281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73648102493735066791354187 110472153740602600187031281)
        ·
          refine ⟨82854115305451950140273461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110472153740602600187031281 82854115305451950140273461)
          ·
            refine ⟨7767573309886120325650637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 82854115305451950140273461 7767573309886120325650637)
            ·
              refine ⟨2912839991207295122118989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7767573309886120325650637 2912839991207295122118989)
              ·
                refine ⟨1092314996702735670794621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2912839991207295122118989 1092314996702735670794621)
                ·
                  refine ⟨409618123763525876547983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1092314996702735670794621 409618123763525876547983)
                  ·
                    rfl

theorem cell21_1794889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 3, 3].length) (baseStart_1794889 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1794889 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1794889 prefixEnd_1794889 := by exact prefixLift 1794889
  have htrace : WordTrace (prefixWord ++ tailWord_1794889) baseStart_1794889 baseEnd_1794889 := by
    simpa [prefixWord, tailWord_1794889, baseEnd_1794889] using wordTrace_append hprefix tailTrace_1794889
  have hstable : (prefixWord ++ tailWord_1794889).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794889).length < 2 ^ (prefixWord ++ tailWord_1794889).sum := by decide
  have hdescent : baseEnd_1794889 < baseStart_1794889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794906 : List Nat := [3, 1, 1, 2, 1, 5, 3, 2, 3]
def baseStart_1794906 : Nat := 118140960795 + 1794906 * 2 ^ 59
def prefixEnd_1794906 : Nat := 4983230072969 + 3 ^ 40 * 1794906 * 2
def baseEnd_1794906 : Nat := 409622003395137624764615

theorem tailTrace_1794906 : CollatzResearch.WordTrace tailWord_1794906 prefixEnd_1794906 409622003395137624764615 := by
  unfold tailWord_1794906
  simp only [CollatzResearch.WordTrace]
  refine ⟨16366400008842395596143143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43643733356913054923048381 16366400008842395596143143)
  ·
    refine ⟨24549600013263593394214715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16366400008842395596143143 24549600013263593394214715)
    ·
      refine ⟨36824400019895390091322073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24549600013263593394214715 36824400019895390091322073)
      ·
        refine ⟨27618300014921542568491555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36824400019895390091322073 27618300014921542568491555)
        ·
          refine ⟨41427450022382313852737333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27618300014921542568491555 41427450022382313852737333)
          ·
            refine ⟨3883823439598341923694125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41427450022382313852737333 3883823439598341923694125)
            ·
              refine ⟨1456433789849378221385297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3883823439598341923694125 1456433789849378221385297)
              ·
                refine ⟨1092325342387033666038973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1456433789849378221385297 1092325342387033666038973)
                ·
                  refine ⟨409622003395137624764615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1092325342387033666038973 409622003395137624764615)
                  ·
                    rfl

theorem cell21_1794906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 3, 2, 3].length) (baseStart_1794906 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1794906 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1794906 prefixEnd_1794906 := by exact prefixLift 1794906
  have htrace : WordTrace (prefixWord ++ tailWord_1794906) baseStart_1794906 baseEnd_1794906 := by
    simpa [prefixWord, tailWord_1794906, baseEnd_1794906] using wordTrace_append hprefix tailTrace_1794906
  have hstable : (prefixWord ++ tailWord_1794906).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794906).length < 2 ^ (prefixWord ++ tailWord_1794906).sum := by decide
  have hdescent : baseEnd_1794906 < baseStart_1794906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794920 : List Nat := [2, 1, 4, 2, 1, 2, 4, 1, 4]
def baseStart_1794920 : Nat := 118140960795 + 1794920 * 2 ^ 59
def prefixEnd_1794920 : Nat := 4983230072969 + 3 ^ 40 * 1794920 * 2
def baseEnd_1794920 : Nat := 409625198385876711531253

theorem tailTrace_1794920 : CollatzResearch.WordTrace tailWord_1794920 prefixEnd_1794920 409625198385876711531253 := by
  unfold tailWord_1794920
  simp only [CollatzResearch.WordTrace]
  refine ⟨32733055328659431387791107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43644073771545908517054809 32733055328659431387791107)
  ·
    refine ⟨49099582992989147081686661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32733055328659431387791107 49099582992989147081686661)
    ·
      refine ⟨9206171811185465077816249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49099582992989147081686661 9206171811185465077816249)
      ·
        refine ⟨6904628858389098808362187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9206171811185465077816249 6904628858389098808362187)
        ·
          refine ⟨10356943287583648212543281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6904628858389098808362187 10356943287583648212543281)
          ·
            refine ⟨7767707465687736159407461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10356943287583648212543281 7767707465687736159407461)
            ·
              refine ⟨1456445149816450529888899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7767707465687736159407461 1456445149816450529888899)
              ·
                refine ⟨2184667724724675794833349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1456445149816450529888899 2184667724724675794833349)
                ·
                  refine ⟨409625198385876711531253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2184667724724675794833349 409625198385876711531253)
                  ·
                    rfl

theorem cell21_1794920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 4, 1, 4].length) (baseStart_1794920 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1794920 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1794920 prefixEnd_1794920 := by exact prefixLift 1794920
  have htrace : WordTrace (prefixWord ++ tailWord_1794920) baseStart_1794920 baseEnd_1794920 := by
    simpa [prefixWord, tailWord_1794920, baseEnd_1794920] using wordTrace_append hprefix tailTrace_1794920
  have hstable : (prefixWord ++ tailWord_1794920).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794920).length < 2 ^ (prefixWord ++ tailWord_1794920).sum := by decide
  have hdescent : baseEnd_1794920 < baseStart_1794920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794931 : List Nat := [1, 1, 1, 2, 2, 1, 4, 4, 5]
def baseStart_1794931 : Nat := 118140960795 + 1794931 * 2 ^ 59
def prefixEnd_1794931 : Nat := 4983230072969 + 3 ^ 40 * 1794931 * 2
def baseEnd_1794931 : Nat := 409627708735743136847897

theorem tailTrace_1794931 : CollatzResearch.WordTrace tailWord_1794931 prefixEnd_1794931 409627708735743136847897 := by
  unfold tailWord_1794931
  simp only [CollatzResearch.WordTrace]
  refine ⟨65466511860279011654232647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43644341240186007769488431 65466511860279011654232647)
  ·
    refine ⟨98199767790418517481348971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65466511860279011654232647 98199767790418517481348971)
    ·
      refine ⟨147299651685627776222023457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98199767790418517481348971 147299651685627776222023457)
      ·
        refine ⟨110474738764220832166517593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147299651685627776222023457 110474738764220832166517593)
        ·
          refine ⟨82856054073165624124888195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110474738764220832166517593 82856054073165624124888195)
          ·
            refine ⟨124284081109748436187332293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82856054073165624124888195 124284081109748436187332293)
            ·
              refine ⟨23303265208077831785124805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 124284081109748436187332293 23303265208077831785124805)
              ·
                refine ⟨4369362226514593459710901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23303265208077831785124805 4369362226514593459710901)
                ·
                  refine ⟨409627708735743136847897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4369362226514593459710901 409627708735743136847897)
                  ·
                    rfl

theorem cell21_1794931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 4, 5].length) (baseStart_1794931 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1794931 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1794931 prefixEnd_1794931 := by exact prefixLift 1794931
  have htrace : WordTrace (prefixWord ++ tailWord_1794931) baseStart_1794931 baseEnd_1794931 := by
    simpa [prefixWord, tailWord_1794931, baseEnd_1794931] using wordTrace_append hprefix tailTrace_1794931
  have hstable : (prefixWord ++ tailWord_1794931).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794931).length < 2 ^ (prefixWord ++ tailWord_1794931).sum := by decide
  have hdescent : baseEnd_1794931 < baseStart_1794931 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794934 : List Nat := [5, 1, 1, 3, 1, 1, 2, 7]
def baseStart_1794934 : Nat := 118140960795 + 1794934 * 2 ^ 59
def prefixEnd_1794934 : Nat := 4983230072969 + 3 ^ 40 * 1794934 * 2
def baseEnd_1794934 : Nat := 136542797792205266099297

theorem tailTrace_1794934 : CollatzResearch.WordTrace tailWord_1794934 prefixEnd_1794934 136542797792205266099297 := by
  unfold tailWord_1794934
  simp only [CollatzResearch.WordTrace]
  refine ⟨4091663829954258947911991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43644414186178762111061237 4091663829954258947911991)
  ·
    refine ⟨6137495744931388421867987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4091663829954258947911991 6137495744931388421867987)
    ·
      refine ⟨9206243617397082632801981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6137495744931388421867987 9206243617397082632801981)
      ·
        refine ⟨3452341356523905987300743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9206243617397082632801981 3452341356523905987300743)
        ·
          refine ⟨5178512034785858980951115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3452341356523905987300743 5178512034785858980951115)
          ·
            refine ⟨7767768052178788471426673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5178512034785858980951115 7767768052178788471426673)
            ·
              refine ⟨5825826039134091353570005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7767768052178788471426673 5825826039134091353570005)
              ·
                refine ⟨136542797792205266099297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5825826039134091353570005 136542797792205266099297)
                ·
                  rfl

theorem cell21_1794934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 7].length) (baseStart_1794934 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1794934 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1794934 prefixEnd_1794934 := by exact prefixLift 1794934
  have htrace : WordTrace (prefixWord ++ tailWord_1794934) baseStart_1794934 baseEnd_1794934 := by
    simpa [prefixWord, tailWord_1794934, baseEnd_1794934] using wordTrace_append hprefix tailTrace_1794934
  have hstable : (prefixWord ++ tailWord_1794934).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794934).length < 2 ^ (prefixWord ++ tailWord_1794934).sum := by decide
  have hdescent : baseEnd_1794934 < baseStart_1794934 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794965 : List Nat := [1, 3, 2, 1, 1, 5, 1, 4, 3]
def baseStart_1794965 : Nat := 118140960795 + 1794965 * 2 ^ 59
def prefixEnd_1794965 : Nat := 4983230072969 + 3 ^ 40 * 1794965 * 2
def baseEnd_1794965 : Nat := 409635467998966633281161

theorem tailTrace_1794965 : CollatzResearch.WordTrace tailWord_1794965 prefixEnd_1794965 409635467998966633281161 := by
  unfold tailWord_1794965
  simp only [CollatzResearch.WordTrace]
  refine ⟨65467751942155835460970349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43645167961437223640646899 65467751942155835460970349)
  ·
    refine ⟨24550406978308438297863881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65467751942155835460970349 24550406978308438297863881)
    ·
      refine ⟨18412805233731328723397911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24550406978308438297863881 18412805233731328723397911)
      ·
        refine ⟨27619207850596993085096867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18412805233731328723397911 27619207850596993085096867)
        ·
          refine ⟨41428811775895489627645301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27619207850596993085096867 41428811775895489627645301)
          ·
            refine ⟨3883951103990202152591747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41428811775895489627645301 3883951103990202152591747)
            ·
              refine ⟨5825926655985303228887621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3883951103990202152591747 5825926655985303228887621)
              ·
                refine ⟨1092361247997244355416429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5825926655985303228887621 1092361247997244355416429)
                ·
                  refine ⟨409635467998966633281161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1092361247997244355416429 409635467998966633281161)
                  ·
                    rfl

theorem cell21_1794965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 4, 3].length) (baseStart_1794965 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1794965 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1794965 prefixEnd_1794965 := by exact prefixLift 1794965
  have htrace : WordTrace (prefixWord ++ tailWord_1794965) baseStart_1794965 baseEnd_1794965 := by
    simpa [prefixWord, tailWord_1794965, baseEnd_1794965] using wordTrace_append hprefix tailTrace_1794965
  have hstable : (prefixWord ++ tailWord_1794965).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794965).length < 2 ^ (prefixWord ++ tailWord_1794965).sum := by decide
  have hdescent : baseEnd_1794965 < baseStart_1794965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795128 : List Nat := [2, 1, 2, 1, 5, 10]
def baseStart_1795128 : Nat := 118140960795 + 1795128 * 2 ^ 59
def prefixEnd_1795128 : Nat := 4983230072969 + 3 ^ 40 * 1795128 * 2
def baseEnd_1795128 : Nat := 15173061734063502669043

theorem tailTrace_1795128 : CollatzResearch.WordTrace tailWord_1795128 prefixEnd_1795128 15173061734063502669043 := by
  unfold tailWord_1795128
  simp only [CollatzResearch.WordTrace]
  refine ⟨32736848520282657149577019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43649131360376876199436025 32736848520282657149577019)
  ·
    refine ⟨49105272780423985724365529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32736848520282657149577019 49105272780423985724365529)
    ·
      refine ⟨36828954585317989293274147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49105272780423985724365529 36828954585317989293274147)
      ·
        refine ⟨55243431877976983939911221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36828954585317989293274147 55243431877976983939911221)
        ·
          refine ⟨5179071738560342244366677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 55243431877976983939911221 5179071738560342244366677)
          ·
            refine ⟨15173061734063502669043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5179071738560342244366677 15173061734063502669043)
            ·
              rfl

theorem cell21_1795128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 10].length) (baseStart_1795128 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1795128 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1795128 prefixEnd_1795128 := by exact prefixLift 1795128
  have htrace : WordTrace (prefixWord ++ tailWord_1795128) baseStart_1795128 baseEnd_1795128 := by
    simpa [prefixWord, tailWord_1795128, baseEnd_1795128] using wordTrace_append hprefix tailTrace_1795128
  have hstable : (prefixWord ++ tailWord_1795128).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795128).length < 2 ^ (prefixWord ++ tailWord_1795128).sum := by decide
  have hdescent : baseEnd_1795128 < baseStart_1795128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795134 : List Nat := [4, 2, 1, 3, 1, 2, 1, 4, 3]
def baseStart_1795134 : Nat := 118140960795 + 1795134 * 2 ^ 59
def prefixEnd_1795134 : Nat := 4983230072969 + 3 ^ 40 * 1795134 * 2
def baseEnd_1795134 : Nat := 409674036101459894964149

theorem tailTrace_1795134 : CollatzResearch.WordTrace tailWord_1795134 prefixEnd_1795134 409674036101459894964149 := by
  unfold tailWord_1795134
  simp only [CollatzResearch.WordTrace]
  refine ⟨8184239484817947165484057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43649277252362384882581637 8184239484817947165484057)
  ·
    refine ⟨6138179613613460374113043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8184239484817947165484057 6138179613613460374113043)
    ·
      refine ⟨9207269420420190561169565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6138179613613460374113043 9207269420420190561169565)
      ·
        refine ⟨3452726032657571460438587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9207269420420190561169565 3452726032657571460438587)
        ·
          refine ⟨5179089048986357190657881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3452726032657571460438587 5179089048986357190657881)
          ·
            refine ⟨3884316786739767892993411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5179089048986357190657881 3884316786739767892993411)
            ·
              refine ⟨5826475180109651839490117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3884316786739767892993411 5826475180109651839490117)
              ·
                refine ⟨1092464096270559719904397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5826475180109651839490117 1092464096270559719904397)
                ·
                  refine ⟨409674036101459894964149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1092464096270559719904397 409674036101459894964149)
                  ·
                    rfl

theorem cell21_1795134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 4, 3].length) (baseStart_1795134 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1795134 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1795134 prefixEnd_1795134 := by exact prefixLift 1795134
  have htrace : WordTrace (prefixWord ++ tailWord_1795134) baseStart_1795134 baseEnd_1795134 := by
    simpa [prefixWord, tailWord_1795134, baseEnd_1795134] using wordTrace_append hprefix tailTrace_1795134
  have hstable : (prefixWord ++ tailWord_1795134).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795134).length < 2 ^ (prefixWord ++ tailWord_1795134).sum := by decide
  have hdescent : baseEnd_1795134 < baseStart_1795134 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795303 : List Nat := [1, 1, 5, 3, 2, 2, 2, 2, 3]
def baseStart_1795303 : Nat := 118140960795 + 1795303 * 2 ^ 59
def prefixEnd_1795303 : Nat := 4983230072969 + 3 ^ 40 * 1795303 * 2
def baseEnd_1795303 : Nat := 409712604203953156647137

theorem tailTrace_1795303 : CollatzResearch.WordTrace tailWord_1795303 prefixEnd_1795303 409712604203953156647137 := by
  unfold tailWord_1795303
  simp only [CollatzResearch.WordTrace]
  refine ⟨65480079814931319186774563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43653386543287546124516375 65480079814931319186774563)
  ·
    refine ⟨98220119722396978780161845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65480079814931319186774563 98220119722396978780161845)
    ·
      refine ⟨9208136223974716760640173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 98220119722396978780161845 9208136223974716760640173)
      ·
        refine ⟨3453051083990518785240065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9208136223974716760640173 3453051083990518785240065)
        ·
          refine ⟨2589788312992889088930049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3453051083990518785240065 2589788312992889088930049)
          ·
            refine ⟨1942341234744666816697537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2589788312992889088930049 1942341234744666816697537)
            ·
              refine ⟨1456755926058500112523153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1942341234744666816697537 1456755926058500112523153)
              ·
                refine ⟨1092566944543875084392365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1456755926058500112523153 1092566944543875084392365)
                ·
                  refine ⟨409712604203953156647137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1092566944543875084392365 409712604203953156647137)
                  ·
                    rfl

theorem cell21_1795303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 2, 2, 3].length) (baseStart_1795303 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1795303 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1795303 prefixEnd_1795303 := by exact prefixLift 1795303
  have htrace : WordTrace (prefixWord ++ tailWord_1795303) baseStart_1795303 baseEnd_1795303 := by
    simpa [prefixWord, tailWord_1795303, baseEnd_1795303] using wordTrace_append hprefix tailTrace_1795303
  have hstable : (prefixWord ++ tailWord_1795303).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795303).length < 2 ^ (prefixWord ++ tailWord_1795303).sum := by decide
  have hdescent : baseEnd_1795303 < baseStart_1795303 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795314 : List Nat := [3, 2, 1, 3, 3, 2, 1, 6]
def baseStart_1795314 : Nat := 118140960795 + 1795314 * 2 ^ 59
def prefixEnd_1795314 : Nat := 4983230072969 + 3 ^ 40 * 1795314 * 2
def baseEnd_1795314 : Nat := 136571704851273193987927

theorem tailTrace_1795314 : CollatzResearch.WordTrace tailWord_1795314 prefixEnd_1795314 136571704851273193987927 := by
  unfold tailWord_1795314
  simp only [CollatzResearch.WordTrace]
  refine ⟨16370120254472867016356249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43653654011927645376949997 16370120254472867016356249)
  ·
    refine ⟨12277590190854650262267187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16370120254472867016356249 12277590190854650262267187)
    ·
      refine ⟨18416385286281975393400781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12277590190854650262267187 18416385286281975393400781)
      ·
        refine ⟨6906144482355740772525293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18416385286281975393400781 6906144482355740772525293)
        ·
          refine ⟨2589804180883402789696985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6906144482355740772525293 2589804180883402789696985)
          ·
            refine ⟨1942353135662552092272739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2589804180883402789696985 1942353135662552092272739)
            ·
              refine ⟨2913529703493828138409109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1942353135662552092272739 2913529703493828138409109)
              ·
                refine ⟨136571704851273193987927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2913529703493828138409109 136571704851273193987927)
                ·
                  rfl

theorem cell21_1795314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 6].length) (baseStart_1795314 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1795314 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1795314 prefixEnd_1795314 := by exact prefixLift 1795314
  have htrace : WordTrace (prefixWord ++ tailWord_1795314) baseStart_1795314 baseEnd_1795314 := by
    simpa [prefixWord, tailWord_1795314, baseEnd_1795314] using wordTrace_append hprefix tailTrace_1795314
  have hstable : (prefixWord ++ tailWord_1795314).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795314).length < 2 ^ (prefixWord ++ tailWord_1795314).sum := by decide
  have hdescent : baseEnd_1795314 < baseStart_1795314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795325 : List Nat := [1, 4, 1, 1, 1, 1, 1, 1, 10]
def baseStart_1795325 : Nat := 118140960795 + 1795325 * 2 ^ 59
def prefixEnd_1795325 : Nat := 4983230072969 + 3 ^ 40 * 1795325 * 2
def baseEnd_1795325 : Nat := 409717624903686007280425

theorem tailTrace_1795325 : CollatzResearch.WordTrace tailWord_1795325 prefixEnd_1795325 409717624903686007280425 := by
  unfold tailWord_1795325
  simp only [CollatzResearch.WordTrace]
  refine ⟨65480882220851616944075429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43653921480567744629383619 65480882220851616944075429)
  ·
    refine ⟨12277665416409678177014143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65480882220851616944075429 12277665416409678177014143)
    ·
      refine ⟨18416498124614517265521215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12277665416409678177014143 18416498124614517265521215)
      ·
        refine ⟨27624747186921775898281823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18416498124614517265521215 27624747186921775898281823)
        ·
          refine ⟨41437120780382663847422735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27624747186921775898281823 41437120780382663847422735)
          ·
            refine ⟨62155681170573995771134103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41437120780382663847422735 62155681170573995771134103)
            ·
              refine ⟨93233521755860993656701155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62155681170573995771134103 93233521755860993656701155)
              ·
                refine ⟨139850282633791490485051733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93233521755860993656701155 139850282633791490485051733)
                ·
                  refine ⟨409717624903686007280425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 139850282633791490485051733 409717624903686007280425)
                  ·
                    rfl

theorem cell21_1795325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 10].length) (baseStart_1795325 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1795325 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1795325 prefixEnd_1795325 := by exact prefixLift 1795325
  have htrace : WordTrace (prefixWord ++ tailWord_1795325) baseStart_1795325 baseEnd_1795325 := by
    simpa [prefixWord, tailWord_1795325, baseEnd_1795325] using wordTrace_append hprefix tailTrace_1795325
  have hstable : (prefixWord ++ tailWord_1795325).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795325).length < 2 ^ (prefixWord ++ tailWord_1795325).sum := by decide
  have hdescent : baseEnd_1795325 < baseStart_1795325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795401 : List Nat := [1, 2, 1, 1, 2, 3, 3, 2, 6]
def baseStart_1795401 : Nat := 118140960795 + 1795401 * 2 ^ 59
def prefixEnd_1795401 : Nat := 4983230072969 + 3 ^ 40 * 1795401 * 2
def baseEnd_1795401 : Nat := 409734969139126764013603

theorem tailTrace_1795401 : CollatzResearch.WordTrace tailWord_1795401 prefixEnd_1795401 409734969139126764013603 := by
  unfold tailWord_1795401
  simp only [CollatzResearch.WordTrace]
  refine ⟨65483654168576281923842057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43655769445717521282561371 65483654168576281923842057)
  ·
    refine ⟨49112740626432211442881543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65483654168576281923842057 49112740626432211442881543)
    ·
      refine ⟨73669110939648317164322315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49112740626432211442881543 73669110939648317164322315)
      ·
        refine ⟨110503666409472475746483473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73669110939648317164322315 110503666409472475746483473)
        ·
          refine ⟨82877749807104356809862605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110503666409472475746483473 82877749807104356809862605)
          ·
            refine ⟨31079156177664133803698477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82877749807104356809862605 31079156177664133803698477)
            ·
              refine ⟨11654683566624050176386929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31079156177664133803698477 11654683566624050176386929)
              ·
                refine ⟨8741012674968037632290197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11654683566624050176386929 8741012674968037632290197)
                ·
                  refine ⟨409734969139126764013603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8741012674968037632290197 409734969139126764013603)
                  ·
                    rfl

theorem cell21_1795401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 2, 6].length) (baseStart_1795401 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1795401 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1795401 prefixEnd_1795401 := by exact prefixLift 1795401
  have htrace : WordTrace (prefixWord ++ tailWord_1795401) baseStart_1795401 baseEnd_1795401 := by
    simpa [prefixWord, tailWord_1795401, baseEnd_1795401] using wordTrace_append hprefix tailTrace_1795401
  have hstable : (prefixWord ++ tailWord_1795401).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795401).length < 2 ^ (prefixWord ++ tailWord_1795401).sum := by decide
  have hdescent : baseEnd_1795401 < baseStart_1795401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795477 : List Nat := [1, 3, 2, 1, 1, 2, 2, 3, 6]
def baseStart_1795477 : Nat := 118140960795 + 1795477 * 2 ^ 59
def prefixEnd_1795477 : Nat := 4983230072969 + 3 ^ 40 * 1795477 * 2
def baseEnd_1795477 : Nat := 409752313374567520746781

theorem tailTrace_1795477 : CollatzResearch.WordTrace tailWord_1795477 prefixEnd_1795477 409752313374567520746781 := by
  unfold tailWord_1795477
  simp only [CollatzResearch.WordTrace]
  refine ⟨65486426116300946903608685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43657617410867297935739123 65486426116300946903608685)
  ·
    refine ⟨24557409793612855088853257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65486426116300946903608685 24557409793612855088853257)
    ·
      refine ⟨18418057345209641316639943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24557409793612855088853257 18418057345209641316639943)
      ·
        refine ⟨27627086017814461974959915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18418057345209641316639943 27627086017814461974959915)
        ·
          refine ⟨41440629026721692962439873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27627086017814461974959915 41440629026721692962439873)
          ·
            refine ⟨31080471770041269721829905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41440629026721692962439873 31080471770041269721829905)
            ·
              refine ⟨23310353827530952291372429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31080471770041269721829905 23310353827530952291372429)
              ·
                refine ⟨8741382685324107109264661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23310353827530952291372429 8741382685324107109264661)
                ·
                  refine ⟨409752313374567520746781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8741382685324107109264661 409752313374567520746781)
                  ·
                    rfl

theorem cell21_1795477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 3, 6].length) (baseStart_1795477 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1795477 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1795477 prefixEnd_1795477 := by exact prefixLift 1795477
  have htrace : WordTrace (prefixWord ++ tailWord_1795477) baseStart_1795477 baseEnd_1795477 := by
    simpa [prefixWord, tailWord_1795477, baseEnd_1795477] using wordTrace_append hprefix tailTrace_1795477
  have hstable : (prefixWord ++ tailWord_1795477).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795477).length < 2 ^ (prefixWord ++ tailWord_1795477).sum := by decide
  have hdescent : baseEnd_1795477 < baseStart_1795477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795570 : List Nat := [3, 2, 1, 4, 1, 1, 1, 2, 6]
def baseStart_1795570 : Nat := 118140960795 + 1795570 * 2 ^ 59
def prefixEnd_1795570 : Nat := 4983230072969 + 3 ^ 40 * 1795570 * 2
def baseEnd_1795570 : Nat := 409773537241620025696591

theorem tailTrace_1795570 : CollatzResearch.WordTrace tailWord_1795570 prefixEnd_1795570 409773537241620025696591 := by
  unfold tailWord_1795570
  simp only [CollatzResearch.WordTrace]
  refine ⟨16372454526241005946686041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43659878736642682524496109 16372454526241005946686041)
  ·
    refine ⟨12279340894680754460014531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16372454526241005946686041 12279340894680754460014531)
    ·
      refine ⟨18419011342021131690021797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12279340894680754460014531 18419011342021131690021797)
      ·
        refine ⟨3453564626628962191879087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18419011342021131690021797 3453564626628962191879087)
        ·
          refine ⟨5180346939943443287818631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3453564626628962191879087 5180346939943443287818631)
          ·
            refine ⟨7770520409915164931727947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5180346939943443287818631 7770520409915164931727947)
            ·
              refine ⟨11655780614872747397591921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7770520409915164931727947 11655780614872747397591921)
              ·
                refine ⟨8741835461154560548193941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11655780614872747397591921 8741835461154560548193941)
                ·
                  refine ⟨409773537241620025696591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8741835461154560548193941 409773537241620025696591)
                  ·
                    rfl

theorem cell21_1795570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 2, 6].length) (baseStart_1795570 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1795570 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1795570 prefixEnd_1795570 := by exact prefixLift 1795570
  have htrace : WordTrace (prefixWord ++ tailWord_1795570) baseStart_1795570 baseEnd_1795570 := by
    simpa [prefixWord, tailWord_1795570, baseEnd_1795570] using wordTrace_append hprefix tailTrace_1795570
  have hstable : (prefixWord ++ tailWord_1795570).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795570).length < 2 ^ (prefixWord ++ tailWord_1795570).sum := by decide
  have hdescent : baseEnd_1795570 < baseStart_1795570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795604 : List Nat := [2, 4, 3, 1, 2, 1, 1, 3, 4]
def baseStart_1795604 : Nat := 118140960795 + 1795604 * 2 ^ 59
def prefixEnd_1795604 : Nat := 4983230072969 + 3 ^ 40 * 1795604 * 2
def baseEnd_1795604 : Nat := 409781296504843522129855

theorem tailTrace_1795604 : CollatzResearch.WordTrace tailWord_1795604 prefixEnd_1795604 409781296504843522129855 := by
  unfold tailWord_1795604
  simp only [CollatzResearch.WordTrace]
  refine ⟨32745529093420423796740933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43660705457893898395654577 32745529093420423796740933)
  ·
    refine ⟨6139786705016329461888925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32745529093420423796740933 6139786705016329461888925)
    ·
      refine ⟨2302420014381123548208347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6139786705016329461888925 2302420014381123548208347)
      ·
        refine ⟨3453630021571685322312521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2302420014381123548208347 3453630021571685322312521)
        ·
          refine ⟨2590222516178763991734391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3453630021571685322312521 2590222516178763991734391)
          ·
            refine ⟨3885333774268145987601587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2590222516178763991734391 3885333774268145987601587)
            ·
              refine ⟨5828000661402218981402381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3885333774268145987601587 5828000661402218981402381)
              ·
                refine ⟨2185500248025832118025893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5828000661402218981402381 2185500248025832118025893)
                ·
                  refine ⟨409781296504843522129855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2185500248025832118025893 409781296504843522129855)
                  ·
                    rfl

theorem cell21_1795604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 3, 4].length) (baseStart_1795604 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1795604 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1795604 prefixEnd_1795604 := by exact prefixLift 1795604
  have htrace : WordTrace (prefixWord ++ tailWord_1795604) baseStart_1795604 baseEnd_1795604 := by
    simpa [prefixWord, tailWord_1795604, baseEnd_1795604] using wordTrace_append hprefix tailTrace_1795604
  have hstable : (prefixWord ++ tailWord_1795604).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795604).length < 2 ^ (prefixWord ++ tailWord_1795604).sum := by decide
  have hdescent : baseEnd_1795604 < baseStart_1795604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795660 : List Nat := [2, 2, 1, 3, 1, 3, 3, 6]
def baseStart_1795660 : Nat := 118140960795 + 1795660 * 2 ^ 59
def prefixEnd_1795660 : Nat := 4983230072969 + 3 ^ 40 * 1795660 * 2
def baseEnd_1795660 : Nat := 136598025489266623065469

theorem tailTrace_1795660 : CollatzResearch.WordTrace tailWord_1795660 prefixEnd_1795660 136598025489266623065469 := by
  unfold tailWord_1795660
  simp only [CollatzResearch.WordTrace]
  refine ⟨32746550337318984578760217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43662067116425312771680289 32746550337318984578760217)
  ·
    refine ⟨24559912752989238434070163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32746550337318984578760217 24559912752989238434070163)
    ·
      refine ⟨36839869129483857651105245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24559912752989238434070163 36839869129483857651105245)
      ·
        refine ⟨13814950923556446619164467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36839869129483857651105245 13814950923556446619164467)
        ·
          refine ⟨20722426385334669928746701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13814950923556446619164467 20722426385334669928746701)
          ·
            refine ⟨7770909894500501223280013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20722426385334669928746701 7770909894500501223280013)
            ·
              refine ⟨2914091210437687958730005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7770909894500501223280013 2914091210437687958730005)
              ·
                refine ⟨136598025489266623065469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2914091210437687958730005 136598025489266623065469)
                ·
                  rfl

theorem cell21_1795660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 6].length) (baseStart_1795660 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1795660 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1795660 prefixEnd_1795660 := by exact prefixLift 1795660
  have htrace : WordTrace (prefixWord ++ tailWord_1795660) baseStart_1795660 baseEnd_1795660 := by
    simpa [prefixWord, tailWord_1795660, baseEnd_1795660] using wordTrace_append hprefix tailTrace_1795660
  have hstable : (prefixWord ++ tailWord_1795660).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795660).length < 2 ^ (prefixWord ++ tailWord_1795660).sum := by decide
  have hdescent : baseEnd_1795660 < baseStart_1795660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795705 : List Nat := [1, 2, 1, 3, 3, 1, 3, 1, 6]
def baseStart_1795705 : Nat := 118140960795 + 1795705 * 2 ^ 59
def prefixEnd_1795705 : Nat := 4983230072969 + 3 ^ 40 * 1795705 * 2
def baseEnd_1795705 : Nat := 409804346080889790946315

theorem tailTrace_1795705 : CollatzResearch.WordTrace tailWord_1795705 prefixEnd_1795705 409804346080889790946315 := by
  unfold tailWord_1795705
  simp only [CollatzResearch.WordTrace]
  refine ⟨65494741959474941842908569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43663161306316627895272379 65494741959474941842908569)
  ·
    refine ⟨49121056469606206382181427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65494741959474941842908569 49121056469606206382181427)
    ·
      refine ⟨73681584704409309573272141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49121056469606206382181427 73681584704409309573272141)
      ·
        refine ⟨27630594264153491089977053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73681584704409309573272141 27630594264153491089977053)
        ·
          refine ⟨10361472849057559158741395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27630594264153491089977053 10361472849057559158741395)
          ·
            refine ⟨15542209273586338738112093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10361472849057559158741395 15542209273586338738112093)
            ·
              refine ⟨5828328477594877026792035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15542209273586338738112093 5828328477594877026792035)
              ·
                refine ⟨8742492716392315540188053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5828328477594877026792035 8742492716392315540188053)
                ·
                  refine ⟨409804346080889790946315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8742492716392315540188053 409804346080889790946315)
                  ·
                    rfl

theorem cell21_1795705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 1, 6].length) (baseStart_1795705 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1795705 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1795705 prefixEnd_1795705 := by exact prefixLift 1795705
  have htrace : WordTrace (prefixWord ++ tailWord_1795705) baseStart_1795705 baseEnd_1795705 := by
    simpa [prefixWord, tailWord_1795705, baseEnd_1795705] using wordTrace_append hprefix tailTrace_1795705
  have hstable : (prefixWord ++ tailWord_1795705).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795705).length < 2 ^ (prefixWord ++ tailWord_1795705).sum := by decide
  have hdescent : baseEnd_1795705 < baseStart_1795705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795736 : List Nat := [2, 1, 2, 4, 1, 3, 1, 7]
def baseStart_1795736 : Nat := 118140960795 + 1795736 * 2 ^ 59
def prefixEnd_1795736 : Nat := 4983230072969 + 3 ^ 40 * 1795736 * 2
def baseEnd_1795736 : Nat := 136603806901080208643195

theorem tailTrace_1795736 : CollatzResearch.WordTrace tailWord_1795736 prefixEnd_1795736 136603806901080208643195 := by
  unfold tailWord_1795736
  simp only [CollatzResearch.WordTrace]
  refine ⟨32747936311181317068643531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43663915081575089424858041 32747936311181317068643531)
  ·
    refine ⟨49121904466771975602965297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32747936311181317068643531 49121904466771975602965297)
    ·
      refine ⟨36841428350078981702223973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49121904466771975602965297 36841428350078981702223973)
      ·
        refine ⟨6907767815639809069166995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36841428350078981702223973 6907767815639809069166995)
        ·
          refine ⟨10361651723459713603750493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6907767815639809069166995 10361651723459713603750493)
          ·
            refine ⟨3885619396297392601406435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10361651723459713603750493 3885619396297392601406435)
            ·
              refine ⟨5828429094446088902109653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3885619396297392601406435 5828429094446088902109653)
              ·
                refine ⟨136603806901080208643195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5828429094446088902109653 136603806901080208643195)
                ·
                  rfl

theorem cell21_1795736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 7].length) (baseStart_1795736 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1795736 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1795736 prefixEnd_1795736 := by exact prefixLift 1795736
  have htrace : WordTrace (prefixWord ++ tailWord_1795736) baseStart_1795736 baseEnd_1795736 := by
    simpa [prefixWord, tailWord_1795736, baseEnd_1795736] using wordTrace_append hprefix tailTrace_1795736
  have hstable : (prefixWord ++ tailWord_1795736).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795736).length < 2 ^ (prefixWord ++ tailWord_1795736).sum := by decide
  have hdescent : baseEnd_1795736 < baseStart_1795736 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795742 : List Nat := [4, 3, 1, 1, 1, 4, 1, 3, 3]
def baseStart_1795742 : Nat := 118140960795 + 1795742 * 2 ^ 59
def prefixEnd_1795742 : Nat := 4983230072969 + 3 ^ 40 * 1795742 * 2
def baseEnd_1795742 : Nat := 409812789984985948829573

theorem tailTrace_1795742 : CollatzResearch.WordTrace tailWord_1795742 prefixEnd_1795742 409812789984985948829573 := by
  unfold tailWord_1795742
  simp only [CollatzResearch.WordTrace]
  refine ⟨8187011432542612145250685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43664060973560598108003653 8187011432542612145250685)
  ·
    refine ⟨3070129287203479554469007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8187011432542612145250685 3070129287203479554469007)
    ·
      refine ⟨4605193930805219331703511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3070129287203479554469007 4605193930805219331703511)
      ·
        refine ⟨6907790896207828997555267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4605193930805219331703511 6907790896207828997555267)
        ·
          refine ⟨10361686344311743496332901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6907790896207828997555267 10361686344311743496332901)
          ·
            refine ⟨1942816189558451905562419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10361686344311743496332901 1942816189558451905562419)
            ·
              refine ⟨2914224284337677858343629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1942816189558451905562419 2914224284337677858343629)
              ·
                refine ⟨1092834106626629196878861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2914224284337677858343629 1092834106626629196878861)
                ·
                  refine ⟨409812789984985948829573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1092834106626629196878861 409812789984985948829573)
                  ·
                    rfl

theorem cell21_1795742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 3, 3].length) (baseStart_1795742 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1795742 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1795742 prefixEnd_1795742 := by exact prefixLift 1795742
  have htrace : WordTrace (prefixWord ++ tailWord_1795742) baseStart_1795742 baseEnd_1795742 := by
    simpa [prefixWord, tailWord_1795742, baseEnd_1795742] using wordTrace_append hprefix tailTrace_1795742
  have hstable : (prefixWord ++ tailWord_1795742).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795742).length < 2 ^ (prefixWord ++ tailWord_1795742).sum := by decide
  have hdescent : baseEnd_1795742 < baseStart_1795742 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795767 : List Nat := [1, 1, 3, 1, 5, 1, 3, 1, 5]
def baseStart_1795767 : Nat := 118140960795 + 1795767 * 2 ^ 59
def prefixEnd_1795767 : Nat := 4983230072969 + 3 ^ 40 * 1795767 * 2
def baseEnd_1795767 : Nat := 409818495325591460912855

theorem tailTrace_1795767 : CollatzResearch.WordTrace tailWord_1795767 prefixEnd_1795767 409818495325591460912855 := by
  unfold tailWord_1795767
  simp only [CollatzResearch.WordTrace]
  refine ⟨65497003285250326431665555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43664668856833550954443703 65497003285250326431665555)
  ·
    refine ⟨98245504927875489647498333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65497003285250326431665555 98245504927875489647498333)
    ·
      refine ⟨36842064347953308617811875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98245504927875489647498333 36842064347953308617811875)
      ·
        refine ⟨55263096521929962926717813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36842064347953308617811875 55263096521929962926717813)
        ·
          refine ⟨5180915298930934024379795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 55263096521929962926717813 5180915298930934024379795)
          ·
            refine ⟨7771372948396401036569693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5180915298930934024379795 7771372948396401036569693)
            ·
              refine ⟨2914264855648650388713635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7771372948396401036569693 2914264855648650388713635)
              ·
                refine ⟨4371397283472975583070453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2914264855648650388713635 4371397283472975583070453)
                ·
                  refine ⟨409818495325591460912855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4371397283472975583070453 409818495325591460912855)
                  ·
                    rfl

theorem cell21_1795767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 1, 5].length) (baseStart_1795767 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1795767 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1795767 prefixEnd_1795767 := by exact prefixLift 1795767
  have htrace : WordTrace (prefixWord ++ tailWord_1795767) baseStart_1795767 baseEnd_1795767 := by
    simpa [prefixWord, tailWord_1795767, baseEnd_1795767] using wordTrace_append hprefix tailTrace_1795767
  have hstable : (prefixWord ++ tailWord_1795767).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795767).length < 2 ^ (prefixWord ++ tailWord_1795767).sum := by decide
  have hdescent : baseEnd_1795767 < baseStart_1795767 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795781 : List Nat := [1, 3, 1, 1, 1, 1, 2, 7, 4]
def baseStart_1795781 : Nat := 118140960795 + 1795781 * 2 ^ 59
def prefixEnd_1795781 : Nat := 4983230072969 + 3 ^ 40 * 1795781 * 2
def baseEnd_1795781 : Nat := 409821690316330547679493

theorem tailTrace_1795781 : CollatzResearch.WordTrace tailWord_1795781 prefixEnd_1795781 409821690316330547679493 := by
  unfold tailWord_1795781
  simp only [CollatzResearch.WordTrace]
  refine ⟨65497513907199606822675197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43665009271466404548450131 65497513907199606822675197)
  ·
    refine ⟨24561567715199852558503199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65497513907199606822675197 24561567715199852558503199)
    ·
      refine ⟨36842351572799778837754799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24561567715199852558503199 36842351572799778837754799)
      ·
        refine ⟨55263527359199668256632199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36842351572799778837754799 55263527359199668256632199)
        ·
          refine ⟨82895291038799502384948299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55263527359199668256632199 82895291038799502384948299)
          ·
            refine ⟨124342936558199253577422449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82895291038799502384948299 124342936558199253577422449)
            ·
              refine ⟨93257202418649440183066837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124342936558199253577422449 93257202418649440183066837)
              ·
                refine ⟨2185715681687096254290629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 93257202418649440183066837 2185715681687096254290629)
                ·
                  refine ⟨409821690316330547679493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2185715681687096254290629 409821690316330547679493)
                  ·
                    rfl

theorem cell21_1795781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 7, 4].length) (baseStart_1795781 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1795781 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1795781 prefixEnd_1795781 := by exact prefixLift 1795781
  have htrace : WordTrace (prefixWord ++ tailWord_1795781) baseStart_1795781 baseEnd_1795781 := by
    simpa [prefixWord, tailWord_1795781, baseEnd_1795781] using wordTrace_append hprefix tailTrace_1795781
  have hstable : (prefixWord ++ tailWord_1795781).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795781).length < 2 ^ (prefixWord ++ tailWord_1795781).sum := by decide
  have hdescent : baseEnd_1795781 < baseStart_1795781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795871 : List Nat := [1, 1, 2, 4, 2, 1, 10]
def baseStart_1795871 : Nat := 118140960795 + 1795871 * 2 ^ 59
def prefixEnd_1795871 : Nat := 4983230072969 + 3 ^ 40 * 1795871 * 2
def baseEnd_1795871 : Nat := 45538025504723376797701

theorem tailTrace_1795871 : CollatzResearch.WordTrace tailWord_1795871 prefixEnd_1795871 45538025504723376797701 := by
  unfold tailWord_1795871
  simp only [CollatzResearch.WordTrace]
  refine ⟨65500796476873552193451467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43667197651249034795634311 65500796476873552193451467)
  ·
    refine ⟨98251194715310328290177201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65500796476873552193451467 98251194715310328290177201)
    ·
      refine ⟨73688396036482746217632901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98251194715310328290177201 73688396036482746217632901)
      ·
        refine ⟨13816574256840514915806169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73688396036482746217632901 13816574256840514915806169)
        ·
          refine ⟨10362430692630386186854627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13816574256840514915806169 10362430692630386186854627)
          ·
            refine ⟨15543646038945579280281941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10362430692630386186854627 15543646038945579280281941)
            ·
              refine ⟨45538025504723376797701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15543646038945579280281941 45538025504723376797701)
              ·
                rfl

theorem cell21_1795871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 10].length) (baseStart_1795871 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1795871 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1795871 prefixEnd_1795871 := by exact prefixLift 1795871
  have htrace : WordTrace (prefixWord ++ tailWord_1795871) baseStart_1795871 baseEnd_1795871 := by
    simpa [prefixWord, tailWord_1795871, baseEnd_1795871] using wordTrace_append hprefix tailTrace_1795871
  have hstable : (prefixWord ++ tailWord_1795871).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795871).length < 2 ^ (prefixWord ++ tailWord_1795871).sum := by decide
  have hdescent : baseEnd_1795871 < baseStart_1795871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795891 : List Nat := [1, 1, 1, 2, 7, 1, 3, 1, 4]
def baseStart_1795891 : Nat := 118140960795 + 1795891 * 2 ^ 59
def prefixEnd_1795891 : Nat := 4983230072969 + 3 ^ 40 * 1795891 * 2
def baseEnd_1795891 : Nat := 409846793814994800845935

theorem tailTrace_1795891 : CollatzResearch.WordTrace tailWord_1795891 prefixEnd_1795891 409846793814994800845935 := by
  unfold tailWord_1795891
  simp only [CollatzResearch.WordTrace]
  refine ⟨65501525936801095609179527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43667683957867397072786351 65501525936801095609179527)
  ·
    refine ⟨98252288905201643413769291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65501525936801095609179527 98252288905201643413769291)
    ·
      refine ⟨147378433357802465120653937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98252288905201643413769291 147378433357802465120653937)
      ·
        refine ⟨110533825018351848840490453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147378433357802465120653937 110533825018351848840490453)
        ·
          refine ⟨2590636523867621457198995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 110533825018351848840490453 2590636523867621457198995)
          ·
            refine ⟨3885954785801432185798493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2590636523867621457198995 3885954785801432185798493)
            ·
              refine ⟨1457233044675537069674435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3885954785801432185798493 1457233044675537069674435)
              ·
                refine ⟨2185849567013305604511653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1457233044675537069674435 2185849567013305604511653)
                ·
                  refine ⟨409846793814994800845935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2185849567013305604511653 409846793814994800845935)
                  ·
                    rfl

theorem cell21_1795891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 3, 1, 4].length) (baseStart_1795891 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1795891 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1795891 prefixEnd_1795891 := by exact prefixLift 1795891
  have htrace : WordTrace (prefixWord ++ tailWord_1795891) baseStart_1795891 baseEnd_1795891 := by
    simpa [prefixWord, tailWord_1795891, baseEnd_1795891] using wordTrace_append hprefix tailTrace_1795891
  have hstable : (prefixWord ++ tailWord_1795891).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795891).length < 2 ^ (prefixWord ++ tailWord_1795891).sum := by decide
  have hdescent : baseEnd_1795891 < baseStart_1795891 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1796130 : List Nat := [3, 3, 1, 1, 1, 2, 2, 1, 7]
def baseStart_1796130 : Nat := 118140960795 + 1796130 * 2 ^ 59
def prefixEnd_1796130 : Nat := 4983230072969 + 3 ^ 40 * 1796130 * 2
def baseEnd_1796130 : Nat := 409901336871183496362113

theorem tailTrace_1796130 : CollatzResearch.WordTrace tailWord_1796130 prefixEnd_1796130 409901336871183496362113 := by
  unfold tailWord_1796130
  simp only [CollatzResearch.WordTrace]
  refine ⟨16377560745733809856782461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43673495321956826284753229 16377560745733809856782461)
  ·
    refine ⟨6141585279650178696293423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16377560745733809856782461 6141585279650178696293423)
    ·
      refine ⟨9212377919475268044440135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6141585279650178696293423 9212377919475268044440135)
      ·
        refine ⟨13818566879212902066660203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9212377919475268044440135 13818566879212902066660203)
        ·
          refine ⟨20727850318819353099990305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13818566879212902066660203 20727850318819353099990305)
          ·
            refine ⟨15545887739114514824992729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20727850318819353099990305 15545887739114514824992729)
            ·
              refine ⟨11659415804335886118744547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15545887739114514824992729 11659415804335886118744547)
              ·
                refine ⟨17489123706503829178116821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11659415804335886118744547 17489123706503829178116821)
                ·
                  refine ⟨409901336871183496362113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17489123706503829178116821 409901336871183496362113)
                  ·
                    rfl

theorem cell21_1796130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_1796130 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1796130 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1796130 prefixEnd_1796130 := by exact prefixLift 1796130
  have htrace : WordTrace (prefixWord ++ tailWord_1796130) baseStart_1796130 baseEnd_1796130 := by
    simpa [prefixWord, tailWord_1796130, baseEnd_1796130] using wordTrace_append hprefix tailTrace_1796130
  have hstable : (prefixWord ++ tailWord_1796130).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1796130).length < 2 ^ (prefixWord ++ tailWord_1796130).sum := by decide
  have hdescent : baseEnd_1796130 < baseStart_1796130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1796130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1796192 : List Nat := [2, 1, 1, 3, 2, 4, 3, 5]
def baseStart_1796192 : Nat := 118140960795 + 1796192 * 2 ^ 59
def prefixEnd_1796192 : Nat := 4983230072969 + 3 ^ 40 * 1796192 * 2
def baseEnd_1796192 : Nat := 136638495371961722109551

theorem tailTrace_1796192 : CollatzResearch.WordTrace tailWord_1796192 prefixEnd_1796192 136638495371961722109551 := by
  unfold tailWord_1796192
  simp only [CollatzResearch.WordTrace]
  refine ⟨32756252154355312007943415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43675002872473749343924553 32756252154355312007943415)
  ·
    refine ⟨49134378231532968011915123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32756252154355312007943415 49134378231532968011915123)
    ·
      refine ⟨73701567347299452017872685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49134378231532968011915123 73701567347299452017872685)
      ·
        refine ⟨27638087755237294506702257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73701567347299452017872685 27638087755237294506702257)
        ·
          refine ⟨20728565816427970880026693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27638087755237294506702257 20728565816427970880026693)
          ·
            refine ⟨3886606090580244540005005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20728565816427970880026693 3886606090580244540005005)
            ·
              refine ⟨1457477283967591702501877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3886606090580244540005005 1457477283967591702501877)
              ·
                refine ⟨136638495371961722109551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1457477283967591702501877 136638495371961722109551)
                ·
                  rfl

theorem cell21_1796192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 3, 5].length) (baseStart_1796192 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1796192 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1796192 prefixEnd_1796192 := by exact prefixLift 1796192
  have htrace : WordTrace (prefixWord ++ tailWord_1796192) baseStart_1796192 baseEnd_1796192 := by
    simpa [prefixWord, tailWord_1796192, baseEnd_1796192] using wordTrace_append hprefix tailTrace_1796192
  have hstable : (prefixWord ++ tailWord_1796192).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1796192).length < 2 ^ (prefixWord ++ tailWord_1796192).sum := by decide
  have hdescent : baseEnd_1796192 < baseStart_1796192 := by decide
  rcases family_descends (prefixWord ++ tailWord_1796192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1796206 : List Nat := [4, 1, 2, 2, 1, 1, 1, 2, 7]
def baseStart_1796206 : Nat := 118140960795 + 1796206 * 2 ^ 59
def prefixEnd_1796206 : Nat := 4983230072969 + 3 ^ 40 * 1796206 * 2
def baseEnd_1796206 : Nat := 409918681106624253095291

theorem tailTrace_1796206 : CollatzResearch.WordTrace tailWord_1796206 prefixEnd_1796206 409918681106624253095291 := by
  unfold tailWord_1796206
  simp only [CollatzResearch.WordTrace]
  refine ⟨8189126866332488050862059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43675343287106602937930981 8189126866332488050862059)
  ·
    refine ⟨12283690299498732076293089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8189126866332488050862059 12283690299498732076293089)
    ·
      refine ⟨9212767724624049057219817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12283690299498732076293089 9212767724624049057219817)
      ·
        refine ⟨6909575793468036792914863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9212767724624049057219817 6909575793468036792914863)
        ·
          refine ⟨10364363690202055189372295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6909575793468036792914863 10364363690202055189372295)
          ·
            refine ⟨15546545535303082784058443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10364363690202055189372295 15546545535303082784058443)
            ·
              refine ⟨23319818302954624176087665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15546545535303082784058443 23319818302954624176087665)
              ·
                refine ⟨17489863727215968132065749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23319818302954624176087665 17489863727215968132065749)
                ·
                  refine ⟨409918681106624253095291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17489863727215968132065749 409918681106624253095291)
                  ·
                    rfl

theorem cell21_1796206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 2, 7].length) (baseStart_1796206 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1796206 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1796206 prefixEnd_1796206 := by exact prefixLift 1796206
  have htrace : WordTrace (prefixWord ++ tailWord_1796206) baseStart_1796206 baseEnd_1796206 := by
    simpa [prefixWord, tailWord_1796206, baseEnd_1796206] using wordTrace_append hprefix tailTrace_1796206
  have hstable : (prefixWord ++ tailWord_1796206).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1796206).length < 2 ^ (prefixWord ++ tailWord_1796206).sum := by decide
  have hdescent : baseEnd_1796206 < baseStart_1796206 := by decide
  rcases family_descends (prefixWord ++ tailWord_1796206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1796282 : List Nat := [3, 1, 1, 1, 2, 2, 5, 1, 5]
def baseStart_1796282 : Nat := 118140960795 + 1796282 * 2 ^ 59
def prefixEnd_1796282 : Nat := 4983230072969 + 3 ^ 40 * 1796282 * 2
def baseEnd_1796282 : Nat := 409936025342065009828469

theorem tailTrace_1796282 : CollatzResearch.WordTrace tailWord_1796282 prefixEnd_1796282 409936025342065009828469 := by
  unfold tailWord_1796282
  simp only [CollatzResearch.WordTrace]
  refine ⟨16378946719596142346665775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43677191252256379591108733 16378946719596142346665775)
  ·
    refine ⟨24568420079394213519998663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16378946719596142346665775 24568420079394213519998663)
    ·
      refine ⟨36852630119091320279997995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24568420079394213519998663 36852630119091320279997995)
      ·
        refine ⟨55278945178636980419996993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36852630119091320279997995 55278945178636980419996993)
        ·
          refine ⟨41459208883977735314997745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55278945178636980419996993 41459208883977735314997745)
          ·
            refine ⟨31094406662983301486248309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41459208883977735314997745 31094406662983301486248309)
            ·
              refine ⟨2915100624654684514335779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31094406662983301486248309 2915100624654684514335779)
              ·
                refine ⟨4372650936982026771503669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2915100624654684514335779 4372650936982026771503669)
                ·
                  refine ⟨409936025342065009828469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4372650936982026771503669 409936025342065009828469)
                  ·
                    rfl

theorem cell21_1796282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 1, 5].length) (baseStart_1796282 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1796282 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1796282 prefixEnd_1796282 := by exact prefixLift 1796282
  have htrace : WordTrace (prefixWord ++ tailWord_1796282) baseStart_1796282 baseEnd_1796282 := by
    simpa [prefixWord, tailWord_1796282, baseEnd_1796282] using wordTrace_append hprefix tailTrace_1796282
  have hstable : (prefixWord ++ tailWord_1796282).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1796282).length < 2 ^ (prefixWord ++ tailWord_1796282).sum := by decide
  have hdescent : baseEnd_1796282 < baseStart_1796282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1796282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1796327 : List Nat := [1, 1, 5, 3, 1, 10]
def baseStart_1796327 : Nat := 118140960795 + 1796327 * 2 ^ 59
def prefixEnd_1796327 : Nat := 4983230072969 + 3 ^ 40 * 1796327 * 2
def baseEnd_1796327 : Nat := 15183196109450182651051

theorem tailTrace_1796327 : CollatzResearch.WordTrace tailWord_1796327 prefixEnd_1796327 15183196109450182651051 := by
  unfold tailWord_1796327
  simp only [CollatzResearch.WordTrace]
  refine ⟨65517428163221542072051235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43678285442147694714700823 65517428163221542072051235)
  ·
    refine ⟨98276142244832313108076853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65517428163221542072051235 98276142244832313108076853)
    ·
      refine ⟨9213388335453029353882205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 98276142244832313108076853 9213388335453029353882205)
      ·
        refine ⟨3455020625794886007705827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9213388335453029353882205 3455020625794886007705827)
        ·
          refine ⟨5182530938692329011558741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3455020625794886007705827 5182530938692329011558741)
          ·
            refine ⟨15183196109450182651051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5182530938692329011558741 15183196109450182651051)
            ·
              rfl

theorem cell21_1796327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 10].length) (baseStart_1796327 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1796327 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1796327 prefixEnd_1796327 := by exact prefixLift 1796327
  have htrace : WordTrace (prefixWord ++ tailWord_1796327) baseStart_1796327 baseEnd_1796327 := by
    simpa [prefixWord, tailWord_1796327, baseEnd_1796327] using wordTrace_append hprefix tailTrace_1796327
  have hstable : (prefixWord ++ tailWord_1796327).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1796327).length < 2 ^ (prefixWord ++ tailWord_1796327).sum := by decide
  have hdescent : baseEnd_1796327 < baseStart_1796327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1796327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1796375 : List Nat := [1, 1, 3, 4, 1, 2, 1, 5, 3]
def baseStart_1796375 : Nat := 118140960795 + 1796375 * 2 ^ 59
def prefixEnd_1796375 : Nat := 4983230072969 + 3 ^ 40 * 1796375 * 2
def baseEnd_1796375 : Nat := 409957249209117514778279

theorem tailTrace_1796375 : CollatzResearch.WordTrace tailWord_1796375 prefixEnd_1796375 409957249209117514778279 := by
  unfold tailWord_1796375
  simp only [CollatzResearch.WordTrace]
  refine ⟨65519178867047646269798579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43679452578031764179865719 65519178867047646269798579)
  ·
    refine ⟨98278768300571469404697869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65519178867047646269798579 98278768300571469404697869)
    ·
      refine ⟨36854538112714301026761701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98278768300571469404697869 36854538112714301026761701)
      ·
        refine ⟨6910225896133931442517819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36854538112714301026761701 6910225896133931442517819)
        ·
          refine ⟨10365338844200897163776729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6910225896133931442517819 10365338844200897163776729)
          ·
            refine ⟨7774004133150672872832547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10365338844200897163776729 7774004133150672872832547)
            ·
              refine ⟨11661006199726009309248821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7774004133150672872832547 11661006199726009309248821)
              ·
                refine ⟨1093219331224313372742077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11661006199726009309248821 1093219331224313372742077)
                ·
                  refine ⟨409957249209117514778279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1093219331224313372742077 409957249209117514778279)
                  ·
                    rfl

theorem cell21_1796375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 5, 3].length) (baseStart_1796375 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1796375 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1796375 prefixEnd_1796375 := by exact prefixLift 1796375
  have htrace : WordTrace (prefixWord ++ tailWord_1796375) baseStart_1796375 baseEnd_1796375 := by
    simpa [prefixWord, tailWord_1796375, baseEnd_1796375] using wordTrace_append hprefix tailTrace_1796375
  have hstable : (prefixWord ++ tailWord_1796375).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1796375).length < 2 ^ (prefixWord ++ tailWord_1796375).sum := by decide
  have hdescent : baseEnd_1796375 < baseStart_1796375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1796375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1796389 : List Nat := [1, 3, 1, 2, 5, 1, 1, 1, 6]
def baseStart_1796389 : Nat := 118140960795 + 1796389 * 2 ^ 59
def prefixEnd_1796389 : Nat := 4983230072969 + 3 ^ 40 * 1796389 * 2
def baseEnd_1796389 : Nat := 409960444199856601544917

theorem tailTrace_1796389 : CollatzResearch.WordTrace tailWord_1796389 prefixEnd_1796389 409960444199856601544917 := by
  unfold tailWord_1796389
  simp only [CollatzResearch.WordTrace]
  refine ⟨65519689488996926660808221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43679792992664617773872147 65519689488996926660808221)
  ·
    refine ⟨24569883558373847497803083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65519689488996926660808221 24569883558373847497803083)
    ·
      refine ⟨36854825337560771246704625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24569883558373847497803083 36854825337560771246704625)
      ·
        refine ⟨27641119003170578435028469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36854825337560771246704625 27641119003170578435028469)
        ·
          refine ⟨2591354906547241728283919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27641119003170578435028469 2591354906547241728283919)
          ·
            refine ⟨3887032359820862592425879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2591354906547241728283919 3887032359820862592425879)
            ·
              refine ⟨5830548539731293888638819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3887032359820862592425879 5830548539731293888638819)
              ·
                refine ⟨8745822809596940832958229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5830548539731293888638819 8745822809596940832958229)
                ·
                  refine ⟨409960444199856601544917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8745822809596940832958229 409960444199856601544917)
                  ·
                    rfl

theorem cell21_1796389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 1, 6].length) (baseStart_1796389 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1796389 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1796389 prefixEnd_1796389 := by exact prefixLift 1796389
  have htrace : WordTrace (prefixWord ++ tailWord_1796389) baseStart_1796389 baseEnd_1796389 := by
    simpa [prefixWord, tailWord_1796389, baseEnd_1796389] using wordTrace_append hprefix tailTrace_1796389
  have hstable : (prefixWord ++ tailWord_1796389).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1796389).length < 2 ^ (prefixWord ++ tailWord_1796389).sum := by decide
  have hdescent : baseEnd_1796389 < baseStart_1796389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1796389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1796513 : List Nat := [1, 2, 3, 5, 1, 2, 1, 6]
def baseStart_1796513 : Nat := 118140960795 + 1796513 * 2 ^ 59
def prefixEnd_1796513 : Nat := 4983230072969 + 3 ^ 40 * 1796513 * 2
def baseEnd_1796513 : Nat := 136662914229753313825999

theorem tailTrace_1796513 : CollatzResearch.WordTrace tailWord_1796513 prefixEnd_1796513 136662914229753313825999 := by
  unfold tailWord_1796513
  simp only [CollatzResearch.WordTrace]
  refine ⟨65524212140547695838322193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43682808093698463892214795 65524212140547695838322193)
  ·
    refine ⟨49143159105410771878741645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65524212140547695838322193 49143159105410771878741645)
    ·
      refine ⟨18428684664529039454528117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49143159105410771878741645 18428684664529039454528117)
      ·
        refine ⟨1727689187299597448862011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18428684664529039454528117 1727689187299597448862011)
        ·
          refine ⟨2591533780949396173293017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1727689187299597448862011 2591533780949396173293017)
          ·
            refine ⟨1943650335712047129969763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2591533780949396173293017 1943650335712047129969763)
            ·
              refine ⟨2915475503568070694954645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1943650335712047129969763 2915475503568070694954645)
              ·
                refine ⟨136662914229753313825999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2915475503568070694954645 136662914229753313825999)
                ·
                  rfl

theorem cell21_1796513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 6].length) (baseStart_1796513 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1796513 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1796513 prefixEnd_1796513 := by exact prefixLift 1796513
  have htrace : WordTrace (prefixWord ++ tailWord_1796513) baseStart_1796513 baseEnd_1796513 := by
    simpa [prefixWord, tailWord_1796513, baseEnd_1796513] using wordTrace_append hprefix tailTrace_1796513
  have hstable : (prefixWord ++ tailWord_1796513).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1796513).length < 2 ^ (prefixWord ++ tailWord_1796513).sum := by decide
  have hdescent : baseEnd_1796513 < baseStart_1796513 := by decide
  rcases family_descends (prefixWord ++ tailWord_1796513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1796538 : List Nat := [3, 1, 1, 1, 2, 1, 1, 11]
def baseStart_1796538 : Nat := 118140960795 + 1796538 * 2 ^ 59
def prefixEnd_1796538 : Nat := 4983230072969 + 3 ^ 40 * 1796538 * 2
def baseEnd_1796538 : Nat := 136664816009955151187093

theorem tailTrace_1796538 : CollatzResearch.WordTrace tailWord_1796538 prefixEnd_1796538 136664816009955151187093 := by
  unfold tailWord_1796538
  simp only [CollatzResearch.WordTrace]
  refine ⟨16381280991364281276995567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43683415976971416738654845 16381280991364281276995567)
  ·
    refine ⟨24571921487046421915493351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16381280991364281276995567 24571921487046421915493351)
    ·
      refine ⟨36857882230569632873240027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24571921487046421915493351 36857882230569632873240027)
      ·
        refine ⟨55286823345854449309860041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36857882230569632873240027 55286823345854449309860041)
        ·
          refine ⟨41465117509390836982395031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55286823345854449309860041 41465117509390836982395031)
          ·
            refine ⟨62197676264086255473592547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41465117509390836982395031 62197676264086255473592547)
            ·
              refine ⟨93296514396129383210388821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62197676264086255473592547 93296514396129383210388821)
              ·
                refine ⟨136664816009955151187093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 93296514396129383210388821 136664816009955151187093)
                ·
                  rfl

theorem cell21_1796538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 11].length) (baseStart_1796538 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1796538 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1796538 prefixEnd_1796538 := by exact prefixLift 1796538
  have htrace : WordTrace (prefixWord ++ tailWord_1796538) baseStart_1796538 baseEnd_1796538 := by
    simpa [prefixWord, tailWord_1796538, baseEnd_1796538] using wordTrace_append hprefix tailTrace_1796538
  have hstable : (prefixWord ++ tailWord_1796538).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1796538).length < 2 ^ (prefixWord ++ tailWord_1796538).sum := by decide
  have hdescent : baseEnd_1796538 < baseStart_1796538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1796538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1796586 : List Nat := [3, 1, 3, 1, 3, 1, 2, 2, 5]
def baseStart_1796586 : Nat := 118140960795 + 1796586 * 2 ^ 59
def prefixEnd_1796586 : Nat := 4983230072969 + 3 ^ 40 * 1796586 * 2
def baseEnd_1796586 : Nat := 410005402283828036761181

theorem tailTrace_1796586 : CollatzResearch.WordTrace tailWord_1796586 prefixEnd_1796586 410005402283828036761181 := by
  unfold tailWord_1796586
  simp only [CollatzResearch.WordTrace]
  refine ⟨16381718667320807326432403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43684583112855486203819741 16381718667320807326432403)
  ·
    refine ⟨24572578000981210989648605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16381718667320807326432403 24572578000981210989648605)
    ·
      refine ⟨9214716750367954121118227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24572578000981210989648605 9214716750367954121118227)
      ·
        refine ⟨13822075125551931181677341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9214716750367954121118227 13822075125551931181677341)
        ·
          refine ⟨5183278172081974193129003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13822075125551931181677341 5183278172081974193129003)
          ·
            refine ⟨7774917258122961289693505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5183278172081974193129003 7774917258122961289693505)
            ·
              refine ⟨5831187943592220967270129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7774917258122961289693505 5831187943592220967270129)
              ·
                refine ⟨4373390957694165725452597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5831187943592220967270129 4373390957694165725452597)
                ·
                  refine ⟨410005402283828036761181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4373390957694165725452597 410005402283828036761181)
                  ·
                    rfl

theorem cell21_1796586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 2, 5].length) (baseStart_1796586 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1796586 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1796586 prefixEnd_1796586 := by exact prefixLift 1796586
  have htrace : WordTrace (prefixWord ++ tailWord_1796586) baseStart_1796586 baseEnd_1796586 := by
    simpa [prefixWord, tailWord_1796586, baseEnd_1796586] using wordTrace_append hprefix tailTrace_1796586
  have hstable : (prefixWord ++ tailWord_1796586).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1796586).length < 2 ^ (prefixWord ++ tailWord_1796586).sum := by decide
  have hdescent : baseEnd_1796586 < baseStart_1796586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1796586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1796589 : List Nat := [1, 5, 1, 3, 1, 3, 2, 5]
def baseStart_1796589 : Nat := 118140960795 + 1796589 * 2 ^ 59
def prefixEnd_1796589 : Nat := 4983230072969 + 3 ^ 40 * 1796589 * 2
def baseEnd_1796589 : Nat := 136668695641566899403725

theorem tailTrace_1796589 : CollatzResearch.WordTrace tailWord_1796589 prefixEnd_1796589 136668695641566899403725 := by
  unfold tailWord_1796589
  simp only [CollatzResearch.WordTrace]
  refine ⟨65526984088272360818088821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43684656058848240545392547 65526984088272360818088821)
  ·
    refine ⟨6143154758275533826695827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 65526984088272360818088821 6143154758275533826695827)
    ·
      refine ⟨9214732137413300740043741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6143154758275533826695827 9214732137413300740043741)
      ·
        refine ⟨3455524551529987777516403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9214732137413300740043741 3455524551529987777516403)
        ·
          refine ⟨5183286827294981666274605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3455524551529987777516403 5183286827294981666274605)
          ·
            refine ⟨1943732560235618124852977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5183286827294981666274605 1943732560235618124852977)
            ·
              refine ⟨1457799420176713593639733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1943732560235618124852977 1457799420176713593639733)
              ·
                refine ⟨136668695641566899403725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1457799420176713593639733 136668695641566899403725)
                ·
                  rfl

theorem cell21_1796589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 2, 5].length) (baseStart_1796589 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1796589 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1796589 prefixEnd_1796589 := by exact prefixLift 1796589
  have htrace : WordTrace (prefixWord ++ tailWord_1796589) baseStart_1796589 baseEnd_1796589 := by
    simpa [prefixWord, tailWord_1796589, baseEnd_1796589] using wordTrace_append hprefix tailTrace_1796589
  have hstable : (prefixWord ++ tailWord_1796589).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1796589).length < 2 ^ (prefixWord ++ tailWord_1796589).sum := by decide
  have hdescent : baseEnd_1796589 < baseStart_1796589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1796589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1796620 : List Nat := [2, 2, 1, 2, 4, 2, 3, 2, 3]
def baseStart_1796620 : Nat := 118140960795 + 1796620 * 2 ^ 59
def prefixEnd_1796620 : Nat := 4983230072969 + 3 ^ 40 * 1796620 * 2
def baseEnd_1796620 : Nat := 410013161547051533194445

theorem tailTrace_1796620 : CollatzResearch.WordTrace tailWord_1796620 prefixEnd_1796620 410013161547051533194445 := by
  unfold tailWord_1796620
  simp only [CollatzResearch.WordTrace]
  refine ⟨32764057375580026556233657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43685409834106702074978209 32764057375580026556233657)
  ·
    refine ⟨24573043031685019917175243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32764057375580026556233657 24573043031685019917175243)
    ·
      refine ⟨36859564547527529875762865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24573043031685019917175243 36859564547527529875762865)
      ·
        refine ⟨27644673410645647406822149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36859564547527529875762865 27644673410645647406822149)
        ·
          refine ⟨5183376264496058888779153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27644673410645647406822149 5183376264496058888779153)
          ·
            refine ⟨3887532198372044166584365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5183376264496058888779153 3887532198372044166584365)
            ·
              refine ⟨1457824574389516562469137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3887532198372044166584365 1457824574389516562469137)
              ·
                refine ⟨1093368430792137421851853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1457824574389516562469137 1093368430792137421851853)
                ·
                  refine ⟨410013161547051533194445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1093368430792137421851853 410013161547051533194445)
                  ·
                    rfl

theorem cell21_1796620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 3, 2, 3].length) (baseStart_1796620 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1796620 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1796620 prefixEnd_1796620 := by exact prefixLift 1796620
  have htrace : WordTrace (prefixWord ++ tailWord_1796620) baseStart_1796620 baseEnd_1796620 := by
    simpa [prefixWord, tailWord_1796620, baseEnd_1796620] using wordTrace_append hprefix tailTrace_1796620
  have hstable : (prefixWord ++ tailWord_1796620).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1796620).length < 2 ^ (prefixWord ++ tailWord_1796620).sum := by decide
  have hdescent : baseEnd_1796620 < baseStart_1796620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1796620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1796645 : List Nat := [1, 3, 1, 2, 2, 1, 2, 4, 5]
def baseStart_1796645 : Nat := 118140960795 + 1796645 * 2 ^ 59
def prefixEnd_1796645 : Nat := 4983230072969 + 3 ^ 40 * 1796645 * 2
def baseEnd_1796645 : Nat := 410018866887657045277727

theorem tailTrace_1796645 : CollatzResearch.WordTrace tailWord_1796645 prefixEnd_1796645 410018866887657045277727 := by
  unfold tailWord_1796645
  simp only [CollatzResearch.WordTrace]
  refine ⟨65529026576069482382127389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43686017717379654921418259 65529026576069482382127389)
  ·
    refine ⟨24573384966026055893297771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65529026576069482382127389 24573384966026055893297771)
    ·
      refine ⟨36860077449039083839946657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24573384966026055893297771 36860077449039083839946657)
      ·
        refine ⟨27645058086779312879959993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36860077449039083839946657 27645058086779312879959993)
        ·
          refine ⟨20733793565084484659969995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27645058086779312879959993 20733793565084484659969995)
          ·
            refine ⟨31100690347626726989954993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20733793565084484659969995 31100690347626726989954993)
            ·
              refine ⟨23325517760720045242466245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31100690347626726989954993 23325517760720045242466245)
              ·
                refine ⟨4373534580135008482962421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23325517760720045242466245 4373534580135008482962421)
                ·
                  refine ⟨410018866887657045277727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4373534580135008482962421 410018866887657045277727)
                  ·
                    rfl

theorem cell21_1796645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 4, 5].length) (baseStart_1796645 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1796645 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1796645 prefixEnd_1796645 := by exact prefixLift 1796645
  have htrace : WordTrace (prefixWord ++ tailWord_1796645) baseStart_1796645 baseEnd_1796645 := by
    simpa [prefixWord, tailWord_1796645, baseEnd_1796645] using wordTrace_append hprefix tailTrace_1796645
  have hstable : (prefixWord ++ tailWord_1796645).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1796645).length < 2 ^ (prefixWord ++ tailWord_1796645).sum := by decide
  have hdescent : baseEnd_1796645 < baseStart_1796645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1796645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1796679 : List Nat := [1, 1, 4, 1, 4, 2, 1, 4, 3]
def baseStart_1796679 : Nat := 118140960795 + 1796679 * 2 ^ 59
def prefixEnd_1796679 : Nat := 4983230072969 + 3 ^ 40 * 1796679 * 2
def baseEnd_1796679 : Nat := 410026626150880541710991

theorem tailTrace_1796679 : CollatzResearch.WordTrace tailWord_1796679 prefixEnd_1796679 410026626150880541710991 := by
  unfold tailWord_1796679
  simp only [CollatzResearch.WordTrace]
  refine ⟨65530266657946306188865091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43686844438630870792576727 65530266657946306188865091)
  ·
    refine ⟨98295399986919459283297637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65530266657946306188865091 98295399986919459283297637)
    ·
      refine ⟨18430387497547398615618307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98295399986919459283297637 18430387497547398615618307)
      ·
        refine ⟨27645581246321097923427461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18430387497547398615618307 27645581246321097923427461)
        ·
          refine ⟨5183546483685205860642649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27645581246321097923427461 5183546483685205860642649)
          ·
            refine ⟨3887659862763904395481987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5183546483685205860642649 3887659862763904395481987)
            ·
              refine ⟨5831489794145856593222981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3887659862763904395481987 5831489794145856593222981)
              ·
                refine ⟨1093404336402348111229309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5831489794145856593222981 1093404336402348111229309)
                ·
                  refine ⟨410026626150880541710991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1093404336402348111229309 410026626150880541710991)
                  ·
                    rfl

theorem cell21_1796679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 4, 3].length) (baseStart_1796679 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1796679 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1796679 prefixEnd_1796679 := by exact prefixLift 1796679
  have htrace : WordTrace (prefixWord ++ tailWord_1796679) baseStart_1796679 baseEnd_1796679 := by
    simpa [prefixWord, tailWord_1796679, baseEnd_1796679] using wordTrace_append hprefix tailTrace_1796679
  have hstable : (prefixWord ++ tailWord_1796679).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1796679).length < 2 ^ (prefixWord ++ tailWord_1796679).sum := by decide
  have hdescent : baseEnd_1796679 < baseStart_1796679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1796679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1796707 : List Nat := [1, 1, 1, 5, 1, 2, 5, 5]
def baseStart_1796707 : Nat := 118140960795 + 1796707 * 2 ^ 59
def prefixEnd_1796707 : Nat := 4983230072969 + 3 ^ 40 * 1796707 * 2
def baseEnd_1796707 : Nat := 136677672044119571748089

theorem tailTrace_1796707 : CollatzResearch.WordTrace tailWord_1796707 prefixEnd_1796707 136677672044119571748089 := by
  unfold tailWord_1796707
  simp only [CollatzResearch.WordTrace]
  refine ⟨65531287901844866970884375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43687525267896577980589583 65531287901844866970884375)
  ·
    refine ⟨98296931852767300456326563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65531287901844866970884375 98296931852767300456326563)
    ·
      refine ⟨147445397779150950684489845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98296931852767300456326563 147445397779150950684489845)
      ·
        refine ⟨13823006041795401626670923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 147445397779150950684489845 13823006041795401626670923)
        ·
          refine ⟨20734509062693102440006385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13823006041795401626670923 20734509062693102440006385)
          ·
            refine ⟨15550881797019826830004789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20734509062693102440006385 15550881797019826830004789)
            ·
              refine ⟨1457895168470608765312949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15550881797019826830004789 1457895168470608765312949)
              ·
                refine ⟨136677672044119571748089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1457895168470608765312949 136677672044119571748089)
                ·
                  rfl

theorem cell21_1796707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 5, 5].length) (baseStart_1796707 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1796707 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1796707 prefixEnd_1796707 := by exact prefixLift 1796707
  have htrace : WordTrace (prefixWord ++ tailWord_1796707) baseStart_1796707 baseEnd_1796707 := by
    simpa [prefixWord, tailWord_1796707, baseEnd_1796707] using wordTrace_append hprefix tailTrace_1796707
  have hstable : (prefixWord ++ tailWord_1796707).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1796707).length < 2 ^ (prefixWord ++ tailWord_1796707).sum := by decide
  have hdescent : baseEnd_1796707 < baseStart_1796707 := by decide
  rcases family_descends (prefixWord ++ tailWord_1796707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1796845 : List Nat := [1, 5, 1, 2, 1, 1, 4, 2, 4]
def baseStart_1796845 : Nat := 118140960795 + 1796845 * 2 ^ 59
def prefixEnd_1796845 : Nat := 4983230072969 + 3 ^ 40 * 1796845 * 2
def baseEnd_1796845 : Nat := 410064509612501141943985

theorem tailTrace_1796845 : CollatzResearch.WordTrace tailWord_1796845 prefixEnd_1796845 410064509612501141943985 := by
  unfold tailWord_1796845
  simp only [CollatzResearch.WordTrace]
  refine ⟨65536321175344916539407989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43690880783563277692938659 65536321175344916539407989)
  ·
    refine ⟨6144030110188585925569499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 65536321175344916539407989 6144030110188585925569499)
    ·
      refine ⟨9216045165282878888354249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6144030110188585925569499 9216045165282878888354249)
      ·
        refine ⟨6912033873962159166265687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9216045165282878888354249 6912033873962159166265687)
        ·
          refine ⟨10368050810943238749398531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6912033873962159166265687 10368050810943238749398531)
          ·
            refine ⟨15552076216414858124097797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10368050810943238749398531 15552076216414858124097797)
            ·
              refine ⟨2916014290577785898268337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15552076216414858124097797 2916014290577785898268337)
              ·
                refine ⟨2187010717933339423701253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2916014290577785898268337 2187010717933339423701253)
                ·
                  refine ⟨410064509612501141943985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2187010717933339423701253 410064509612501141943985)
                  ·
                    rfl

theorem cell21_1796845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 2, 4].length) (baseStart_1796845 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1796845 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1796845 prefixEnd_1796845 := by exact prefixLift 1796845
  have htrace : WordTrace (prefixWord ++ tailWord_1796845) baseStart_1796845 baseEnd_1796845 := by
    simpa [prefixWord, tailWord_1796845, baseEnd_1796845] using wordTrace_append hprefix tailTrace_1796845
  have hstable : (prefixWord ++ tailWord_1796845).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1796845).length < 2 ^ (prefixWord ++ tailWord_1796845).sum := by decide
  have hdescent : baseEnd_1796845 < baseStart_1796845 := by decide
  rcases family_descends (prefixWord ++ tailWord_1796845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1796904 : List Nat := [2, 1, 5, 1, 1, 1, 3, 1, 6]
def baseStart_1796904 : Nat := 118140960795 + 1796904 * 2 ^ 59
def prefixEnd_1796904 : Nat := 4983230072969 + 3 ^ 40 * 1796904 * 2
def baseEnd_1796904 : Nat := 410077974216330150460531

theorem tailTrace_1796904 : CollatzResearch.WordTrace tailWord_1796904 prefixEnd_1796904 410077974216330150460531 := by
  unfold tailWord_1796904
  simp only [CollatzResearch.WordTrace]
  refine ⟨32769236541065584807902883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43692315388087446410537177 32769236541065584807902883)
  ·
    refine ⟨49153854811598377211854325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32769236541065584807902883 49153854811598377211854325)
    ·
      refine ⟨4608173888587347863611343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 49153854811598377211854325 4608173888587347863611343)
      ·
        refine ⟨6912260832881021795417015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4608173888587347863611343 6912260832881021795417015)
        ·
          refine ⟨10368391249321532693125523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6912260832881021795417015 10368391249321532693125523)
          ·
            refine ⟨15552586873982299039688285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10368391249321532693125523 15552586873982299039688285)
            ·
              refine ⟨5832220077743362139883107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15552586873982299039688285 5832220077743362139883107)
              ·
                refine ⟨8748330116615043209824661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5832220077743362139883107 8748330116615043209824661)
                ·
                  refine ⟨410077974216330150460531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8748330116615043209824661 410077974216330150460531)
                  ·
                    rfl

theorem cell21_1796904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 1, 6].length) (baseStart_1796904 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1796904 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1796904 prefixEnd_1796904 := by exact prefixLift 1796904
  have htrace : WordTrace (prefixWord ++ tailWord_1796904) baseStart_1796904 baseEnd_1796904 := by
    simpa [prefixWord, tailWord_1796904, baseEnd_1796904] using wordTrace_append hprefix tailTrace_1796904
  have hstable : (prefixWord ++ tailWord_1796904).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1796904).length < 2 ^ (prefixWord ++ tailWord_1796904).sum := by decide
  have hdescent : baseEnd_1796904 < baseStart_1796904 := by decide
  rcases family_descends (prefixWord ++ tailWord_1796904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1796941 : List Nat := [1, 6, 1, 2, 2, 2, 1, 3, 3]
def baseStart_1796941 : Nat := 118140960795 + 1796941 * 2 ^ 59
def prefixEnd_1796941 : Nat := 4983230072969 + 3 ^ 40 * 1796941 * 2
def baseEnd_1796941 : Nat := 410086418120426308343789

theorem tailTrace_1796941 : CollatzResearch.WordTrace tailWord_1796941 prefixEnd_1796941 410086418120426308343789 := by
  unfold tailWord_1796941
  simp only [CollatzResearch.WordTrace]
  refine ⟨65539822582997124934902677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43693215055331416623268451 65539822582997124934902677)
  ·
    refine ⟨3072179183577990231323563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 65539822582997124934902677 3072179183577990231323563)
    ·
      refine ⟨4608268775366985346985345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3072179183577990231323563 4608268775366985346985345)
      ·
        refine ⟨3456201581525239010239009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4608268775366985346985345 3456201581525239010239009)
        ·
          refine ⟨2592151186143929257679257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3456201581525239010239009 2592151186143929257679257)
          ·
            refine ⟨1944113389607946943259443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2592151186143929257679257 1944113389607946943259443)
            ·
              refine ⟨2916170084411920414889165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1944113389607946943259443 2916170084411920414889165)
              ·
                refine ⟨1093563781654470155583437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2916170084411920414889165 1093563781654470155583437)
                ·
                  refine ⟨410086418120426308343789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1093563781654470155583437 410086418120426308343789)
                  ·
                    rfl

theorem cell21_1796941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 3, 3].length) (baseStart_1796941 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1796941 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1796941 prefixEnd_1796941 := by exact prefixLift 1796941
  have htrace : WordTrace (prefixWord ++ tailWord_1796941) baseStart_1796941 baseEnd_1796941 := by
    simpa [prefixWord, tailWord_1796941, baseEnd_1796941] using wordTrace_append hprefix tailTrace_1796941
  have hstable : (prefixWord ++ tailWord_1796941).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1796941).length < 2 ^ (prefixWord ++ tailWord_1796941).sum := by decide
  have hdescent : baseEnd_1796941 < baseStart_1796941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1796941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797062 : List Nat := [6, 1, 3, 1, 1, 1, 8]
def baseStart_1797062 : Nat := 118140960795 + 1797062 * 2 ^ 59
def prefixEnd_1797062 : Nat := 4983230072969 + 3 ^ 40 * 1797062 * 2
def baseEnd_1797062 : Nat := 45568225774328554091875

theorem tailTrace_1797062 : CollatzResearch.WordTrace tailWord_1797062 prefixEnd_1797062 45568225774328554091875 := by
  unfold tailWord_1797062
  simp only [CollatzResearch.WordTrace]
  refine ⟨2048257369236211331251795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 43696157210372508400038293 2048257369236211331251795)
  ·
    refine ⟨3072386053854316996877693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2048257369236211331251795 3072386053854316996877693)
    ·
      refine ⟨1152144770195368873829135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3072386053854316996877693 1152144770195368873829135)
      ·
        refine ⟨1728217155293053310743703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1152144770195368873829135 1728217155293053310743703)
        ·
          refine ⟨2592325732939579966115555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1728217155293053310743703 2592325732939579966115555)
          ·
            refine ⟨3888488599409369949173333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2592325732939579966115555 3888488599409369949173333)
            ·
              refine ⟨45568225774328554091875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3888488599409369949173333 45568225774328554091875)
              ·
                rfl

theorem cell21_1797062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 8].length) (baseStart_1797062 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1797062 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1797062 prefixEnd_1797062 := by exact prefixLift 1797062
  have htrace : WordTrace (prefixWord ++ tailWord_1797062) baseStart_1797062 baseEnd_1797062 := by
    simpa [prefixWord, tailWord_1797062, baseEnd_1797062] using wordTrace_append hprefix tailTrace_1797062
  have hstable : (prefixWord ++ tailWord_1797062).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797062).length < 2 ^ (prefixWord ++ tailWord_1797062).sum := by decide
  have hdescent : baseEnd_1797062 < baseStart_1797062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797070 : List Nat := [4, 1, 1, 1, 2, 4, 8]
def baseStart_1797070 : Nat := 118140960795 + 1797070 * 2 ^ 59
def prefixEnd_1797070 : Nat := 4983230072969 + 3 ^ 40 * 1797070 * 2
def baseEnd_1797070 : Nat := 45568428630883416743725

theorem tailTrace_1797070 : CollatzResearch.WordTrace tailWord_1797070 prefixEnd_1797070 45568428630883416743725 := by
  unfold tailWord_1797070
  simp only [CollatzResearch.WordTrace]
  refine ⟨8193065949941222495793583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43696351733019853310899109 8193065949941222495793583)
  ·
    refine ⟨12289598924911833743690375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8193065949941222495793583 12289598924911833743690375)
    ·
      refine ⟨18434398387367750615535563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12289598924911833743690375 18434398387367750615535563)
      ·
        refine ⟨27651597581051625923303345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18434398387367750615535563 27651597581051625923303345)
        ·
          refine ⟨20738698185788719442477509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27651597581051625923303345 20738698185788719442477509)
          ·
            refine ⟨3888505909835384895464533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20738698185788719442477509 3888505909835384895464533)
            ·
              refine ⟨45568428630883416743725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3888505909835384895464533 45568428630883416743725)
              ·
                rfl

theorem cell21_1797070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 8].length) (baseStart_1797070 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1797070 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1797070 prefixEnd_1797070 := by exact prefixLift 1797070
  have htrace : WordTrace (prefixWord ++ tailWord_1797070) baseStart_1797070 baseEnd_1797070 := by
    simpa [prefixWord, tailWord_1797070, baseEnd_1797070] using wordTrace_append hprefix tailTrace_1797070
  have hstable : (prefixWord ++ tailWord_1797070).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797070).length < 2 ^ (prefixWord ++ tailWord_1797070).sum := by decide
  have hdescent : baseEnd_1797070 < baseStart_1797070 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797146 : List Nat := [3, 1, 1, 3, 1, 2, 4, 6]
def baseStart_1797146 : Nat := 118140960795 + 1797146 * 2 ^ 59
def prefixEnd_1797146 : Nat := 4983230072969 + 3 ^ 40 * 1797146 * 2
def baseEnd_1797146 : Nat := 136711067304463835808901

theorem tailTrace_1797146 : CollatzResearch.WordTrace tailWord_1797146 prefixEnd_1797146 136711067304463835808901 := by
  unfold tailWord_1797146
  simp only [CollatzResearch.WordTrace]
  refine ⟨16386824886813611236528823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43698199698169629964076861 16386824886813611236528823)
  ·
    refine ⟨24580237330220416854793235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16386824886813611236528823 24580237330220416854793235)
    ·
      refine ⟨36870355995330625282189853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24580237330220416854793235 36870355995330625282189853)
      ·
        refine ⟨13826383498248984480821195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36870355995330625282189853 13826383498248984480821195)
        ·
          refine ⟨20739575247373476721231793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13826383498248984480821195 20739575247373476721231793)
          ·
            refine ⟨15554681435530107540923845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20739575247373476721231793 15554681435530107540923845)
            ·
              refine ⟨2916502769161895163923221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15554681435530107540923845 2916502769161895163923221)
              ·
                refine ⟨136711067304463835808901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2916502769161895163923221 136711067304463835808901)
                ·
                  rfl

theorem cell21_1797146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 6].length) (baseStart_1797146 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1797146 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1797146 prefixEnd_1797146 := by exact prefixLift 1797146
  have htrace : WordTrace (prefixWord ++ tailWord_1797146) baseStart_1797146 baseEnd_1797146 := by
    simpa [prefixWord, tailWord_1797146, baseEnd_1797146] using wordTrace_append hprefix tailTrace_1797146
  have hstable : (prefixWord ++ tailWord_1797146).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797146).length < 2 ^ (prefixWord ++ tailWord_1797146).sum := by decide
  have hdescent : baseEnd_1797146 < baseStart_1797146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797149 : List Nat := [1, 4, 2, 2, 3, 1, 1, 3, 4]
def baseStart_1797149 : Nat := 118140960795 + 1797149 * 2 ^ 59
def prefixEnd_1797149 : Nat := 4983230072969 + 3 ^ 40 * 1797149 * 2
def baseEnd_1797149 : Nat := 410133886554264168876697

theorem tailTrace_1797149 : CollatzResearch.WordTrace tailWord_1797149 prefixEnd_1797149 410133886554264168876697 := by
  unfold tailWord_1797149
  simp only [CollatzResearch.WordTrace]
  refine ⟨65547408966243576458474501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43698272644162384305649667 65547408966243576458474501)
  ·
    refine ⟨12290139181170670585963969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65547408966243576458474501 12290139181170670585963969)
    ·
      refine ⟨9217604385878002939472977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12290139181170670585963969 9217604385878002939472977)
      ·
        refine ⟨6913203289408502204604733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9217604385878002939472977 6913203289408502204604733)
        ·
          refine ⟨2592451233528188326726775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6913203289408502204604733 2592451233528188326726775)
          ·
            refine ⟨3888676850292282490090163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2592451233528188326726775 3888676850292282490090163)
            ·
              refine ⟨5833015275438423735135245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3888676850292282490090163 5833015275438423735135245)
              ·
                refine ⟨2187380728289408900675717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5833015275438423735135245 2187380728289408900675717)
                ·
                  refine ⟨410133886554264168876697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2187380728289408900675717 410133886554264168876697)
                  ·
                    rfl

theorem cell21_1797149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 3, 4].length) (baseStart_1797149 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1797149 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1797149 prefixEnd_1797149 := by exact prefixLift 1797149
  have htrace : WordTrace (prefixWord ++ tailWord_1797149) baseStart_1797149 baseEnd_1797149 := by
    simpa [prefixWord, tailWord_1797149, baseEnd_1797149] using wordTrace_append hprefix tailTrace_1797149
  have hstable : (prefixWord ++ tailWord_1797149).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797149).length < 2 ^ (prefixWord ++ tailWord_1797149).sum := by decide
  have hdescent : baseEnd_1797149 < baseStart_1797149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797267 : List Nat := [1, 1, 1, 2, 1, 2, 4, 5, 4]
def baseStart_1797267 : Nat := 118140960795 + 1797267 * 2 ^ 59
def prefixEnd_1797267 : Nat := 4983230072969 + 3 ^ 40 * 1797267 * 2
def baseEnd_1797267 : Nat := 410160815761922185909789

theorem tailTrace_1797267 : CollatzResearch.WordTrace tailWord_1797267 prefixEnd_1797267 410160815761922185909789 := by
  unfold tailWord_1797267
  simp only [CollatzResearch.WordTrace]
  refine ⟨65551712779816082611270055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43701141853210721740846703 65551712779816082611270055)
  ·
    refine ⟨98327569169724123916905083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65551712779816082611270055 98327569169724123916905083)
    ·
      refine ⟨147491353754586185875357625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98327569169724123916905083 147491353754586185875357625)
      ·
        refine ⟨110618515315939639406518219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147491353754586185875357625 110618515315939639406518219)
        ·
          refine ⟨165927772973909459109777329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110618515315939639406518219 165927772973909459109777329)
          ·
            refine ⟨124445829730432094332332997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165927772973909459109777329 124445829730432094332332997)
            ·
              refine ⟨23333593074456017687312437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 124445829730432094332332997 23333593074456017687312437)
              ·
                refine ⟨2187524350730251658185541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23333593074456017687312437 2187524350730251658185541)
                ·
                  refine ⟨410160815761922185909789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2187524350730251658185541 410160815761922185909789)
                  ·
                    rfl

theorem cell21_1797267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 5, 4].length) (baseStart_1797267 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1797267 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1797267 prefixEnd_1797267 := by exact prefixLift 1797267
  have htrace : WordTrace (prefixWord ++ tailWord_1797267) baseStart_1797267 baseEnd_1797267 := by
    simpa [prefixWord, tailWord_1797267, baseEnd_1797267] using wordTrace_append hprefix tailTrace_1797267
  have hstable : (prefixWord ++ tailWord_1797267).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797267).length < 2 ^ (prefixWord ++ tailWord_1797267).sum := by decide
  have hdescent : baseEnd_1797267 < baseStart_1797267 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797287 : List Nat := [1, 1, 6, 2, 1, 1, 3, 3, 3]
def baseStart_1797287 : Nat := 118140960795 + 1797287 * 2 ^ 59
def prefixEnd_1797287 : Nat := 4983230072969 + 3 ^ 40 * 1797287 * 2
def baseEnd_1797287 : Nat := 410165380034406595576415

theorem tailTrace_1797287 : CollatzResearch.WordTrace tailWord_1797287 prefixEnd_1797287 410165380034406595576415 := by
  unfold tailWord_1797287
  simp only [CollatzResearch.WordTrace]
  refine ⟨65552442239743626026998115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43701628159829084017998743 65552442239743626026998115)
  ·
    refine ⟨98328663359615439040497173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65552442239743626026998115 98328663359615439040497173)
    ·
      refine ⟨4609156094981973705023305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 98328663359615439040497173 4609156094981973705023305)
      ·
        refine ⟨3456867071236480278767479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4609156094981973705023305 3456867071236480278767479)
        ·
          refine ⟨5185300606854720418151219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3456867071236480278767479 5185300606854720418151219)
          ·
            refine ⟨7777950910282080627226829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5185300606854720418151219 7777950910282080627226829)
            ·
              refine ⟨2916731591355780235210061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7777950910282080627226829 2916731591355780235210061)
              ·
                refine ⟨1093774346758417588203773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2916731591355780235210061 1093774346758417588203773)
                ·
                  refine ⟨410165380034406595576415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1093774346758417588203773 410165380034406595576415)
                  ·
                    rfl

theorem cell21_1797287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 3, 3].length) (baseStart_1797287 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1797287 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1797287 prefixEnd_1797287 := by exact prefixLift 1797287
  have htrace : WordTrace (prefixWord ++ tailWord_1797287) baseStart_1797287 baseEnd_1797287 := by
    simpa [prefixWord, tailWord_1797287, baseEnd_1797287] using wordTrace_append hprefix tailTrace_1797287
  have hstable : (prefixWord ++ tailWord_1797287).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797287).length < 2 ^ (prefixWord ++ tailWord_1797287).sum := by decide
  have hdescent : baseEnd_1797287 < baseStart_1797287 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797298 : List Nat := [3, 2, 1, 1, 1, 6, 7]
def baseStart_1797298 : Nat := 118140960795 + 1797298 * 2 ^ 59
def prefixEnd_1797298 : Nat := 4983230072969 + 3 ^ 40 * 1797298 * 2
def baseEnd_1797298 : Nat := 45574210042697002321451

theorem tailTrace_1797298 : CollatzResearch.WordTrace tailWord_1797298 prefixEnd_1797298 45574210042697002321451 := by
  unfold tailWord_1797298
  simp only [CollatzResearch.WordTrace]
  refine ⟨16388210860675943726412137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43701895628469183270432365 16388210860675943726412137)
  ·
    refine ⟨12291158145506957794809103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16388210860675943726412137 12291158145506957794809103)
    ·
      refine ⟨18436737218260436692213655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12291158145506957794809103 18436737218260436692213655)
      ·
        refine ⟨27655105827390655038320483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18436737218260436692213655 27655105827390655038320483)
        ·
          refine ⟨41482658741085982557480725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27655105827390655038320483 41482658741085982557480725)
          ·
            refine ⟨1944499628488405432381909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 41482658741085982557480725 1944499628488405432381909)
            ·
              refine ⟨45574210042697002321451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1944499628488405432381909 45574210042697002321451)
              ·
                rfl

theorem cell21_1797298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 7].length) (baseStart_1797298 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1797298 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1797298 prefixEnd_1797298 := by exact prefixLift 1797298
  have htrace : WordTrace (prefixWord ++ tailWord_1797298) baseStart_1797298 baseEnd_1797298 := by
    simpa [prefixWord, tailWord_1797298, baseEnd_1797298] using wordTrace_append hprefix tailTrace_1797298
  have hstable : (prefixWord ++ tailWord_1797298).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797298).length < 2 ^ (prefixWord ++ tailWord_1797298).sum := by decide
  have hdescent : baseEnd_1797298 < baseStart_1797298 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797363 : List Nat := [1, 1, 1, 2, 2, 7, 2, 2, 3]
def baseStart_1797363 : Nat := 118140960795 + 1797363 * 2 ^ 59
def prefixEnd_1797363 : Nat := 4983230072969 + 3 ^ 40 * 1797363 * 2
def baseEnd_1797363 : Nat := 410182724269847352309593

theorem tailTrace_1797363 : CollatzResearch.WordTrace tailWord_1797363 prefixEnd_1797363 410182724269847352309593 := by
  unfold tailWord_1797363
  simp only [CollatzResearch.WordTrace]
  refine ⟨65555214187468291006764743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43703476124978860671176495 65555214187468291006764743)
  ·
    refine ⟨98332821281202436510147115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65555214187468291006764743 98332821281202436510147115)
    ·
      refine ⟨147499231921803654765220673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98332821281202436510147115 147499231921803654765220673)
      ·
        refine ⟨110624423941352741073915505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147499231921803654765220673 110624423941352741073915505)
        ·
          refine ⟨82968317956014555805436629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110624423941352741073915505 82968317956014555805436629)
          ·
            refine ⟨1944569952094091151689921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 82968317956014555805436629 1944569952094091151689921)
            ·
              refine ⟨1458427464070568363767441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1944569952094091151689921 1458427464070568363767441)
              ·
                refine ⟨1093820598052926272825581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1458427464070568363767441 1093820598052926272825581)
                ·
                  refine ⟨410182724269847352309593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1093820598052926272825581 410182724269847352309593)
                  ·
                    rfl

theorem cell21_1797363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 2, 2, 3].length) (baseStart_1797363 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1797363 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1797363 prefixEnd_1797363 := by exact prefixLift 1797363
  have htrace : WordTrace (prefixWord ++ tailWord_1797363) baseStart_1797363 baseEnd_1797363 := by
    simpa [prefixWord, tailWord_1797363, baseEnd_1797363] using wordTrace_append hprefix tailTrace_1797363
  have hstable : (prefixWord ++ tailWord_1797363).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797363).length < 2 ^ (prefixWord ++ tailWord_1797363).sum := by decide
  have hdescent : baseEnd_1797363 < baseStart_1797363 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797388 : List Nat := [2, 2, 1, 2, 2, 3, 1, 1, 7]
def baseStart_1797388 : Nat := 118140960795 + 1797388 * 2 ^ 59
def prefixEnd_1797388 : Nat := 4983230072969 + 3 ^ 40 * 1797388 * 2
def baseEnd_1797388 : Nat := 410188429610452864392875

theorem tailTrace_1797388 : CollatzResearch.WordTrace tailWord_1797388 prefixEnd_1797388 410188429610452864392875 := by
  unfold tailWord_1797388
  simp only [CollatzResearch.WordTrace]
  refine ⟨32778063006188860138212409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43704084008251813517616545 32778063006188860138212409)
  ·
    refine ⟨24583547254641645103659307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32778063006188860138212409 24583547254641645103659307)
    ·
      refine ⟨36875320881962467655488961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24583547254641645103659307 36875320881962467655488961)
      ·
        refine ⟨27656490661471850741616721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36875320881962467655488961 27656490661471850741616721)
        ·
          refine ⟨20742367996103888056212541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27656490661471850741616721 20742367996103888056212541)
          ·
            refine ⟨7778387998538958021079703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20742367996103888056212541 7778387998538958021079703)
            ·
              refine ⟨11667581997808437031619555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7778387998538958021079703 11667581997808437031619555)
              ·
                refine ⟨17501372996712655547429333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11667581997808437031619555 17501372996712655547429333)
                ·
                  refine ⟨410188429610452864392875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17501372996712655547429333 410188429610452864392875)
                  ·
                    rfl

theorem cell21_1797388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 1, 7].length) (baseStart_1797388 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1797388 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1797388 prefixEnd_1797388 := by exact prefixLift 1797388
  have htrace : WordTrace (prefixWord ++ tailWord_1797388) baseStart_1797388 baseEnd_1797388 := by
    simpa [prefixWord, tailWord_1797388, baseEnd_1797388] using wordTrace_append hprefix tailTrace_1797388
  have hstable : (prefixWord ++ tailWord_1797388).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797388).length < 2 ^ (prefixWord ++ tailWord_1797388).sum := by decide
  have hdescent : baseEnd_1797388 < baseStart_1797388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797495 : List Nat := [1, 1, 3, 1, 1, 2, 5, 3, 4]
def baseStart_1797495 : Nat := 118140960795 + 1797495 * 2 ^ 59
def prefixEnd_1797495 : Nat := 4983230072969 + 3 ^ 40 * 1797495 * 2
def baseEnd_1797495 : Nat := 410212848468244456109323

theorem tailTrace_1797495 : CollatzResearch.WordTrace tailWord_1797495 prefixEnd_1797495 410212848468244456109323 := by
  unfold tailWord_1797495
  simp only [CollatzResearch.WordTrace]
  refine ⟨65560028622990077550569939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43706685748660051700379959 65560028622990077550569939)
  ·
    refine ⟨98340042934485116325854909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65560028622990077550569939 98340042934485116325854909)
    ·
      refine ⟨36877516100431918622195591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98340042934485116325854909 36877516100431918622195591)
      ·
        refine ⟨55316274150647877933293387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36877516100431918622195591 55316274150647877933293387)
        ·
          refine ⟨82974411225971816899940081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55316274150647877933293387 82974411225971816899940081)
          ·
            refine ⟨62230808419478862674955061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82974411225971816899940081 62230808419478862674955061)
            ·
              refine ⟨5834138289326143375777037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62230808419478862674955061 5834138289326143375777037)
              ·
                refine ⟨2187801858497303765916389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5834138289326143375777037 2187801858497303765916389)
                ·
                  refine ⟨410212848468244456109323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2187801858497303765916389 410212848468244456109323)
                  ·
                    rfl

theorem cell21_1797495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 3, 4].length) (baseStart_1797495 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1797495 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1797495 prefixEnd_1797495 := by exact prefixLift 1797495
  have htrace : WordTrace (prefixWord ++ tailWord_1797495) baseStart_1797495 baseEnd_1797495 := by
    simpa [prefixWord, tailWord_1797495, baseEnd_1797495] using wordTrace_append hprefix tailTrace_1797495
  have hstable : (prefixWord ++ tailWord_1797495).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797495).length < 2 ^ (prefixWord ++ tailWord_1797495).sum := by decide
  have hdescent : baseEnd_1797495 < baseStart_1797495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797509 : List Nat := [1, 3, 1, 1, 3, 1, 4, 7]
def baseStart_1797509 : Nat := 118140960795 + 1797509 * 2 ^ 59
def prefixEnd_1797509 : Nat := 4983230072969 + 3 ^ 40 * 1797509 * 2
def baseEnd_1797509 : Nat := 136738681152994514291987

theorem tailTrace_1797509 : CollatzResearch.WordTrace tailWord_1797509 prefixEnd_1797509 136738681152994514291987 := by
  unfold tailWord_1797509
  simp only [CollatzResearch.WordTrace]
  refine ⟨65560539244939357941579581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43707026163292905294386387 65560539244939357941579581)
  ·
    refine ⟨24585202216852259228092343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65560539244939357941579581 24585202216852259228092343)
    ·
      refine ⟨36877803325278388842138515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24585202216852259228092343 36877803325278388842138515)
      ·
        refine ⟨55316704987917583263207773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36877803325278388842138515 55316704987917583263207773)
        ·
          refine ⟨20743764370469093723702915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55316704987917583263207773 20743764370469093723702915)
          ·
            refine ⟨31115646555703640585554373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20743764370469093723702915 31115646555703640585554373)
            ·
              refine ⟨5834183729194432609791445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31115646555703640585554373 5834183729194432609791445)
              ·
                refine ⟨136738681152994514291987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5834183729194432609791445 136738681152994514291987)
                ·
                  rfl

theorem cell21_1797509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 7].length) (baseStart_1797509 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1797509 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1797509 prefixEnd_1797509 := by exact prefixLift 1797509
  have htrace : WordTrace (prefixWord ++ tailWord_1797509) baseStart_1797509 baseEnd_1797509 := by
    simpa [prefixWord, tailWord_1797509, baseEnd_1797509] using wordTrace_append hprefix tailTrace_1797509
  have hstable : (prefixWord ++ tailWord_1797509).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797509).length < 2 ^ (prefixWord ++ tailWord_1797509).sum := by decide
  have hdescent : baseEnd_1797509 < baseStart_1797509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797540 : List Nat := [2, 3, 1, 2, 1, 1, 1, 5, 5]
def baseStart_1797540 : Nat := 118140960795 + 1797540 * 2 ^ 59
def prefixEnd_1797540 : Nat := 4983230072969 + 3 ^ 40 * 1797540 * 2
def baseEnd_1797540 : Nat := 410223118081334377859231

theorem tailTrace_1797540 : CollatzResearch.WordTrace tailWord_1797540 prefixEnd_1797540 410223118081334377859231 := by
  unfold tailWord_1797540
  simp only [CollatzResearch.WordTrace]
  refine ⟨32780834953913525117979037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43707779938551366823972049 32780834953913525117979037)
  ·
    refine ⟨12292813107717571919242139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32780834953913525117979037 12292813107717571919242139)
    ·
      refine ⟨18439219661576357878863209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12292813107717571919242139 18439219661576357878863209)
      ·
        refine ⟨13829414746182268409147407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18439219661576357878863209 13829414746182268409147407)
        ·
          refine ⟨20744122119273402613721111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13829414746182268409147407 20744122119273402613721111)
          ·
            refine ⟨31116183178910103920581667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20744122119273402613721111 31116183178910103920581667)
            ·
              refine ⟨46674274768365155880872501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31116183178910103920581667 46674274768365155880872501)
              ·
                refine ⟨4375713259534233363831797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46674274768365155880872501 4375713259534233363831797)
                ·
                  refine ⟨410223118081334377859231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4375713259534233363831797 410223118081334377859231)
                  ·
                    rfl

theorem cell21_1797540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 5, 5].length) (baseStart_1797540 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1797540 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1797540 prefixEnd_1797540 := by exact prefixLift 1797540
  have htrace : WordTrace (prefixWord ++ tailWord_1797540) baseStart_1797540 baseEnd_1797540 := by
    simpa [prefixWord, tailWord_1797540, baseEnd_1797540] using wordTrace_append hprefix tailTrace_1797540
  have hstable : (prefixWord ++ tailWord_1797540).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797540).length < 2 ^ (prefixWord ++ tailWord_1797540).sum := by decide
  have hdescent : baseEnd_1797540 < baseStart_1797540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797557 : List Nat := [1, 3, 3, 2, 2, 2, 1, 2, 5]
def baseStart_1797557 : Nat := 118140960795 + 1797557 * 2 ^ 59
def prefixEnd_1797557 : Nat := 4983230072969 + 3 ^ 40 * 1797557 * 2
def baseEnd_1797557 : Nat := 410226997712946126075863

theorem tailTrace_1797557 : CollatzResearch.WordTrace tailWord_1797557 prefixEnd_1797557 410226997712946126075863 := by
  unfold tailWord_1797557
  simp only [CollatzResearch.WordTrace]
  refine ⟨65562289948765462139326925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43708193299176974759551283 65562289948765462139326925)
  ·
    refine ⟨24585858730787048302247597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65562289948765462139326925 24585858730787048302247597)
    ·
      refine ⟨9219697024045143113342849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24585858730787048302247597 9219697024045143113342849)
      ·
        refine ⟨6914772768033857335007137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9219697024045143113342849 6914772768033857335007137)
        ·
          refine ⟨5186079576025393001255353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6914772768033857335007137 5186079576025393001255353)
          ·
            refine ⟨3889559682019044750941515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5186079576025393001255353 3889559682019044750941515)
            ·
              refine ⟨5834339523028567126412273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3889559682019044750941515 5834339523028567126412273)
              ·
                refine ⟨4375754642271425344809205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5834339523028567126412273 4375754642271425344809205)
                ·
                  refine ⟨410226997712946126075863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4375754642271425344809205 410226997712946126075863)
                  ·
                    rfl

theorem cell21_1797557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 2, 5].length) (baseStart_1797557 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1797557 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1797557 prefixEnd_1797557 := by exact prefixLift 1797557
  have htrace : WordTrace (prefixWord ++ tailWord_1797557) baseStart_1797557 baseEnd_1797557 := by
    simpa [prefixWord, tailWord_1797557, baseEnd_1797557] using wordTrace_append hprefix tailTrace_1797557
  have hstable : (prefixWord ++ tailWord_1797557).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797557).length < 2 ^ (prefixWord ++ tailWord_1797557).sum := by decide
  have hdescent : baseEnd_1797557 < baseStart_1797557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797588 : List Nat := [2, 4, 1, 2, 3, 1, 1, 1, 6]
def baseStart_1797588 : Nat := 118140960795 + 1797588 * 2 ^ 59
def prefixEnd_1797588 : Nat := 4983230072969 + 3 ^ 40 * 1797588 * 2
def baseEnd_1797588 : Nat := 410234072335296961059133

theorem tailTrace_1797588 : CollatzResearch.WordTrace tailWord_1797588 prefixEnd_1797588 410234072335296961059133 := by
  unfold tailWord_1797588
  simp only [CollatzResearch.WordTrace]
  refine ⟨32781710305826577216852709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43708947074435436289136945 32781710305826577216852709)
  ·
    refine ⟨6146570682342483228159883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32781710305826577216852709 6146570682342483228159883)
    ·
      refine ⟨9219856023513724842239825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6146570682342483228159883 9219856023513724842239825)
      ·
        refine ⟨6914892017635293631679869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9219856023513724842239825 6914892017635293631679869)
        ·
          refine ⟨2593084506613235111879951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6914892017635293631679869 2593084506613235111879951)
          ·
            refine ⟨3889626759919852667819927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2593084506613235111879951 3889626759919852667819927)
            ·
              refine ⟨5834440139879779001729891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3889626759919852667819927 5834440139879779001729891)
              ·
                refine ⟨8751660209819668502594837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5834440139879779001729891 8751660209819668502594837)
                ·
                  refine ⟨410234072335296961059133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8751660209819668502594837 410234072335296961059133)
                  ·
                    rfl

theorem cell21_1797588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 1, 6].length) (baseStart_1797588 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1797588 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1797588 prefixEnd_1797588 := by exact prefixLift 1797588
  have htrace : WordTrace (prefixWord ++ tailWord_1797588) baseStart_1797588 baseEnd_1797588 := by
    simpa [prefixWord, tailWord_1797588, baseEnd_1797588] using wordTrace_append hprefix tailTrace_1797588
  have hstable : (prefixWord ++ tailWord_1797588).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797588).length < 2 ^ (prefixWord ++ tailWord_1797588).sum := by decide
  have hdescent : baseEnd_1797588 < baseStart_1797588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797605 : List Nat := [1, 3, 1, 5, 1, 2, 3, 1, 4]
def baseStart_1797605 : Nat := 118140960795 + 1797605 * 2 ^ 59
def prefixEnd_1797605 : Nat := 4983230072969 + 3 ^ 40 * 1797605 * 2
def baseEnd_1797605 : Nat := 410237951966908709275765

theorem tailTrace_1797605 : CollatzResearch.WordTrace tailWord_1797605 prefixEnd_1797605 410237951966908709275765 := by
  unfold tailWord_1797605
  simp only [CollatzResearch.WordTrace]
  refine ⟨65564040652591566337074269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43709360435061044224716179 65564040652591566337074269)
  ·
    refine ⟨24586515244721837376402851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65564040652591566337074269 24586515244721837376402851)
    ·
      refine ⟨36879772867082756064604277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24586515244721837376402851 36879772867082756064604277)
      ·
        refine ⟨3457478706289008381056651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36879772867082756064604277 3457478706289008381056651)
        ·
          refine ⟨5186218059433512571584977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3457478706289008381056651 5186218059433512571584977)
          ·
            refine ⟨3889663544575134428688733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5186218059433512571584977 3889663544575134428688733)
            ·
              refine ⟨1458623829215675410758275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3889663544575134428688733 1458623829215675410758275)
              ·
                refine ⟨2187935743823513116137413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1458623829215675410758275 2187935743823513116137413)
                ·
                  refine ⟨410237951966908709275765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2187935743823513116137413 410237951966908709275765)
                  ·
                    rfl

theorem cell21_1797605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 3, 1, 4].length) (baseStart_1797605 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1797605 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1797605 prefixEnd_1797605 := by exact prefixLift 1797605
  have htrace : WordTrace (prefixWord ++ tailWord_1797605) baseStart_1797605 baseEnd_1797605 := by
    simpa [prefixWord, tailWord_1797605, baseEnd_1797605] using wordTrace_append hprefix tailTrace_1797605
  have hstable : (prefixWord ++ tailWord_1797605).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797605).length < 2 ^ (prefixWord ++ tailWord_1797605).sum := by decide
  have hdescent : baseEnd_1797605 < baseStart_1797605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797616 : List Nat := [2, 1, 1, 1, 3, 4, 2, 2, 5]
def baseStart_1797616 : Nat := 118140960795 + 1797616 * 2 ^ 59
def prefixEnd_1797616 : Nat := 4983230072969 + 3 ^ 40 * 1797616 * 2
def baseEnd_1797616 : Nat := 410240462316775134592409

theorem tailTrace_1797616 : CollatzResearch.WordTrace tailWord_1797616 prefixEnd_1797616 410240462316775134592409 := by
  unfold tailWord_1797616
  simp only [CollatzResearch.WordTrace]
  refine ⟨32782220927775857607862351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43709627903701143477149801 32782220927775857607862351)
  ·
    refine ⟨49173331391663786411793527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32782220927775857607862351 49173331391663786411793527)
    ·
      refine ⟨73759997087495679617690291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49173331391663786411793527 73759997087495679617690291)
      ·
        refine ⟨110639995631243519426535437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73759997087495679617690291 110639995631243519426535437)
        ·
          refine ⟨41489998361716319784950789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110639995631243519426535437 41489998361716319784950789)
          ·
            refine ⟨7779374692821809959678273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41489998361716319784950789 7779374692821809959678273)
            ·
              refine ⟨5834531019616357469758705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7779374692821809959678273 5834531019616357469758705)
              ·
                refine ⟨4375898264712268102319029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5834531019616357469758705 4375898264712268102319029)
                ·
                  refine ⟨410240462316775134592409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4375898264712268102319029 410240462316775134592409)
                  ·
                    rfl

theorem cell21_1797616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 2, 5].length) (baseStart_1797616 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1797616 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1797616 prefixEnd_1797616 := by exact prefixLift 1797616
  have htrace : WordTrace (prefixWord ++ tailWord_1797616) baseStart_1797616 baseEnd_1797616 := by
    simpa [prefixWord, tailWord_1797616, baseEnd_1797616] using wordTrace_append hprefix tailTrace_1797616
  have hstable : (prefixWord ++ tailWord_1797616).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797616).length < 2 ^ (prefixWord ++ tailWord_1797616).sum := by decide
  have hdescent : baseEnd_1797616 < baseStart_1797616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797664 : List Nat := [2, 1, 1, 6, 1, 2, 1, 3, 4]
def baseStart_1797664 : Nat := 118140960795 + 1797664 * 2 ^ 59
def prefixEnd_1797664 : Nat := 4983230072969 + 3 ^ 40 * 1797664 * 2
def baseEnd_1797664 : Nat := 410251416570737717792311

theorem tailTrace_1797664 : CollatzResearch.WordTrace tailWord_1797664 prefixEnd_1797664 410251416570737717792311 := by
  unfold tailWord_1797664
  simp only [CollatzResearch.WordTrace]
  refine ⟨32783096279688909706736023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43710795039585212942314697 32783096279688909706736023)
  ·
    refine ⟨49174644419533364560104035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32783096279688909706736023 49174644419533364560104035)
    ·
      refine ⟨73761966629300046840156053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49174644419533364560104035 73761966629300046840156053)
      ·
        refine ⟨3457592185748439695632315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 73761966629300046840156053 3457592185748439695632315)
        ·
          refine ⟨5186388278622659543448473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3457592185748439695632315 5186388278622659543448473)
          ·
            refine ⟨3889791208966994657586355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5186388278622659543448473 3889791208966994657586355)
            ·
              refine ⟨5834686813450491986379533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3889791208966994657586355 5834686813450491986379533)
              ·
                refine ⟨2188007555043934494892325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5834686813450491986379533 2188007555043934494892325)
                ·
                  refine ⟨410251416570737717792311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2188007555043934494892325 410251416570737717792311)
                  ·
                    rfl

theorem cell21_1797664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 3, 4].length) (baseStart_1797664 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1797664 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1797664 prefixEnd_1797664 := by exact prefixLift 1797664
  have htrace : WordTrace (prefixWord ++ tailWord_1797664) baseStart_1797664 baseEnd_1797664 := by
    simpa [prefixWord, tailWord_1797664, baseEnd_1797664] using wordTrace_append hprefix tailTrace_1797664
  have hstable : (prefixWord ++ tailWord_1797664).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797664).length < 2 ^ (prefixWord ++ tailWord_1797664).sum := by decide
  have hdescent : baseEnd_1797664 < baseStart_1797664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797678 : List Nat := [4, 1, 3, 1, 2, 1, 2, 7]
def baseStart_1797678 : Nat := 118140960795 + 1797678 * 2 ^ 59
def prefixEnd_1797678 : Nat := 4983230072969 + 3 ^ 40 * 1797678 * 2
def baseEnd_1797678 : Nat := 136751537187158934852983

theorem tailTrace_1797678 : CollatzResearch.WordTrace tailWord_1797678 prefixEnd_1797678 136751537187158934852983 := by
  unfold tailWord_1797678
  simp only [CollatzResearch.WordTrace]
  refine ⟨8195837897665887475560211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43711135454218066536321125 8195837897665887475560211)
  ·
    refine ⟨12293756846498831213340317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8195837897665887475560211 12293756846498831213340317)
    ·
      refine ⟨4610158817437061705002619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12293756846498831213340317 4610158817437061705002619)
      ·
        refine ⟨6915238226155592557503929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4610158817437061705002619 6915238226155592557503929)
        ·
          refine ⟨5186428669616694418127947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6915238226155592557503929 5186428669616694418127947)
          ·
            refine ⟨7779643004425041627191921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5186428669616694418127947 7779643004425041627191921)
            ·
              refine ⟨5834732253318781220393941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7779643004425041627191921 5834732253318781220393941)
              ·
                refine ⟨136751537187158934852983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5834732253318781220393941 136751537187158934852983)
                ·
                  rfl

theorem cell21_1797678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 7].length) (baseStart_1797678 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1797678 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1797678 prefixEnd_1797678 := by exact prefixLift 1797678
  have htrace : WordTrace (prefixWord ++ tailWord_1797678) baseStart_1797678 baseEnd_1797678 := by
    simpa [prefixWord, tailWord_1797678, baseEnd_1797678] using wordTrace_append hprefix tailTrace_1797678
  have hstable : (prefixWord ++ tailWord_1797678).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797678).length < 2 ^ (prefixWord ++ tailWord_1797678).sum := by decide
  have hdescent : baseEnd_1797678 < baseStart_1797678 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797751 : List Nat := [1, 1, 3, 1, 1, 3, 1, 1, 9]
def baseStart_1797751 : Nat := 118140960795 + 1797751 * 2 ^ 59
def prefixEnd_1797751 : Nat := 4983230072969 + 3 ^ 40 * 1797751 * 2
def baseEnd_1797751 : Nat := 410271271156044899842133

theorem tailTrace_1797751 : CollatzResearch.WordTrace tailWord_1797751 prefixEnd_1797751 410271271156044899842133 := by
  unfold tailWord_1797751
  simp only [CollatzResearch.WordTrace]
  refine ⟨65569365710062633271889107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43712910473375088847926071 65569365710062633271889107)
  ·
    refine ⟨98354048565093949907833661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65569365710062633271889107 98354048565093949907833661)
    ·
      refine ⟨36882768211910231215437623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98354048565093949907833661 36882768211910231215437623)
      ·
        refine ⟨55324152317865346823156435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36882768211910231215437623 55324152317865346823156435)
        ·
          refine ⟨82986228476798020234734653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55324152317865346823156435 82986228476798020234734653)
          ·
            refine ⟨31119835678799257588025495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82986228476798020234734653 31119835678799257588025495)
            ·
              refine ⟨46679753518198886382038243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31119835678799257588025495 46679753518198886382038243)
              ·
                refine ⟨70019630277298329573057365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46679753518198886382038243 70019630277298329573057365)
                ·
                  refine ⟨410271271156044899842133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 70019630277298329573057365 410271271156044899842133)
                  ·
                    rfl

theorem cell21_1797751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 9].length) (baseStart_1797751 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1797751 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1797751 prefixEnd_1797751 := by exact prefixLift 1797751
  have htrace : WordTrace (prefixWord ++ tailWord_1797751) baseStart_1797751 baseEnd_1797751 := by
    simpa [prefixWord, tailWord_1797751, baseEnd_1797751] using wordTrace_append hprefix tailTrace_1797751
  have hstable : (prefixWord ++ tailWord_1797751).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797751).length < 2 ^ (prefixWord ++ tailWord_1797751).sum := by decide
  have hdescent : baseEnd_1797751 < baseStart_1797751 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797788 : List Nat := [2, 2, 3, 2, 4, 1, 2, 5]
def baseStart_1797788 : Nat := 118140960795 + 1797788 * 2 ^ 59
def prefixEnd_1797788 : Nat := 4983230072969 + 3 ^ 40 * 1797788 * 2
def baseEnd_1797788 : Nat := 136759905020047019241797

theorem tailTrace_1797788 : CollatzResearch.WordTrace tailWord_1797788 prefixEnd_1797788 136759905020047019241797 := by
  unfold tailWord_1797788
  simp only [CollatzResearch.WordTrace]
  refine ⟨32785357605464294295493009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43713810140619059060657345 32785357605464294295493009)
  ·
    refine ⟨24589018204098220721619757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32785357605464294295493009 24589018204098220721619757)
    ·
      refine ⟨9220881826536832770607409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24589018204098220721619757 9220881826536832770607409)
      ·
        refine ⟨6915661369902624577955557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9220881826536832770607409 6915661369902624577955557)
        ·
          refine ⟨1296686506856742108366667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6915661369902624577955557 1296686506856742108366667)
          ·
            refine ⟨1945029760285113162550001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1296686506856742108366667 1945029760285113162550001)
            ·
              refine ⟨1458772320213834871912501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1945029760285113162550001 1458772320213834871912501)
              ·
                refine ⟨136759905020047019241797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1458772320213834871912501 136759905020047019241797)
                ·
                  rfl

theorem cell21_1797788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 2, 5].length) (baseStart_1797788 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1797788 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1797788 prefixEnd_1797788 := by exact prefixLift 1797788
  have htrace : WordTrace (prefixWord ++ tailWord_1797788) baseStart_1797788 baseEnd_1797788 := by
    simpa [prefixWord, tailWord_1797788, baseEnd_1797788] using wordTrace_append hprefix tailTrace_1797788
  have hstable : (prefixWord ++ tailWord_1797788).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797788).length < 2 ^ (prefixWord ++ tailWord_1797788).sum := by decide
  have hdescent : baseEnd_1797788 < baseStart_1797788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797861 : List Nat := [1, 3, 1, 4, 1, 1, 2, 5, 3]
def baseStart_1797861 : Nat := 118140960795 + 1797861 * 2 ^ 59
def prefixEnd_1797861 : Nat := 4983230072969 + 3 ^ 40 * 1797861 * 2
def baseEnd_1797861 : Nat := 410296374654709153008575

theorem tailTrace_1797861 : CollatzResearch.WordTrace tailWord_1797861 prefixEnd_1797861 410296374654709153008575 := by
  unfold tailWord_1797861
  simp only [CollatzResearch.WordTrace]
  refine ⟨65573377739664122058393437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43715585159776081372262291 65573377739664122058393437)
  ·
    refine ⟨24590016652374045771897539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65573377739664122058393437 24590016652374045771897539)
    ·
      refine ⟨36885024978561068657846309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24590016652374045771897539 36885024978561068657846309)
      ·
        refine ⟨6915942183480200373346183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36885024978561068657846309 6915942183480200373346183)
        ·
          refine ⟨10373913275220300560019275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6915942183480200373346183 10373913275220300560019275)
          ·
            refine ⟨15560869912830450840028913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10373913275220300560019275 15560869912830450840028913)
            ·
              refine ⟨11670652434622838130021685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15560869912830450840028913 11670652434622838130021685)
              ·
                refine ⟨1094123665745891074689533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11670652434622838130021685 1094123665745891074689533)
                ·
                  refine ⟨410296374654709153008575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1094123665745891074689533 410296374654709153008575)
                  ·
                    rfl

theorem cell21_1797861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 5, 3].length) (baseStart_1797861 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1797861 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1797861 prefixEnd_1797861 := by exact prefixLift 1797861
  have htrace : WordTrace (prefixWord ++ tailWord_1797861) baseStart_1797861 baseEnd_1797861 := by
    simpa [prefixWord, tailWord_1797861, baseEnd_1797861] using wordTrace_append hprefix tailTrace_1797861
  have hstable : (prefixWord ++ tailWord_1797861).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797861).length < 2 ^ (prefixWord ++ tailWord_1797861).sum := by decide
  have hdescent : baseEnd_1797861 < baseStart_1797861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797878 : List Nat := [5, 1, 1, 1, 1, 4, 1, 4, 3]
def baseStart_1797878 : Nat := 118140960795 + 1797878 * 2 ^ 59
def prefixEnd_1797878 : Nat := 4983230072969 + 3 ^ 40 * 1797878 * 2
def baseEnd_1797878 : Nat := 410300254286320901225207

theorem tailTrace_1797878 : CollatzResearch.WordTrace tailWord_1797878 prefixEnd_1797878 410300254286320901225207 := by
  unfold tailWord_1797878
  simp only [CollatzResearch.WordTrace]
  refine ⟨4098374861287658372610143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43715998520401689307841525 4098374861287658372610143)
  ·
    refine ⟨6147562291931487558915215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4098374861287658372610143 6147562291931487558915215)
    ·
      refine ⟨9221343437897231338372823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6147562291931487558915215 9221343437897231338372823)
      ·
        refine ⟨13832015156845847007559235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9221343437897231338372823 13832015156845847007559235)
        ·
          refine ⟨20748022735268770511338853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13832015156845847007559235 20748022735268770511338853)
          ·
            refine ⟨3890254262862894470876035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20748022735268770511338853 3890254262862894470876035)
            ·
              refine ⟨5835381394294341706314053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3890254262862894470876035 5835381394294341706314053)
              ·
                refine ⟨1094134011430189069933885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5835381394294341706314053 1094134011430189069933885)
                ·
                  refine ⟨410300254286320901225207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1094134011430189069933885 410300254286320901225207)
                  ·
                    rfl

theorem cell21_1797878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 4, 3].length) (baseStart_1797878 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1797878 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1797878 prefixEnd_1797878 := by exact prefixLift 1797878
  have htrace : WordTrace (prefixWord ++ tailWord_1797878) baseStart_1797878 baseEnd_1797878 := by
    simpa [prefixWord, tailWord_1797878, baseEnd_1797878] using wordTrace_append hprefix tailTrace_1797878
  have hstable : (prefixWord ++ tailWord_1797878).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797878).length < 2 ^ (prefixWord ++ tailWord_1797878).sum := by decide
  have hdescent : baseEnd_1797878 < baseStart_1797878 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797889 : List Nat := [1, 2, 4, 1, 1, 1, 5, 6]
def baseStart_1797889 : Nat := 118140960795 + 1797889 * 2 ^ 59
def prefixEnd_1797889 : Nat := 4983230072969 + 3 ^ 40 * 1797889 * 2
def baseEnd_1797889 : Nat := 136767588212062442180617

theorem tailTrace_1797889 : CollatzResearch.WordTrace tailWord_1797889 prefixEnd_1797889 136767588212062442180617 := by
  unfold tailWord_1797889
  simp only [CollatzResearch.WordTrace]
  refine ⟨65574398983562682840412721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43716265989041788560275147 65574398983562682840412721)
  ·
    refine ⟨49180799237672012130309541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65574398983562682840412721 49180799237672012130309541)
    ·
      refine ⟨9221399857063502274433039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49180799237672012130309541 9221399857063502274433039)
      ·
        refine ⟨13832099785595253411649559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9221399857063502274433039 13832099785595253411649559)
        ·
          refine ⟨20748149678392880117474339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13832099785595253411649559 20748149678392880117474339)
          ·
            refine ⟨31122224517589320176211509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20748149678392880117474339 31122224517589320176211509)
            ·
              refine ⟨2917708548523998766519829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31122224517589320176211509 2917708548523998766519829)
              ·
                refine ⟨136767588212062442180617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2917708548523998766519829 136767588212062442180617)
                ·
                  rfl

theorem cell21_1797889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 6].length) (baseStart_1797889 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1797889 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1797889 prefixEnd_1797889 := by exact prefixLift 1797889
  have htrace : WordTrace (prefixWord ++ tailWord_1797889) baseStart_1797889 baseEnd_1797889 := by
    simpa [prefixWord, tailWord_1797889, baseEnd_1797889] using wordTrace_append hprefix tailTrace_1797889
  have hstable : (prefixWord ++ tailWord_1797889).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797889).length < 2 ^ (prefixWord ++ tailWord_1797889).sum := by decide
  have hdescent : baseEnd_1797889 < baseStart_1797889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797937 : List Nat := [1, 2, 2, 3, 2, 2, 2, 4, 3]
def baseStart_1797937 : Nat := 118140960795 + 1797937 * 2 ^ 59
def prefixEnd_1797937 : Nat := 4983230072969 + 3 ^ 40 * 1797937 * 2
def baseEnd_1797937 : Nat := 410313718890149909741753

theorem tailTrace_1797937 : CollatzResearch.WordTrace tailWord_1797937 prefixEnd_1797937 410313718890149909741753 := by
  unfold tailWord_1797937
  simp only [CollatzResearch.WordTrace]
  refine ⟨65576149687388787038160065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43717433124925858025440043 65576149687388787038160065)
  ·
    refine ⟨49182112265541590278620049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65576149687388787038160065 49182112265541590278620049)
    ·
      refine ⟨36886584199156192708965037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49182112265541590278620049 36886584199156192708965037)
      ·
        refine ⟨13832469074683572265861889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36886584199156192708965037 13832469074683572265861889)
        ·
          refine ⟨10374351806012679199396417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13832469074683572265861889 10374351806012679199396417)
          ·
            refine ⟨7780763854509509399547313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10374351806012679199396417 7780763854509509399547313)
            ·
              refine ⟨5835572890882132049660485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7780763854509509399547313 5835572890882132049660485)
              ·
                refine ⟨1094169917040399759311341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5835572890882132049660485 1094169917040399759311341)
                ·
                  refine ⟨410313718890149909741753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1094169917040399759311341 410313718890149909741753)
                  ·
                    rfl

theorem cell21_1797937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 4, 3].length) (baseStart_1797937 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1797937 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1797937 prefixEnd_1797937 := by exact prefixLift 1797937
  have htrace : WordTrace (prefixWord ++ tailWord_1797937) baseStart_1797937 baseEnd_1797937 := by
    simpa [prefixWord, tailWord_1797937, baseEnd_1797937] using wordTrace_append hprefix tailTrace_1797937
  have hstable : (prefixWord ++ tailWord_1797937).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797937).length < 2 ^ (prefixWord ++ tailWord_1797937).sum := by decide
  have hdescent : baseEnd_1797937 < baseStart_1797937 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797996 : List Nat := [2, 2, 1, 1, 4, 2, 3, 1, 5]
def baseStart_1797996 : Nat := 118140960795 + 1797996 * 2 ^ 59
def prefixEnd_1797996 : Nat := 4983230072969 + 3 ^ 40 * 1797996 * 2
def baseEnd_1797996 : Nat := 410327183493978918258299

theorem tailTrace_1797996 : CollatzResearch.WordTrace tailWord_1797996 prefixEnd_1797996 410327183493978918258299 := by
  unfold tailWord_1797996
  simp only [CollatzResearch.WordTrace]
  refine ⟨32789150797087520057278921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43718867729450026743038561 32789150797087520057278921)
  ·
    refine ⟨24591863097815640042959191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32789150797087520057278921 24591863097815640042959191)
    ·
      refine ⟨36887794646723460064438787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24591863097815640042959191 36887794646723460064438787)
      ·
        refine ⟨55331691970085190096658181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36887794646723460064438787 55331691970085190096658181)
        ·
          refine ⟨10374692244390973143123409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55331691970085190096658181 10374692244390973143123409)
          ·
            refine ⟨7781019183293229857342557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10374692244390973143123409 7781019183293229857342557)
            ·
              refine ⟨2917882193734961196503459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7781019183293229857342557 2917882193734961196503459)
              ·
                refine ⟨4376823290602441794755189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2917882193734961196503459 4376823290602441794755189)
                ·
                  refine ⟨410327183493978918258299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4376823290602441794755189 410327183493978918258299)
                  ·
                    rfl

theorem cell21_1797996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 5].length) (baseStart_1797996 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1797996 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1797996 prefixEnd_1797996 := by exact prefixLift 1797996
  have htrace : WordTrace (prefixWord ++ tailWord_1797996) baseStart_1797996 baseEnd_1797996 := by
    simpa [prefixWord, tailWord_1797996, baseEnd_1797996] using wordTrace_append hprefix tailTrace_1797996
  have hstable : (prefixWord ++ tailWord_1797996).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797996).length < 2 ^ (prefixWord ++ tailWord_1797996).sum := by decide
  have hdescent : baseEnd_1797996 < baseStart_1797996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1798044 : List Nat := [2, 2, 3, 3, 1, 2, 2, 2, 4]
def baseStart_1798044 : Nat := 118140960795 + 1798044 * 2 ^ 59
def prefixEnd_1798044 : Nat := 4983230072969 + 3 ^ 40 * 1798044 * 2
def baseEnd_1798044 : Nat := 410338137747941501458201

theorem tailTrace_1798044 : CollatzResearch.WordTrace tailWord_1798044 prefixEnd_1798044 410338137747941501458201 := by
  unfold tailWord_1798044
  simp only [CollatzResearch.WordTrace]
  refine ⟨32790026149000572156152593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43720034865334096208203457 32790026149000572156152593)
  ·
    refine ⟨24592519611750429117114445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32790026149000572156152593 24592519611750429117114445)
    ·
      refine ⟨9222194854406410918917917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24592519611750429117114445 9222194854406410918917917)
      ·
        refine ⟨3458323070402404094594219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9222194854406410918917917 3458323070402404094594219)
        ·
          refine ⟨5187484605603606141891329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3458323070402404094594219 5187484605603606141891329)
          ·
            refine ⟨3890613454202704606418497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5187484605603606141891329 3890613454202704606418497)
            ·
              refine ⟨2917960090652028454813873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3890613454202704606418497 2917960090652028454813873)
              ·
                refine ⟨2188470067989021341110405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2917960090652028454813873 2188470067989021341110405)
                ·
                  refine ⟨410338137747941501458201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2188470067989021341110405 410338137747941501458201)
                  ·
                    rfl

theorem cell21_1798044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 2, 4].length) (baseStart_1798044 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1798044 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1798044 prefixEnd_1798044 := by exact prefixLift 1798044
  have htrace : WordTrace (prefixWord ++ tailWord_1798044) baseStart_1798044 baseEnd_1798044 := by
    simpa [prefixWord, tailWord_1798044, baseEnd_1798044] using wordTrace_append hprefix tailTrace_1798044
  have hstable : (prefixWord ++ tailWord_1798044).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798044).length < 2 ^ (prefixWord ++ tailWord_1798044).sum := by decide
  have hdescent : baseEnd_1798044 < baseStart_1798044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1798047 : List Nat := [1, 1, 2, 5, 3, 2, 2, 2, 3]
def baseStart_1798047 : Nat := 118140960795 + 1798047 * 2 ^ 59
def prefixEnd_1798047 : Nat := 4983230072969 + 3 ^ 40 * 1798047 * 2
def baseEnd_1798047 : Nat := 410338822388814162908195

theorem tailTrace_1798047 : CollatzResearch.WordTrace tailWord_1798047 prefixEnd_1798047 410338822388814162908195 := by
  unfold tailWord_1798047
  simp only [CollatzResearch.WordTrace]
  refine ⟨65580161716990275824664395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43720107811326850549776263 65580161716990275824664395)
  ·
    refine ⟨98370242575485413736996593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65580161716990275824664395 98370242575485413736996593)
    ·
      refine ⟨73777681931614060302747445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98370242575485413736996593 73777681931614060302747445)
      ·
        refine ⟨6916657681088818153382573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 73777681931614060302747445 6916657681088818153382573)
        ·
          refine ⟨2593746630408306807518465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6916657681088818153382573 2593746630408306807518465)
          ·
            refine ⟨1945309972806230105638849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2593746630408306807518465 1945309972806230105638849)
            ·
              refine ⟨1458982479604672579229137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1945309972806230105638849 1458982479604672579229137)
              ·
                refine ⟨1094236859703504434421853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1458982479604672579229137 1094236859703504434421853)
                ·
                  refine ⟨410338822388814162908195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1094236859703504434421853 410338822388814162908195)
                  ·
                    rfl

theorem cell21_1798047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 2, 2, 3].length) (baseStart_1798047 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1798047 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1798047 prefixEnd_1798047 := by exact prefixLift 1798047
  have htrace : WordTrace (prefixWord ++ tailWord_1798047) baseStart_1798047 baseEnd_1798047 := by
    simpa [prefixWord, tailWord_1798047, baseEnd_1798047] using wordTrace_append hprefix tailTrace_1798047
  have hstable : (prefixWord ++ tailWord_1798047).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798047).length < 2 ^ (prefixWord ++ tailWord_1798047).sum := by decide
  have hdescent : baseEnd_1798047 < baseStart_1798047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1798134 : List Nat := [5, 1, 1, 1, 4, 1, 1, 7]
def baseStart_1798134 : Nat := 118140960795 + 1798134 * 2 ^ 59
def prefixEnd_1798134 : Nat := 4983230072969 + 3 ^ 40 * 1798134 * 2
def baseEnd_1798134 : Nat := 136786225658040448319339

theorem tailTrace_1798134 : CollatzResearch.WordTrace tailWord_1798134 prefixEnd_1798134 136786225658040448319339 := by
  unfold tailWord_1798134
  simp only [CollatzResearch.WordTrace]
  refine ⟨4098958429229693105192591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43722223245116726455387637 4098958429229693105192591)
  ·
    refine ⟨6148437643844539657788887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4098958429229693105192591 6148437643844539657788887)
    ·
      refine ⟨9222656465766809486683331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6148437643844539657788887 9222656465766809486683331)
      ·
        refine ⟨13833984698650214230024997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9222656465766809486683331 13833984698650214230024997)
        ·
          refine ⟨2593872130996915168129687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13833984698650214230024997 2593872130996915168129687)
          ·
            refine ⟨3890808196495372752194531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2593872130996915168129687 3890808196495372752194531)
            ·
              refine ⟨5836212294743059128291797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3890808196495372752194531 5836212294743059128291797)
              ·
                refine ⟨136786225658040448319339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5836212294743059128291797 136786225658040448319339)
                ·
                  rfl

theorem cell21_1798134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 7].length) (baseStart_1798134 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1798134 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1798134 prefixEnd_1798134 := by exact prefixLift 1798134
  have htrace : WordTrace (prefixWord ++ tailWord_1798134) baseStart_1798134 baseEnd_1798134 := by
    simpa [prefixWord, tailWord_1798134, baseEnd_1798134] using wordTrace_append hprefix tailTrace_1798134
  have hstable : (prefixWord ++ tailWord_1798134).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798134).length < 2 ^ (prefixWord ++ tailWord_1798134).sum := by decide
  have hdescent : baseEnd_1798134 < baseStart_1798134 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1798157 : List Nat := [1, 7, 1, 2, 1, 1, 3, 2, 3]
def baseStart_1798157 : Nat := 118140960795 + 1798157 * 2 ^ 59
def prefixEnd_1798157 : Nat := 4983230072969 + 3 ^ 40 * 1798157 * 2
def baseEnd_1798157 : Nat := 410363925887478416074637

theorem tailTrace_1798157 : CollatzResearch.WordTrace tailWord_1798157 prefixEnd_1798157 410363925887478416074637 := by
  unfold tailWord_1798157
  simp only [CollatzResearch.WordTrace]
  refine ⟨65584173746591764611168725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43722782497727843074112483 65584173746591764611168725)
  ·
    refine ⟨1537129072185744483074267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 65584173746591764611168725 1537129072185744483074267)
    ·
      refine ⟨2305693608278616724611401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1537129072185744483074267 2305693608278616724611401)
      ·
        refine ⟨1729270206208962543458551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2305693608278616724611401 1729270206208962543458551)
        ·
          refine ⟨2593905309313443815187827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1729270206208962543458551 2593905309313443815187827)
          ·
            refine ⟨3890857963970165722781741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2593905309313443815187827 3890857963970165722781741)
            ·
              refine ⟨1459071736488812146043153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3890857963970165722781741 1459071736488812146043153)
              ·
                refine ⟨1094303802366609109532365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1459071736488812146043153 1094303802366609109532365)
                ·
                  refine ⟨410363925887478416074637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1094303802366609109532365 410363925887478416074637)
                  ·
                    rfl

theorem cell21_1798157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_1798157 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1798157 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1798157 prefixEnd_1798157 := by exact prefixLift 1798157
  have htrace : WordTrace (prefixWord ++ tailWord_1798157) baseStart_1798157 baseEnd_1798157 := by
    simpa [prefixWord, tailWord_1798157, baseEnd_1798157] using wordTrace_append hprefix tailTrace_1798157
  have hstable : (prefixWord ++ tailWord_1798157).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798157).length < 2 ^ (prefixWord ++ tailWord_1798157).sum := by decide
  have hdescent : baseEnd_1798157 < baseStart_1798157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1798165 : List Nat := [1, 3, 2, 1, 5, 2, 1, 1, 5]
def baseStart_1798165 : Nat := 118140960795 + 1798165 * 2 ^ 59
def prefixEnd_1798165 : Nat := 4983230072969 + 3 ^ 40 * 1798165 * 2
def baseEnd_1798165 : Nat := 410365751596472179941287

theorem tailTrace_1798165 : CollatzResearch.WordTrace tailWord_1798165 prefixEnd_1798165 410365751596472179941287 := by
  unfold tailWord_1798165
  simp only [CollatzResearch.WordTrace]
  refine ⟨65584465530562781977459949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43722977020375187984973299 65584465530562781977459949)
  ·
    refine ⟨24594174573961043241547481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65584465530562781977459949 24594174573961043241547481)
    ·
      refine ⟨18445630930470782431160611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24594174573961043241547481 18445630930470782431160611)
      ·
        refine ⟨27668446395706173646740917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18445630930470782431160611 27668446395706173646740917)
        ·
          refine ⟨2593916849597453779381961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27668446395706173646740917 2593916849597453779381961)
          ·
            refine ⟨1945437637198090334536471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2593916849597453779381961 1945437637198090334536471)
            ·
              refine ⟨2918156455797135501804707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1945437637198090334536471 2918156455797135501804707)
              ·
                refine ⟨4377234683695703252707061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2918156455797135501804707 4377234683695703252707061)
                ·
                  refine ⟨410365751596472179941287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4377234683695703252707061 410365751596472179941287)
                  ·
                    rfl

theorem cell21_1798165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 1, 5].length) (baseStart_1798165 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1798165 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1798165 prefixEnd_1798165 := by exact prefixLift 1798165
  have htrace : WordTrace (prefixWord ++ tailWord_1798165) baseStart_1798165 baseEnd_1798165 := by
    simpa [prefixWord, tailWord_1798165, baseEnd_1798165] using wordTrace_append hprefix tailTrace_1798165
  have hstable : (prefixWord ++ tailWord_1798165).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798165).length < 2 ^ (prefixWord ++ tailWord_1798165).sum := by decide
  have hdescent : baseEnd_1798165 < baseStart_1798165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1798334 : List Nat := [4, 2, 1, 1, 5, 1, 1, 1, 5]
def baseStart_1798334 : Nat := 118140960795 + 1798334 * 2 ^ 59
def prefixEnd_1798334 : Nat := 4983230072969 + 3 ^ 40 * 1798334 * 2
def baseEnd_1798334 : Nat := 410404319698965441624275

theorem tailTrace_1798334 : CollatzResearch.WordTrace tailWord_1798334 prefixEnd_1798334 410404319698965441624275 := by
  unfold tailWord_1798334
  simp only [CollatzResearch.WordTrace]
  refine ⟨8198828683368815480045257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43727086311300349226908037 8198828683368815480045257)
  ·
    refine ⟨6149121512526611610033943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8198828683368815480045257 6149121512526611610033943)
    ·
      refine ⟨9223682268789917415050915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6149121512526611610033943 9223682268789917415050915)
      ·
        refine ⟨13835523403184876122576373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9223682268789917415050915 13835523403184876122576373)
        ·
          refine ⟨1297080319048582136491535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13835523403184876122576373 1297080319048582136491535)
          ·
            refine ⟨1945620478572873204737303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1297080319048582136491535 1945620478572873204737303)
            ·
              refine ⟨2918430717859309807105955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1945620478572873204737303 2918430717859309807105955)
              ·
                refine ⟨4377646076788964710658933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2918430717859309807105955 4377646076788964710658933)
                ·
                  refine ⟨410404319698965441624275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4377646076788964710658933 410404319698965441624275)
                  ·
                    rfl

theorem cell21_1798334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 1, 5].length) (baseStart_1798334 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1798334 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1798334 prefixEnd_1798334 := by exact prefixLift 1798334
  have htrace : WordTrace (prefixWord ++ tailWord_1798334) baseStart_1798334 baseEnd_1798334 := by
    simpa [prefixWord, tailWord_1798334, baseEnd_1798334] using wordTrace_append hprefix tailTrace_1798334
  have hstable : (prefixWord ++ tailWord_1798334).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798334).length < 2 ^ (prefixWord ++ tailWord_1798334).sum := by decide
  have hdescent : baseEnd_1798334 < baseStart_1798334 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1798348 : List Nat := [2, 2, 1, 6, 1, 1, 1, 3, 4]
def baseStart_1798348 : Nat := 118140960795 + 1798348 * 2 ^ 59
def prefixEnd_1798348 : Nat := 4983230072969 + 3 ^ 40 * 1798348 * 2
def baseEnd_1798348 : Nat := 410407514689704528390913

theorem tailTrace_1798348 : CollatzResearch.WordTrace tailWord_1798348 prefixEnd_1798348 410407514689704528390913 := by
  unfold tailWord_1798348
  simp only [CollatzResearch.WordTrace]
  refine ⟨32795570044449902115685849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43727426725933202820914465 32795570044449902115685849)
  ·
    refine ⟨24596677533337426586764387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32795570044449902115685849 24596677533337426586764387)
    ·
      refine ⟨36895016300006139880146581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24596677533337426586764387 36895016300006139880146581)
      ·
        refine ⟨1729453889062787806881871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 36895016300006139880146581 1729453889062787806881871)
        ·
          refine ⟨2594180833594181710322807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1729453889062787806881871 2594180833594181710322807)
          ·
            refine ⟨3891271250391272565484211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2594180833594181710322807 3891271250391272565484211)
            ·
              refine ⟨5836906875586908848226317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3891271250391272565484211 5836906875586908848226317)
              ·
                refine ⟨2188840078345090818084869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5836906875586908848226317 2188840078345090818084869)
                ·
                  refine ⟨410407514689704528390913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2188840078345090818084869 410407514689704528390913)
                  ·
                    rfl

theorem cell21_1798348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 3, 4].length) (baseStart_1798348 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1798348 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1798348 prefixEnd_1798348 := by exact prefixLift 1798348
  have htrace : WordTrace (prefixWord ++ tailWord_1798348) baseStart_1798348 baseEnd_1798348 := by
    simpa [prefixWord, tailWord_1798348, baseEnd_1798348] using wordTrace_append hprefix tailTrace_1798348
  have hstable : (prefixWord ++ tailWord_1798348).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798348).length < 2 ^ (prefixWord ++ tailWord_1798348).sum := by decide
  have hdescent : baseEnd_1798348 < baseStart_1798348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1798390 : List Nat := [5, 1, 1, 1, 1, 1, 2, 3, 6]
def baseStart_1798390 : Nat := 118140960795 + 1798390 * 2 ^ 59
def prefixEnd_1798390 : Nat := 4983230072969 + 3 ^ 40 * 1798390 * 2
def baseEnd_1798390 : Nat := 410417099661921788690827

theorem tailTrace_1798390 : CollatzResearch.WordTrace tailWord_1798390 prefixEnd_1798390 410417099661921788690827 := by
  unfold tailWord_1798390
  simp only [CollatzResearch.WordTrace]
  refine ⟨4099541997171727837775039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43728447969831763602933749 4099541997171727837775039)
  ·
    refine ⟨6149312995757591756662559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4099541997171727837775039 6149312995757591756662559)
    ·
      refine ⟨9223969493636387634993839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6149312995757591756662559 9223969493636387634993839)
      ·
        refine ⟨13835954240454581452490759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9223969493636387634993839 13835954240454581452490759)
        ·
          refine ⟨20753931360681872178736139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13835954240454581452490759 20753931360681872178736139)
          ·
            refine ⟨31130897041022808268104209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20753931360681872178736139 31130897041022808268104209)
            ·
              refine ⟨23348172780767106201078157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31130897041022808268104209 23348172780767106201078157)
              ·
                refine ⟨8755564792787664825404309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23348172780767106201078157 8755564792787664825404309)
                ·
                  refine ⟨410417099661921788690827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8755564792787664825404309 410417099661921788690827)
                  ·
                    rfl

theorem cell21_1798390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_1798390 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1798390 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1798390 prefixEnd_1798390 := by exact prefixLift 1798390
  have htrace : WordTrace (prefixWord ++ tailWord_1798390) baseStart_1798390 baseEnd_1798390 := by
    simpa [prefixWord, tailWord_1798390, baseEnd_1798390] using wordTrace_append hprefix tailTrace_1798390
  have hstable : (prefixWord ++ tailWord_1798390).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798390).length < 2 ^ (prefixWord ++ tailWord_1798390).sum := by decide
  have hdescent : baseEnd_1798390 < baseStart_1798390 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1798452 : List Nat := [2, 5, 1, 1, 1, 2, 1, 3, 5]
def baseStart_1798452 : Nat := 118140960795 + 1798452 * 2 ^ 59
def prefixEnd_1798452 : Nat := 4983230072969 + 3 ^ 40 * 1798452 * 2
def baseEnd_1798452 : Nat := 410431248906623458657367

theorem tailTrace_1798452 : CollatzResearch.WordTrace tailWord_1798452 prefixEnd_1798452 410431248906623458657367 := by
  unfold tailWord_1798452
  simp only [CollatzResearch.WordTrace]
  refine ⟨32797466640261514996578805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43729955520348686662105073 32797466640261514996578805)
  ·
    refine ⟨3074762497524517030929263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32797466640261514996578805 3074762497524517030929263)
    ·
      refine ⟨4612143746286775546393895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3074762497524517030929263 4612143746286775546393895)
      ·
        refine ⟨6918215619430163319590843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4612143746286775546393895 6918215619430163319590843)
        ·
          refine ⟨10377323429145244979386265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6918215619430163319590843 10377323429145244979386265)
          ·
            refine ⟨7782992571858933734539699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10377323429145244979386265 7782992571858933734539699)
            ·
              refine ⟨11674488857788400601809549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7782992571858933734539699 11674488857788400601809549)
              ·
                refine ⟨4377933321670650225678581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11674488857788400601809549 4377933321670650225678581)
                ·
                  refine ⟨410431248906623458657367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4377933321670650225678581 410431248906623458657367)
                  ·
                    rfl

theorem cell21_1798452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_1798452 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1798452 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1798452 prefixEnd_1798452 := by exact prefixLift 1798452
  have htrace : WordTrace (prefixWord ++ tailWord_1798452) baseStart_1798452 baseEnd_1798452 := by
    simpa [prefixWord, tailWord_1798452, baseEnd_1798452] using wordTrace_append hprefix tailTrace_1798452
  have hstable : (prefixWord ++ tailWord_1798452).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798452).length < 2 ^ (prefixWord ++ tailWord_1798452).sum := by decide
  have hdescent : baseEnd_1798452 < baseStart_1798452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1798480 : List Nat := [2, 1, 1, 1, 1, 7, 1, 7]
def baseStart_1798480 : Nat := 118140960795 + 1798480 * 2 ^ 59
def prefixEnd_1798480 : Nat := 4983230072969 + 3 ^ 40 * 1798480 * 2
def baseEnd_1798480 : Nat := 136812546296033877396881

theorem tailTrace_1798480 : CollatzResearch.WordTrace tailWord_1798480 prefixEnd_1798480 136812546296033877396881 := by
  unfold tailWord_1798480
  simp only [CollatzResearch.WordTrace]
  refine ⟨32797977262210795387588447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43730636349614393850117929 32797977262210795387588447)
  ·
    refine ⟨49196965893316193081382671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32797977262210795387588447 49196965893316193081382671)
    ·
      refine ⟨73795448839974289622074007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49196965893316193081382671 73795448839974289622074007)
      ·
        refine ⟨110693173259961434433111011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73795448839974289622074007 110693173259961434433111011)
        ·
          refine ⟨166039759889942151649666517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110693173259961434433111011 166039759889942151649666517)
          ·
            refine ⟨3891556872420519179289059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 166039759889942151649666517 3891556872420519179289059)
            ·
              refine ⟨5837335308630778768933589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3891556872420519179289059 5837335308630778768933589)
              ·
                refine ⟨136812546296033877396881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5837335308630778768933589 136812546296033877396881)
                ·
                  rfl

theorem cell21_1798480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 7].length) (baseStart_1798480 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1798480 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1798480 prefixEnd_1798480 := by exact prefixLift 1798480
  have htrace : WordTrace (prefixWord ++ tailWord_1798480) baseStart_1798480 baseEnd_1798480 := by
    simpa [prefixWord, tailWord_1798480, baseEnd_1798480] using wordTrace_append hprefix tailTrace_1798480
  have hstable : (prefixWord ++ tailWord_1798480).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798480).length < 2 ^ (prefixWord ++ tailWord_1798480).sum := by decide
  have hdescent : baseEnd_1798480 < baseStart_1798480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1798677 : List Nat := [1, 3, 2, 1, 3, 1, 1, 3, 6]
def baseStart_1798677 : Nat := 118140960795 + 1798677 * 2 ^ 59
def prefixEnd_1798677 : Nat := 4983230072969 + 3 ^ 40 * 1798677 * 2
def baseEnd_1798677 : Nat := 410482596972073067406907

theorem tailTrace_1798677 : CollatzResearch.WordTrace tailWord_1798677 prefixEnd_1798677 410482596972073067406907 := by
  unfold tailWord_1798677
  simp only [CollatzResearch.WordTrace]
  refine ⟨65603139704707893420098285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43735426469805262280065523 65603139704707893420098285)
  ·
    refine ⟨24601177389265460032536857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65603139704707893420098285 24601177389265460032536857)
    ·
      refine ⟨18450883041949095024402643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24601177389265460032536857 18450883041949095024402643)
      ·
        refine ⟨27676324562923642536603965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18450883041949095024402643 27676324562923642536603965)
        ·
          refine ⟨10378621711096365951226487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27676324562923642536603965 10378621711096365951226487)
          ·
            refine ⟨15567932566644548926839731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10378621711096365951226487 15567932566644548926839731)
            ·
              refine ⟨23351898849966823390259597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15567932566644548926839731 23351898849966823390259597)
              ·
                refine ⟨8756962068737558771347349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23351898849966823390259597 8756962068737558771347349)
                ·
                  refine ⟨410482596972073067406907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8756962068737558771347349 410482596972073067406907)
                  ·
                    rfl

theorem cell21_1798677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 3, 6].length) (baseStart_1798677 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1798677 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1798677 prefixEnd_1798677 := by exact prefixLift 1798677
  have htrace : WordTrace (prefixWord ++ tailWord_1798677) baseStart_1798677 baseEnd_1798677 := by
    simpa [prefixWord, tailWord_1798677, baseEnd_1798677] using wordTrace_append hprefix tailTrace_1798677
  have hstable : (prefixWord ++ tailWord_1798677).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798677).length < 2 ^ (prefixWord ++ tailWord_1798677).sum := by decide
  have hdescent : baseEnd_1798677 < baseStart_1798677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1798680 : List Nat := [2, 1, 2, 3, 3, 3, 1, 1, 5]
def baseStart_1798680 : Nat := 118140960795 + 1798680 * 2 ^ 59
def prefixEnd_1798680 : Nat := 4983230072969 + 3 ^ 40 * 1798680 * 2
def baseEnd_1798680 : Nat := 410483281612945728856901

theorem tailTrace_1798680 : CollatzResearch.WordTrace tailWord_1798680 prefixEnd_1798680 410483281612945728856901 := by
  unfold tailWord_1798680
  simp only [CollatzResearch.WordTrace]
  refine ⟨32801624561848512466228747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43735499415798016621638329 32801624561848512466228747)
  ·
    refine ⟨49202436842772768699343121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32801624561848512466228747 49202436842772768699343121)
    ·
      refine ⟨36901827632079576524507341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49202436842772768699343121 36901827632079576524507341)
      ·
        refine ⟨13838185362029841196690253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36901827632079576524507341 13838185362029841196690253)
        ·
          refine ⟨5189319510761190448758845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13838185362029841196690253 5189319510761190448758845)
          ·
            refine ⟨1945994816535446418284567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5189319510761190448758845 1945994816535446418284567)
            ·
              refine ⟨2918992224803169627426851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1945994816535446418284567 2918992224803169627426851)
              ·
                refine ⟨4378488337204754441140277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2918992224803169627426851 4378488337204754441140277)
                ·
                  refine ⟨410483281612945728856901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4378488337204754441140277 410483281612945728856901)
                  ·
                    rfl

theorem cell21_1798680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 1, 5].length) (baseStart_1798680 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1798680 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1798680 prefixEnd_1798680 := by exact prefixLift 1798680
  have htrace : WordTrace (prefixWord ++ tailWord_1798680) baseStart_1798680 baseEnd_1798680 := by
    simpa [prefixWord, tailWord_1798680, baseEnd_1798680] using wordTrace_append hprefix tailTrace_1798680
  have hstable : (prefixWord ++ tailWord_1798680).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798680).length < 2 ^ (prefixWord ++ tailWord_1798680).sum := by decide
  have hdescent : baseEnd_1798680 < baseStart_1798680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1798767 : List Nat := [1, 1, 2, 1, 3, 2, 2, 9]
def baseStart_1798767 : Nat := 118140960795 + 1798767 * 2 ^ 59
def prefixEnd_1798767 : Nat := 4983230072969 + 3 ^ 40 * 1798767 * 2
def baseEnd_1798767 : Nat := 136834378732750970302241

theorem tailTrace_1798767 : CollatzResearch.WordTrace tailWord_1798767 prefixEnd_1798767 136834378732750970302241 := by
  unfold tailWord_1798767
  simp only [CollatzResearch.WordTrace]
  refine ⟨65606422274381838790874555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43737614849587892527249703 65606422274381838790874555)
  ·
    refine ⟨98409633411572758186311833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65606422274381838790874555 98409633411572758186311833)
    ·
      refine ⟨73807225058679568639733875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98409633411572758186311833 73807225058679568639733875)
      ·
        refine ⟨110710837588019352959600813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73807225058679568639733875 110710837588019352959600813)
        ·
          refine ⟨41516564095507257359850305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110710837588019352959600813 41516564095507257359850305)
          ·
            refine ⟨31137423071630443019887729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41516564095507257359850305 31137423071630443019887729)
            ·
              refine ⟨23353067303722832264915797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31137423071630443019887729 23353067303722832264915797)
              ·
                refine ⟨136834378732750970302241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23353067303722832264915797 136834378732750970302241)
                ·
                  rfl

theorem cell21_1798767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 9].length) (baseStart_1798767 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1798767 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1798767 prefixEnd_1798767 := by exact prefixLift 1798767
  have htrace : WordTrace (prefixWord ++ tailWord_1798767) baseStart_1798767 baseEnd_1798767 := by
    simpa [prefixWord, tailWord_1798767, baseEnd_1798767] using wordTrace_append hprefix tailTrace_1798767
  have hstable : (prefixWord ++ tailWord_1798767).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798767).length < 2 ^ (prefixWord ++ tailWord_1798767).sum := by decide
  have hdescent : baseEnd_1798767 < baseStart_1798767 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1798804 : List Nat := [2, 4, 2, 2, 1, 2, 3, 1, 4]
def baseStart_1798804 : Nat := 118140960795 + 1798804 * 2 ^ 59
def prefixEnd_1798804 : Nat := 4983230072969 + 3 ^ 40 * 1798804 * 2
def baseEnd_1798804 : Nat := 410511580102349068789981

theorem tailTrace_1798804 : CollatzResearch.WordTrace tailWord_1798804 prefixEnd_1798804 410511580102349068789981 := by
  unfold tailWord_1798804
  simp only [CollatzResearch.WordTrace]
  refine ⟨32803885887623897054985733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43738514516831862739980977 32803885887623897054985733)
  ·
    refine ⟨6150728603929480697809825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32803885887623897054985733 6150728603929480697809825)
    ·
      refine ⟨4613046452947110523357369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6150728603929480697809825 4613046452947110523357369)
      ·
        refine ⟨3459784839710332892518027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4613046452947110523357369 3459784839710332892518027)
        ·
          refine ⟨5189677259565499338777041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3459784839710332892518027 5189677259565499338777041)
          ·
            refine ⟨3892257944674124504082781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5189677259565499338777041 3892257944674124504082781)
            ·
              refine ⟨1459596729252796689031043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3892257944674124504082781 1459596729252796689031043)
              ·
                refine ⟨2189395093879195033546565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1459596729252796689031043 2189395093879195033546565)
                ·
                  refine ⟨410511580102349068789981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2189395093879195033546565 410511580102349068789981)
                  ·
                    rfl

theorem cell21_1798804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 3, 1, 4].length) (baseStart_1798804 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1798804 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1798804 prefixEnd_1798804 := by exact prefixLift 1798804
  have htrace : WordTrace (prefixWord ++ tailWord_1798804) baseStart_1798804 baseEnd_1798804 := by
    simpa [prefixWord, tailWord_1798804, baseEnd_1798804] using wordTrace_append hprefix tailTrace_1798804
  have hstable : (prefixWord ++ tailWord_1798804).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798804).length < 2 ^ (prefixWord ++ tailWord_1798804).sum := by decide
  have hdescent : baseEnd_1798804 < baseStart_1798804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1798846 : List Nat := [4, 2, 1, 1, 2, 1, 2, 4, 4]
def baseStart_1798846 : Nat := 118140960795 + 1798846 * 2 ^ 59
def prefixEnd_1798846 : Nat := 4983230072969 + 3 ^ 40 * 1798846 * 2
def baseEnd_1798846 : Nat := 410521165074566329089895

theorem tailTrace_1798846 : CollatzResearch.WordTrace tailWord_1798846 prefixEnd_1798846 410521165074566329089895 := by
  unfold tailWord_1798846
  simp only [CollatzResearch.WordTrace]
  refine ⟨8201162955136954410375049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43739535760730423522000261 8201162955136954410375049)
  ·
    refine ⟨6150872216352715807781287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8201162955136954410375049 6150872216352715807781287)
    ·
      refine ⟨9226308324529073711671931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6150872216352715807781287 9226308324529073711671931)
      ·
        refine ⟨13839462486793610567507897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9226308324529073711671931 13839462486793610567507897)
        ·
          refine ⟨10379596865095207925630923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13839462486793610567507897 10379596865095207925630923)
          ·
            refine ⟨15569395297642811888446385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10379596865095207925630923 15569395297642811888446385)
            ·
              refine ⟨11677046473232108916334789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15569395297642811888446385 11677046473232108916334789)
              ·
                refine ⟨2189446213731020421812773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11677046473232108916334789 2189446213731020421812773)
                ·
                  refine ⟨410521165074566329089895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2189446213731020421812773 410521165074566329089895)
                  ·
                    rfl

theorem cell21_1798846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 4, 4].length) (baseStart_1798846 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1798846 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1798846 prefixEnd_1798846 := by exact prefixLift 1798846
  have htrace : WordTrace (prefixWord ++ tailWord_1798846) baseStart_1798846 baseEnd_1798846 := by
    simpa [prefixWord, tailWord_1798846, baseEnd_1798846] using wordTrace_append hprefix tailTrace_1798846
  have hstable : (prefixWord ++ tailWord_1798846).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798846).length < 2 ^ (prefixWord ++ tailWord_1798846).sum := by decide
  have hdescent : baseEnd_1798846 < baseStart_1798846 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1798860 : List Nat := [2, 2, 1, 5, 1, 1, 1, 8]
def baseStart_1798860 : Nat := 118140960795 + 1798860 * 2 ^ 59
def prefixEnd_1798860 : Nat := 4983230072969 + 3 ^ 40 * 1798860 * 2
def baseEnd_1798860 : Nat := 136841453355101805285511

theorem tailTrace_1798860 : CollatzResearch.WordTrace tailWord_1798860 prefixEnd_1798860 136841453355101805285511 := by
  unfold tailWord_1798860
  simp only [CollatzResearch.WordTrace]
  refine ⟨32804907131522457837005017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43739876175363277116006689 32804907131522457837005017)
  ·
    refine ⟨24603680348641843377753763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32804907131522457837005017 24603680348641843377753763)
    ·
      refine ⟨36905520522962765066630645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24603680348641843377753763 36905520522962765066630645)
      ·
        refine ⟨3459892549027759224996623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36905520522962765066630645 3459892549027759224996623)
        ·
          refine ⟨5189838823541638837494935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3459892549027759224996623 5189838823541638837494935)
          ·
            refine ⟨7784758235312458256242403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5189838823541638837494935 7784758235312458256242403)
            ·
              refine ⟨11677137352968687384363605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7784758235312458256242403 11677137352968687384363605)
              ·
                refine ⟨136841453355101805285511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11677137352968687384363605 136841453355101805285511)
                ·
                  rfl

theorem cell21_1798860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 8].length) (baseStart_1798860 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1798860 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1798860 prefixEnd_1798860 := by exact prefixLift 1798860
  have htrace : WordTrace (prefixWord ++ tailWord_1798860) baseStart_1798860 baseEnd_1798860 := by
    simpa [prefixWord, tailWord_1798860, baseEnd_1798860] using wordTrace_append hprefix tailTrace_1798860
  have hstable : (prefixWord ++ tailWord_1798860).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798860).length < 2 ^ (prefixWord ++ tailWord_1798860).sum := by decide
  have hdescent : baseEnd_1798860 < baseStart_1798860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1798874 : List Nat := [3, 1, 1, 2, 2, 2, 2, 1, 7]
def baseStart_1798874 : Nat := 118140960795 + 1798874 * 2 ^ 59
def prefixEnd_1798874 : Nat := 4983230072969 + 3 ^ 40 * 1798874 * 2
def baseEnd_1798874 : Nat := 410527555056044502623171

theorem tailTrace_1798874 : CollatzResearch.WordTrace tailWord_1798874 prefixEnd_1798874 410527555056044502623171 := by
  unfold tailWord_1798874
  simp only [CollatzResearch.WordTrace]
  refine ⟨16402581221248549016254919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43740216589996130710013117 16402581221248549016254919)
  ·
    refine ⟨24603871831872823524382379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16402581221248549016254919 24603871831872823524382379)
    ·
      refine ⟨36905807747809235286573569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24603871831872823524382379 36905807747809235286573569)
      ·
        refine ⟨27679355810856926464930177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36905807747809235286573569 27679355810856926464930177)
        ·
          refine ⟨20759516858142694848697633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27679355810856926464930177 20759516858142694848697633)
          ·
            refine ⟨15569637643607021136523225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20759516858142694848697633 15569637643607021136523225)
            ·
              refine ⟨11677228232705265852392419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15569637643607021136523225 11677228232705265852392419)
              ·
                refine ⟨17515842349057898778588629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11677228232705265852392419 17515842349057898778588629)
                ·
                  refine ⟨410527555056044502623171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17515842349057898778588629 410527555056044502623171)
                  ·
                    rfl

theorem cell21_1798874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 1, 7].length) (baseStart_1798874 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1798874 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1798874 prefixEnd_1798874 := by exact prefixLift 1798874
  have htrace : WordTrace (prefixWord ++ tailWord_1798874) baseStart_1798874 baseEnd_1798874 := by
    simpa [prefixWord, tailWord_1798874, baseEnd_1798874] using wordTrace_append hprefix tailTrace_1798874
  have hstable : (prefixWord ++ tailWord_1798874).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798874).length < 2 ^ (prefixWord ++ tailWord_1798874).sum := by decide
  have hdescent : baseEnd_1798874 < baseStart_1798874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1798891 : List Nat := [1, 1, 1, 1, 2, 4, 1, 7, 3]
def baseStart_1798891 : Nat := 118140960795 + 1798891 * 2 ^ 59
def prefixEnd_1798891 : Nat := 4983230072969 + 3 ^ 40 * 1798891 * 2
def baseEnd_1798891 : Nat := 410531434687656250839803

theorem tailTrace_1798891 : CollatzResearch.WordTrace tailWord_1798891 prefixEnd_1798891 410531434687656250839803 := by
  unfold tailWord_1798891
  simp only [CollatzResearch.WordTrace]
  refine ⟨65610944925932607968388527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43740629950621738645592351 65610944925932607968388527)
  ·
    refine ⟨98416417388898911952582791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65610944925932607968388527 98416417388898911952582791)
    ·
      refine ⟨147624626083348367928874187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98416417388898911952582791 147624626083348367928874187)
      ·
        refine ⟨221436939125022551893311281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147624626083348367928874187 221436939125022551893311281)
        ·
          refine ⟨166077704343766913919983461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 221436939125022551893311281 166077704343766913919983461)
          ·
            refine ⟨31139569564456296359996899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 166077704343766913919983461 31139569564456296359996899)
            ·
              refine ⟨46709354346684444539995349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31139569564456296359996899 46709354346684444539995349)
              ·
                refine ⟨1094750492500416668906141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 46709354346684444539995349 1094750492500416668906141)
                ·
                  refine ⟨410531434687656250839803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1094750492500416668906141 410531434687656250839803)
                  ·
                    rfl

theorem cell21_1798891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 7, 3].length) (baseStart_1798891 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1798891 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1798891 prefixEnd_1798891 := by exact prefixLift 1798891
  have htrace : WordTrace (prefixWord ++ tailWord_1798891) baseStart_1798891 baseEnd_1798891 := by
    simpa [prefixWord, tailWord_1798891, baseEnd_1798891] using wordTrace_append hprefix tailTrace_1798891
  have hstable : (prefixWord ++ tailWord_1798891).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798891).length < 2 ^ (prefixWord ++ tailWord_1798891).sum := by decide
  have hdescent : baseEnd_1798891 < baseStart_1798891 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1798900 : List Nat := [2, 6, 1, 1, 2, 2, 2, 2, 3]
def baseStart_1798900 : Nat := 118140960795 + 1798900 * 2 ^ 59
def prefixEnd_1798900 : Nat := 4983230072969 + 3 ^ 40 * 1798900 * 2
def baseEnd_1798900 : Nat := 410533488610274235189785

theorem tailTrace_1798900 : CollatzResearch.WordTrace tailWord_1798900 prefixEnd_1798900 410533488610274235189785 := by
  unfold tailWord_1798900
  simp only [CollatzResearch.WordTrace]
  refine ⟨32805636591450001252733077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43740848788600001670310769 32805636591450001252733077)
  ·
    refine ⟨1537764215224218808721863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 32805636591450001252733077 1537764215224218808721863)
    ·
      refine ⟨2306646322836328213082795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1537764215224218808721863 2306646322836328213082795)
      ·
        refine ⟨3459969484254492319624193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2306646322836328213082795 3459969484254492319624193)
        ·
          refine ⟨2594977113190869239718145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3459969484254492319624193 2594977113190869239718145)
          ·
            refine ⟨1946232834893151929788609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2594977113190869239718145 1946232834893151929788609)
            ·
              refine ⟨1459674626169863947341457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1946232834893151929788609 1459674626169863947341457)
              ·
                refine ⟨1094755969627397960506093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1459674626169863947341457 1094755969627397960506093)
                ·
                  refine ⟨410533488610274235189785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1094755969627397960506093 410533488610274235189785)
                  ·
                    rfl

theorem cell21_1798900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_1798900 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1798900 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1798900 prefixEnd_1798900 := by exact prefixLift 1798900
  have htrace : WordTrace (prefixWord ++ tailWord_1798900) baseStart_1798900 baseEnd_1798900 := by
    simpa [prefixWord, tailWord_1798900, baseEnd_1798900] using wordTrace_append hprefix tailTrace_1798900
  have hstable : (prefixWord ++ tailWord_1798900).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798900).length < 2 ^ (prefixWord ++ tailWord_1798900).sum := by decide
  have hdescent : baseEnd_1798900 < baseStart_1798900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1798908 : List Nat := [2, 2, 2, 1, 3, 3, 1, 4, 3]
def baseStart_1798908 : Nat := 118140960795 + 1798908 * 2 ^ 59
def prefixEnd_1798908 : Nat := 4983230072969 + 3 ^ 40 * 1798908 * 2
def baseEnd_1798908 : Nat := 410535314319267999056435

theorem tailTrace_1798908 : CollatzResearch.WordTrace tailWord_1798908 prefixEnd_1798908 410535314319267999056435 := by
  unfold tailWord_1798908
  simp only [CollatzResearch.WordTrace]
  refine ⟨32805782483435509935878689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43741043311247346581171585 32805782483435509935878689)
  ·
    refine ⟨24604336862576632451909017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32805782483435509935878689 24604336862576632451909017)
    ·
      refine ⟨18453252646932474338931763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24604336862576632451909017 18453252646932474338931763)
      ·
        refine ⟨27679878970398711508397645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18453252646932474338931763 27679878970398711508397645)
        ·
          refine ⟨10379954613899516815649117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27679878970398711508397645 10379954613899516815649117)
          ·
            refine ⟨3892482980212318805868419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10379954613899516815649117 3892482980212318805868419)
            ·
              refine ⟨5838724470318478208802629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3892482980212318805868419 5838724470318478208802629)
              ·
                refine ⟨1094760838184714664150493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5838724470318478208802629 1094760838184714664150493)
                ·
                  refine ⟨410535314319267999056435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1094760838184714664150493 410535314319267999056435)
                  ·
                    rfl

theorem cell21_1798908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 4, 3].length) (baseStart_1798908 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1798908 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1798908 prefixEnd_1798908 := by exact prefixLift 1798908
  have htrace : WordTrace (prefixWord ++ tailWord_1798908) baseStart_1798908 baseEnd_1798908 := by
    simpa [prefixWord, tailWord_1798908, baseEnd_1798908] using wordTrace_append hprefix tailTrace_1798908
  have hstable : (prefixWord ++ tailWord_1798908).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798908).length < 2 ^ (prefixWord ++ tailWord_1798908).sum := by decide
  have hdescent : baseEnd_1798908 < baseStart_1798908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1798967 : List Nat := [1, 1, 3, 1, 2, 1, 3, 6, 3]
def baseStart_1798967 : Nat := 118140960795 + 1798967 * 2 ^ 59
def prefixEnd_1798967 : Nat := 4983230072969 + 3 ^ 40 * 1798967 * 2
def baseEnd_1798967 : Nat := 410548778923097007572981

theorem tailTrace_1798967 : CollatzResearch.WordTrace tailWord_1798967 prefixEnd_1798967 410548778923097007572981 := by
  unfold tailWord_1798967
  simp only [CollatzResearch.WordTrace]
  refine ⟨65613716873657272948155155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43742477915771515298770103 65613716873657272948155155)
  ·
    refine ⟨98420575310485909422232733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65613716873657272948155155 98420575310485909422232733)
    ·
      refine ⟨36907715741432216033337275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98420575310485909422232733 36907715741432216033337275)
      ·
        refine ⟨55361573612148324050005913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36907715741432216033337275 55361573612148324050005913)
        ·
          refine ⟨41521180209111243037504435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55361573612148324050005913 41521180209111243037504435)
          ·
            refine ⟨62281770313666864556256653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41521180209111243037504435 62281770313666864556256653)
            ·
              refine ⟨23355663867625074208596245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62281770313666864556256653 23355663867625074208596245)
              ·
                refine ⟨1094796743794925353527949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 23355663867625074208596245 1094796743794925353527949)
                ·
                  refine ⟨410548778923097007572981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1094796743794925353527949 410548778923097007572981)
                  ·
                    rfl

theorem cell21_1798967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 6, 3].length) (baseStart_1798967 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1798967 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1798967 prefixEnd_1798967 := by exact prefixLift 1798967
  have htrace : WordTrace (prefixWord ++ tailWord_1798967) baseStart_1798967 baseEnd_1798967 := by
    simpa [prefixWord, tailWord_1798967, baseEnd_1798967] using wordTrace_append hprefix tailTrace_1798967
  have hstable : (prefixWord ++ tailWord_1798967).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798967).length < 2 ^ (prefixWord ++ tailWord_1798967).sum := by decide
  have hdescent : baseEnd_1798967 < baseStart_1798967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799012 : List Nat := [2, 3, 1, 1, 4, 3, 7]
def baseStart_1799012 : Nat := 118140960795 + 1799012 * 2 ^ 59
def prefixEnd_1799012 : Nat := 4983230072969 + 3 ^ 40 * 1799012 * 2
def baseEnd_1799012 : Nat := 45617672059576325480321

theorem tailTrace_1799012 : CollatzResearch.WordTrace tailWord_1799012 prefixEnd_1799012 45617672059576325480321 := by
  unfold tailWord_1799012
  simp only [CollatzResearch.WordTrace]
  refine ⟨32807679079247122816771645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43743572105662830422362193 32807679079247122816771645)
  ·
    refine ⟨12302879654717671056289367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32807679079247122816771645 12302879654717671056289367)
    ·
      refine ⟨18454319482076506584434051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12302879654717671056289367 18454319482076506584434051)
      ·
        refine ⟨27681479223114759876651077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18454319482076506584434051 27681479223114759876651077)
        ·
          refine ⟨5190277354334017476872077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27681479223114759876651077 5190277354334017476872077)
          ·
            refine ⟨1946354007875256553827029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5190277354334017476872077 1946354007875256553827029)
            ·
              refine ⟨45617672059576325480321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1946354007875256553827029 45617672059576325480321)
              ·
                rfl

theorem cell21_1799012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 7].length) (baseStart_1799012 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1799012 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1799012 prefixEnd_1799012 := by exact prefixLift 1799012
  have htrace : WordTrace (prefixWord ++ tailWord_1799012) baseStart_1799012 baseEnd_1799012 := by
    simpa [prefixWord, tailWord_1799012, baseEnd_1799012] using wordTrace_append hprefix tailTrace_1799012
  have hstable : (prefixWord ++ tailWord_1799012).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799012).length < 2 ^ (prefixWord ++ tailWord_1799012).sum := by decide
  have hdescent : baseEnd_1799012 < baseStart_1799012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799040 : List Nat := [2, 1, 1, 2, 1, 2, 2, 2, 8]
def baseStart_1799040 : Nat := 118140960795 + 1799040 * 2 ^ 59
def prefixEnd_1799040 : Nat := 4983230072969 + 3 ^ 40 * 1799040 * 2
def baseEnd_1799040 : Nat := 410565438517665102856165

theorem tailTrace_1799040 : CollatzResearch.WordTrace tailWord_1799040 prefixEnd_1799040 410565438517665102856165 := by
  unfold tailWord_1799040
  simp only [CollatzResearch.WordTrace]
  refine ⟨32808189701196403207781287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43744252934928537610375049 32808189701196403207781287)
  ·
    refine ⟨49212284551794604811671931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32808189701196403207781287 49212284551794604811671931)
    ·
      refine ⟨73818426827691907217507897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49212284551794604811671931 73818426827691907217507897)
      ·
        refine ⟨55363820120768930413130923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73818426827691907217507897 55363820120768930413130923)
        ·
          refine ⟨83045730181153395619696385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55363820120768930413130923 83045730181153395619696385)
          ·
            refine ⟨62284297635865046714772289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83045730181153395619696385 62284297635865046714772289)
            ·
              refine ⟨46713223226898785036079217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62284297635865046714772289 46713223226898785036079217)
              ·
                refine ⟨35034917420174088777059413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46713223226898785036079217 35034917420174088777059413)
                ·
                  refine ⟨410565438517665102856165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35034917420174088777059413 410565438517665102856165)
                  ·
                    rfl

theorem cell21_1799040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 8].length) (baseStart_1799040 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1799040 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1799040 prefixEnd_1799040 := by exact prefixLift 1799040
  have htrace : WordTrace (prefixWord ++ tailWord_1799040) baseStart_1799040 baseEnd_1799040 := by
    simpa [prefixWord, tailWord_1799040, baseEnd_1799040] using wordTrace_append hprefix tailTrace_1799040
  have hstable : (prefixWord ++ tailWord_1799040).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799040).length < 2 ^ (prefixWord ++ tailWord_1799040).sum := by decide
  have hdescent : baseEnd_1799040 < baseStart_1799040 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799060 : List Nat := [2, 4, 2, 1, 1, 1, 2, 5, 3]
def baseStart_1799060 : Nat := 118140960795 + 1799060 * 2 ^ 59
def prefixEnd_1799060 : Nat := 4983230072969 + 3 ^ 40 * 1799060 * 2
def baseEnd_1799060 : Nat := 410570002790149512522791

theorem tailTrace_1799060 : CollatzResearch.WordTrace tailWord_1799060 prefixEnd_1799060 410570002790149512522791 := by
  unfold tailWord_1799060
  simp only [CollatzResearch.WordTrace]
  refine ⟨32808554431160174915645317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43744739241546899887527089 32808554431160174915645317)
  ·
    refine ⟨6151603955842532796683497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32808554431160174915645317 6151603955842532796683497)
    ·
      refine ⟨4613702966881899597512623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6151603955842532796683497 4613702966881899597512623)
      ·
        refine ⟨6920554450322849396268935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4613702966881899597512623 6920554450322849396268935)
        ·
          refine ⟨10380831675484274094403403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6920554450322849396268935 10380831675484274094403403)
          ·
            refine ⟨15571247513226411141605105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10380831675484274094403403 15571247513226411141605105)
            ·
              refine ⟨11678435634919808356203829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15571247513226411141605105 11678435634919808356203829)
              ·
                refine ⟨1094853340773732033394109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11678435634919808356203829 1094853340773732033394109)
                ·
                  refine ⟨410570002790149512522791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1094853340773732033394109 410570002790149512522791)
                  ·
                    rfl

theorem cell21_1799060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 5, 3].length) (baseStart_1799060 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1799060 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1799060 prefixEnd_1799060 := by exact prefixLift 1799060
  have htrace : WordTrace (prefixWord ++ tailWord_1799060) baseStart_1799060 baseEnd_1799060 := by
    simpa [prefixWord, tailWord_1799060, baseEnd_1799060] using wordTrace_append hprefix tailTrace_1799060
  have hstable : (prefixWord ++ tailWord_1799060).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799060).length < 2 ^ (prefixWord ++ tailWord_1799060).sum := by decide
  have hdescent : baseEnd_1799060 < baseStart_1799060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799071 : List Nat := [1, 1, 2, 5, 2, 10]
def baseStart_1799071 : Nat := 118140960795 + 1799071 * 2 ^ 59
def prefixEnd_1799071 : Nat := 4983230072969 + 3 ^ 40 * 1799071 * 2
def baseEnd_1799071 : Nat := 15206389375556145845905

theorem tailTrace_1799071 : CollatzResearch.WordTrace tailWord_1799071 prefixEnd_1799071 15206389375556145845905 := by
  unfold tailWord_1799071
  simp only [CollatzResearch.WordTrace]
  refine ⟨65617510065280498709941067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43745006710186999139960711 65617510065280498709941067)
  ·
    refine ⟨98426265097920748064911601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65617510065280498709941067 98426265097920748064911601)
    ·
      refine ⟨73819698823440561048683701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98426265097920748064911601 73819698823440561048683701)
      ·
        refine ⟨6920596764697552598314097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 73819698823440561048683701 6920596764697552598314097)
        ·
          refine ⟨5190447573523164448735573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6920596764697552598314097 5190447573523164448735573)
          ·
            refine ⟨15206389375556145845905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5190447573523164448735573 15206389375556145845905)
            ·
              rfl

theorem cell21_1799071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 10].length) (baseStart_1799071 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1799071 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1799071 prefixEnd_1799071 := by exact prefixLift 1799071
  have htrace : WordTrace (prefixWord ++ tailWord_1799071) baseStart_1799071 baseEnd_1799071 := by
    simpa [prefixWord, tailWord_1799071, baseEnd_1799071] using wordTrace_append hprefix tailTrace_1799071
  have hstable : (prefixWord ++ tailWord_1799071).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799071).length < 2 ^ (prefixWord ++ tailWord_1799071).sum := by decide
  have hdescent : baseEnd_1799071 < baseStart_1799071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799074 : List Nat := [3, 3, 1, 2, 2, 1, 1, 4, 4]
def baseStart_1799074 : Nat := 118140960795 + 1799074 * 2 ^ 59
def prefixEnd_1799074 : Nat := 4983230072969 + 3 ^ 40 * 1799074 * 2
def baseEnd_1799074 : Nat := 410573197780888599289429

theorem tailTrace_1799074 : CollatzResearch.WordTrace tailWord_1799074 prefixEnd_1799074 410573197780888599289429 := by
  unfold tailWord_1799074
  simp only [CollatzResearch.WordTrace]
  refine ⟨16404404871067407555575069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43745079656179753481533517 16404404871067407555575069)
  ·
    refine ⟨6151651826650277833340651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16404404871067407555575069 6151651826650277833340651)
    ·
      refine ⟨9227477739975416750010977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6151651826650277833340651 9227477739975416750010977)
      ·
        refine ⟨6920608304981562562508233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9227477739975416750010977 6920608304981562562508233)
        ·
          refine ⟨5190456228736171921881175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6920608304981562562508233 5190456228736171921881175)
          ·
            refine ⟨7785684343104257882821763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5190456228736171921881175 7785684343104257882821763)
            ·
              refine ⟨11678526514656386824232645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7785684343104257882821763 11678526514656386824232645)
              ·
                refine ⟨2189723721498072529543621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11678526514656386824232645 2189723721498072529543621)
                ·
                  refine ⟨410573197780888599289429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2189723721498072529543621 410573197780888599289429)
                  ·
                    rfl

theorem cell21_1799074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 4, 4].length) (baseStart_1799074 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1799074 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1799074 prefixEnd_1799074 := by exact prefixLift 1799074
  have htrace : WordTrace (prefixWord ++ tailWord_1799074) baseStart_1799074 baseEnd_1799074 := by
    simpa [prefixWord, tailWord_1799074, baseEnd_1799074] using wordTrace_append hprefix tailTrace_1799074
  have hstable : (prefixWord ++ tailWord_1799074).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799074).length < 2 ^ (prefixWord ++ tailWord_1799074).sum := by decide
  have hdescent : baseEnd_1799074 < baseStart_1799074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799094 : List Nat := [5, 1, 4, 1, 1, 1, 1, 2, 5]
def baseStart_1799094 : Nat := 118140960795 + 1799094 * 2 ^ 59
def prefixEnd_1799094 : Nat := 4983230072969 + 3 ^ 40 * 1799094 * 2
def baseEnd_1799094 : Nat := 410577762053373008956055

theorem tailTrace_1799094 : CollatzResearch.WordTrace tailWord_1799094 prefixEnd_1799094 410577762053373008956055 := by
  unfold tailWord_1799094
  simp only [CollatzResearch.WordTrace]
  refine ⟨4101146809012323352376771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43745565962798115758685557 4101146809012323352376771)
  ·
    refine ⟨6151720213518485028565157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4101146809012323352376771 6151720213518485028565157)
    ·
      refine ⟨1153447540034715942855967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6151720213518485028565157 1153447540034715942855967)
      ·
        refine ⟨1730171310052073914283951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1153447540034715942855967 1730171310052073914283951)
        ·
          refine ⟨2595256965078110871425927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1730171310052073914283951 2595256965078110871425927)
          ·
            refine ⟨3892885447617166307138891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2595256965078110871425927 3892885447617166307138891)
            ·
              refine ⟨5839328171425749460708337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3892885447617166307138891 5839328171425749460708337)
              ·
                refine ⟨4379496128569312095531253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5839328171425749460708337 4379496128569312095531253)
                ·
                  refine ⟨410577762053373008956055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4379496128569312095531253 410577762053373008956055)
                  ·
                    rfl

theorem cell21_1799094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 2, 5].length) (baseStart_1799094 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1799094 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1799094 prefixEnd_1799094 := by exact prefixLift 1799094
  have htrace : WordTrace (prefixWord ++ tailWord_1799094) baseStart_1799094 baseEnd_1799094 := by
    simpa [prefixWord, tailWord_1799094, baseEnd_1799094] using wordTrace_append hprefix tailTrace_1799094
  have hstable : (prefixWord ++ tailWord_1799094).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799094).length < 2 ^ (prefixWord ++ tailWord_1799094).sum := by decide
  have hdescent : baseEnd_1799094 < baseStart_1799094 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799119 : List Nat := [1, 1, 2, 1, 1, 6, 1, 5, 3]
def baseStart_1799119 : Nat := 118140960795 + 1799119 * 2 ^ 59
def prefixEnd_1799119 : Nat := 4983230072969 + 3 ^ 40 * 1799119 * 2
def baseEnd_1799119 : Nat := 410583467393978521039337

theorem tailTrace_1799119 : CollatzResearch.WordTrace tailWord_1799119 prefixEnd_1799119 410583467393978521039337 := by
  unfold tailWord_1799119
  simp only [CollatzResearch.WordTrace]
  refine ⟨65619260769106602907688411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43746173846071068605125607 65619260769106602907688411)
  ·
    refine ⟨98428891153659904361532617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65619260769106602907688411 98428891153659904361532617)
    ·
      refine ⟨73821668365244928271149463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98428891153659904361532617 73821668365244928271149463)
      ·
        refine ⟨110732502547867392406724195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73821668365244928271149463 110732502547867392406724195)
        ·
          refine ⟨166098753821801088610086293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110732502547867392406724195 166098753821801088610086293)
          ·
            refine ⟨7785879085396926028597795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 166098753821801088610086293 7785879085396926028597795)
            ·
              refine ⟨11678818628095389042896693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7785879085396926028597795 11678818628095389042896693)
              ·
                refine ⟨1094889246383942722771565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11678818628095389042896693 1094889246383942722771565)
                ·
                  refine ⟨410583467393978521039337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1094889246383942722771565 410583467393978521039337)
                  ·
                    rfl

theorem cell21_1799119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 5, 3].length) (baseStart_1799119 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1799119 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1799119 prefixEnd_1799119 := by exact prefixLift 1799119
  have htrace : WordTrace (prefixWord ++ tailWord_1799119) baseStart_1799119 baseEnd_1799119 := by
    simpa [prefixWord, tailWord_1799119, baseEnd_1799119] using wordTrace_append hprefix tailTrace_1799119
  have hstable : (prefixWord ++ tailWord_1799119).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799119).length < 2 ^ (prefixWord ++ tailWord_1799119).sum := by decide
  have hdescent : baseEnd_1799119 < baseStart_1799119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799164 : List Nat := [2, 2, 2, 1, 2, 3, 4, 5]
def baseStart_1799164 : Nat := 118140960795 + 1799164 * 2 ^ 59
def prefixEnd_1799164 : Nat := 4983230072969 + 3 ^ 40 * 1799164 * 2
def baseEnd_1799164 : Nat := 136864579002356147596415

theorem tailTrace_1799164 : CollatzResearch.WordTrace tailWord_1799164 prefixEnd_1799164 136864579002356147596415 := by
  unfold tailWord_1799164
  simp only [CollatzResearch.WordTrace]
  refine ⟨32810451026971787796538273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43747268035962383728717697 32810451026971787796538273)
  ·
    refine ⟨24607838270228840847403705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32810451026971787796538273 24607838270228840847403705)
    ·
      refine ⟨18455878702671630635552779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24607838270228840847403705 18455878702671630635552779)
      ·
        refine ⟨27683818054007445953329169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18455878702671630635552779 27683818054007445953329169)
        ·
          refine ⟨20762863540505584464996877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27683818054007445953329169 20762863540505584464996877)
          ·
            refine ⟨7786073827689594174373829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20762863540505584464996877 7786073827689594174373829)
            ·
              refine ⟨1459888842691798907695093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7786073827689594174373829 1459888842691798907695093)
              ·
                refine ⟨136864579002356147596415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1459888842691798907695093 136864579002356147596415)
                ·
                  rfl

theorem cell21_1799164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 4, 5].length) (baseStart_1799164 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1799164 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1799164 prefixEnd_1799164 := by exact prefixLift 1799164
  have htrace : WordTrace (prefixWord ++ tailWord_1799164) baseStart_1799164 baseEnd_1799164 := by
    simpa [prefixWord, tailWord_1799164, baseEnd_1799164] using wordTrace_append hprefix tailTrace_1799164
  have hstable : (prefixWord ++ tailWord_1799164).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799164).length < 2 ^ (prefixWord ++ tailWord_1799164).sum := by decide
  have hdescent : baseEnd_1799164 < baseStart_1799164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799268 : List Nat := [2, 3, 1, 1, 2, 1, 1, 2, 8]
def baseStart_1799268 : Nat := 118140960795 + 1799268 * 2 ^ 59
def prefixEnd_1799268 : Nat := 4983230072969 + 3 ^ 40 * 1799268 * 2
def baseEnd_1799268 : Nat := 410617471223987373055699

theorem tailTrace_1799268 : CollatzResearch.WordTrace tailWord_1799268 prefixEnd_1799268 410617471223987373055699 := by
  unfold tailWord_1799268
  simp only [CollatzResearch.WordTrace]
  refine ⟨32812347622783400677431229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43749796830377867569908305 32812347622783400677431229)
  ·
    refine ⟨12304630358543775254036711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32812347622783400677431229 12304630358543775254036711)
    ·
      refine ⟨18456945537815662881055067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12304630358543775254036711 18456945537815662881055067)
      ·
        refine ⟨27685418306723494321582601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18456945537815662881055067 27685418306723494321582601)
        ·
          refine ⟨20764063730042620741186951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27685418306723494321582601 20764063730042620741186951)
          ·
            refine ⟨31146095595063931111780427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20764063730042620741186951 31146095595063931111780427)
            ·
              refine ⟨46719143392595896667670641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31146095595063931111780427 46719143392595896667670641)
              ·
                refine ⟨35039357544446922500752981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46719143392595896667670641 35039357544446922500752981)
                ·
                  refine ⟨410617471223987373055699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35039357544446922500752981 410617471223987373055699)
                  ·
                    rfl

theorem cell21_1799268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 8].length) (baseStart_1799268 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1799268 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1799268 prefixEnd_1799268 := by exact prefixLift 1799268
  have htrace : WordTrace (prefixWord ++ tailWord_1799268) baseStart_1799268 baseEnd_1799268 := by
    simpa [prefixWord, tailWord_1799268, baseEnd_1799268] using wordTrace_append hprefix tailTrace_1799268
  have hstable : (prefixWord ++ tailWord_1799268).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799268).length < 2 ^ (prefixWord ++ tailWord_1799268).sum := by decide
  have hdescent : baseEnd_1799268 < baseStart_1799268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799294 : List Nat := [4, 2, 4, 1, 2, 1, 1, 2, 4]
def baseStart_1799294 : Nat := 118140960795 + 1799294 * 2 ^ 59
def prefixEnd_1799294 : Nat := 4983230072969 + 3 ^ 40 * 1799294 * 2
def baseEnd_1799294 : Nat := 410623404778217105622313

theorem tailTrace_1799294 : CollatzResearch.WordTrace tailWord_1799294 prefixEnd_1799294 410623404778217105622313 := by
  unfold tailWord_1799294
  simp only [CollatzResearch.WordTrace]
  refine ⟨8203205442934075974413617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43750429028981738530205957 8203205442934075974413617)
  ·
    refine ⟨6152404082200556980810213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8203205442934075974413617 6152404082200556980810213)
    ·
      refine ⟨1153575765412604433901915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6152404082200556980810213 1153575765412604433901915)
      ·
        refine ⟨1730363648118906650852873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1153575765412604433901915 1730363648118906650852873)
        ·
          refine ⟨1297772736089179988139655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1730363648118906650852873 1297772736089179988139655)
          ·
            refine ⟨1946659104133769982209483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1297772736089179988139655 1946659104133769982209483)
            ·
              refine ⟨2919988656200654973314225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1946659104133769982209483 2919988656200654973314225)
              ·
                refine ⟨2189991492150491229985669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2919988656200654973314225 2189991492150491229985669)
                ·
                  refine ⟨410623404778217105622313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2189991492150491229985669 410623404778217105622313)
                  ·
                    rfl

theorem cell21_1799294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 2, 4].length) (baseStart_1799294 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1799294 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1799294 prefixEnd_1799294 := by exact prefixLift 1799294
  have htrace : WordTrace (prefixWord ++ tailWord_1799294) baseStart_1799294 baseEnd_1799294 := by
    simpa [prefixWord, tailWord_1799294, baseEnd_1799294] using wordTrace_append hprefix tailTrace_1799294
  have hstable : (prefixWord ++ tailWord_1799294).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799294).length < 2 ^ (prefixWord ++ tailWord_1799294).sum := by decide
  have hdescent : baseEnd_1799294 < baseStart_1799294 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799347 : List Nat := [1, 1, 1, 2, 3, 2, 5, 3, 3]
def baseStart_1799347 : Nat := 118140960795 + 1799347 * 2 ^ 59
def prefixEnd_1799347 : Nat := 4983230072969 + 3 ^ 40 * 1799347 * 2
def baseEnd_1799347 : Nat := 410635500100300791238871

theorem tailTrace_1799347 : CollatzResearch.WordTrace tailWord_1799347 prefixEnd_1799347 410635500100300791238871 := by
  unfold tailWord_1799347
  simp only [CollatzResearch.WordTrace]
  refine ⟨65627576612280597846988295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43751717741520398564658863 65627576612280597846988295)
  ·
    refine ⟨98441364918420896770482443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65627576612280597846988295 98441364918420896770482443)
    ·
      refine ⟨147662047377631345155723665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98441364918420896770482443 147662047377631345155723665)
      ·
        refine ⟨110746535533223508866792749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147662047377631345155723665 110746535533223508866792749)
        ·
          refine ⟨41529950824958815825047281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110746535533223508866792749 41529950824958815825047281)
          ·
            refine ⟨31147463118719111868785461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41529950824958815825047281 31147463118719111868785461)
            ·
              refine ⟨2920074667379916737698637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31147463118719111868785461 2920074667379916737698637)
              ·
                refine ⟨1095028000267468776636989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2920074667379916737698637 1095028000267468776636989)
                ·
                  refine ⟨410635500100300791238871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1095028000267468776636989 410635500100300791238871)
                  ·
                    rfl

theorem cell21_1799347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 3, 3].length) (baseStart_1799347 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1799347 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1799347 prefixEnd_1799347 := by exact prefixLift 1799347
  have htrace : WordTrace (prefixWord ++ tailWord_1799347) baseStart_1799347 baseEnd_1799347 := by
    simpa [prefixWord, tailWord_1799347, baseEnd_1799347] using wordTrace_append hprefix tailTrace_1799347
  have hstable : (prefixWord ++ tailWord_1799347).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799347).length < 2 ^ (prefixWord ++ tailWord_1799347).sum := by decide
  have hdescent : baseEnd_1799347 < baseStart_1799347 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799350 : List Nat := [5, 1, 3, 2, 1, 2, 7]
def baseStart_1799350 : Nat := 118140960795 + 1799350 * 2 ^ 59
def prefixEnd_1799350 : Nat := 4983230072969 + 3 ^ 40 * 1799350 * 2
def baseEnd_1799350 : Nat := 45626242749019272520985

theorem tailTrace_1799350 : CollatzResearch.WordTrace tailWord_1799350 prefixEnd_1799350 45626242749019272520985 := by
  unfold tailWord_1799350
  simp only [CollatzResearch.WordTrace]
  refine ⟨4101730376954358084959219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43751790687513152906231669 4101730376954358084959219)
  ·
    refine ⟨6152595565431537127438829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4101730376954358084959219 6152595565431537127438829)
    ·
      refine ⟨2307223337036826422789561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6152595565431537127438829 2307223337036826422789561)
      ·
        refine ⟨1730417502777619817092171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2307223337036826422789561 1730417502777619817092171)
        ·
          refine ⟨2595626254166429725638257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1730417502777619817092171 2595626254166429725638257)
          ·
            refine ⟨1946719690624822294228693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2595626254166429725638257 1946719690624822294228693)
            ·
              refine ⟨45626242749019272520985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1946719690624822294228693 45626242749019272520985)
              ·
                rfl

theorem cell21_1799350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 7].length) (baseStart_1799350 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1799350 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1799350 prefixEnd_1799350 := by exact prefixLift 1799350
  have htrace : WordTrace (prefixWord ++ tailWord_1799350) baseStart_1799350 baseEnd_1799350 := by
    simpa [prefixWord, tailWord_1799350, baseEnd_1799350] using wordTrace_append hprefix tailTrace_1799350
  have hstable : (prefixWord ++ tailWord_1799350).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799350).length < 2 ^ (prefixWord ++ tailWord_1799350).sum := by decide
  have hdescent : baseEnd_1799350 < baseStart_1799350 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799364 : List Nat := [2, 3, 3, 1, 3, 2, 1, 1, 5]
def baseStart_1799364 : Nat := 118140960795 + 1799364 * 2 ^ 59
def prefixEnd_1799364 : Nat := 4983230072969 + 3 ^ 40 * 1799364 * 2
def baseEnd_1799364 : Nat := 410639379731912539455503

theorem tailTrace_1799364 : CollatzResearch.WordTrace tailWord_1799364 prefixEnd_1799364 410639379731912539455503 := by
  unfold tailWord_1799364
  simp only [CollatzResearch.WordTrace]
  refine ⟨32814098326609504875178573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43752131102146006500238097 32814098326609504875178573)
  ·
    refine ⟨12305286872478564328191965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32814098326609504875178573 12305286872478564328191965)
    ·
      refine ⟨4614482577179461623071987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12305286872478564328191965 4614482577179461623071987)
      ·
        refine ⟨6921723865769192434607981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4614482577179461623071987 6921723865769192434607981)
        ·
          refine ⟨2595646449663447162977993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6921723865769192434607981 2595646449663447162977993)
          ·
            refine ⟨1946734837247585372233495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2595646449663447162977993 1946734837247585372233495)
            ·
              refine ⟨2920102255871378058350243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1946734837247585372233495 2920102255871378058350243)
              ·
                refine ⟨4380153383807067087525365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2920102255871378058350243 4380153383807067087525365)
                ·
                  refine ⟨410639379731912539455503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4380153383807067087525365 410639379731912539455503)
                  ·
                    rfl

theorem cell21_1799364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 1, 5].length) (baseStart_1799364 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1799364 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1799364 prefixEnd_1799364 := by exact prefixLift 1799364
  have htrace : WordTrace (prefixWord ++ tailWord_1799364) baseStart_1799364 baseEnd_1799364 := by
    simpa [prefixWord, tailWord_1799364, baseEnd_1799364] using wordTrace_append hprefix tailTrace_1799364
  have hstable : (prefixWord ++ tailWord_1799364).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799364).length < 2 ^ (prefixWord ++ tailWord_1799364).sum := by decide
  have hdescent : baseEnd_1799364 < baseStart_1799364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799423 : List Nat := [1, 1, 2, 2, 1, 6, 1, 4, 3]
def baseStart_1799423 : Nat := 118140960795 + 1799423 * 2 ^ 59
def prefixEnd_1799423 : Nat := 4983230072969 + 3 ^ 40 * 1799423 * 2
def baseEnd_1799423 : Nat := 410652844335741547972049

theorem tailTrace_1799423 : CollatzResearch.WordTrace tailWord_1799423 prefixEnd_1799423 410652844335741547972049 := by
  unfold tailWord_1799423
  simp only [CollatzResearch.WordTrace]
  refine ⟨65630348560005262826754923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43753565706670175217836615 65630348560005262826754923)
  ·
    refine ⟨98445522840007894240132385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65630348560005262826754923 98445522840007894240132385)
    ·
      refine ⟨73834142130005920680099289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98445522840007894240132385 73834142130005920680099289)
      ·
        refine ⟨55375606597504440510074467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73834142130005920680099289 55375606597504440510074467)
        ·
          refine ⟨83063409896256660765111701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55375606597504440510074467 83063409896256660765111701)
          ·
            refine ⟨3893597338887030973364611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 83063409896256660765111701 3893597338887030973364611)
            ·
              refine ⟨5840396008330546460046917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3893597338887030973364611 5840396008330546460046917)
              ·
                refine ⟨1095074251561977461258797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5840396008330546460046917 1095074251561977461258797)
                ·
                  refine ⟨410652844335741547972049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1095074251561977461258797 410652844335741547972049)
                  ·
                    rfl

theorem cell21_1799423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 4, 3].length) (baseStart_1799423 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1799423 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1799423 prefixEnd_1799423 := by exact prefixLift 1799423
  have htrace : WordTrace (prefixWord ++ tailWord_1799423) baseStart_1799423 baseEnd_1799423 := by
    simpa [prefixWord, tailWord_1799423, baseEnd_1799423] using wordTrace_append hprefix tailTrace_1799423
  have hstable : (prefixWord ++ tailWord_1799423).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799423).length < 2 ^ (prefixWord ++ tailWord_1799423).sum := by decide
  have hdescent : baseEnd_1799423 < baseStart_1799423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799426 : List Nat := [3, 4, 1, 1, 4, 1, 1, 6]
def baseStart_1799426 : Nat := 118140960795 + 1799426 * 2 ^ 59
def prefixEnd_1799426 : Nat := 4983230072969 + 3 ^ 40 * 1799426 * 2
def baseEnd_1799426 : Nat := 136884509658871403140681

theorem tailTrace_1799426 : CollatzResearch.WordTrace tailWord_1799426 prefixEnd_1799426 136884509658871403140681 := by
  unfold tailWord_1799426
  simp only [CollatzResearch.WordTrace]
  refine ⟨16407614494748598584778533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43753638652662929559409421 16407614494748598584778533)
  ·
    refine ⟨3076427717765362234645975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16407614494748598584778533 3076427717765362234645975)
    ·
      refine ⟨4614641576648043351968963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3076427717765362234645975 4614641576648043351968963)
      ·
        refine ⟨6921962364972065027953445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4614641576648043351968963 6921962364972065027953445)
        ·
          refine ⟨1297867943432262192741271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6921962364972065027953445 1297867943432262192741271)
          ·
            refine ⟨1946801915148393289111907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1297867943432262192741271 1946801915148393289111907)
            ·
              refine ⟨2920202872722589933667861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1946801915148393289111907 2920202872722589933667861)
              ·
                refine ⟨136884509658871403140681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2920202872722589933667861 136884509658871403140681)
                ·
                  rfl

theorem cell21_1799426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 6].length) (baseStart_1799426 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1799426 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1799426 prefixEnd_1799426 := by exact prefixLift 1799426
  have htrace : WordTrace (prefixWord ++ tailWord_1799426) baseStart_1799426 baseEnd_1799426 := by
    simpa [prefixWord, tailWord_1799426, baseEnd_1799426] using wordTrace_append hprefix tailTrace_1799426
  have hstable : (prefixWord ++ tailWord_1799426).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799426).length < 2 ^ (prefixWord ++ tailWord_1799426).sum := by decide
  have hdescent : baseEnd_1799426 < baseStart_1799426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799482 : List Nat := [3, 1, 1, 1, 4, 1, 4, 1, 5]
def baseStart_1799482 : Nat := 118140960795 + 1799482 * 2 ^ 59
def prefixEnd_1799482 : Nat := 4983230072969 + 3 ^ 40 * 1799482 * 2
def baseEnd_1799482 : Nat := 410666308939570556488595

theorem tailTrace_1799482 : CollatzResearch.WordTrace tailWord_1799482 prefixEnd_1799482 410666308939570556488595 := by
  unfold tailWord_1799482
  simp only [CollatzResearch.WordTrace]
  refine ⟨16408125116697878975788175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43755000311194343935435133 16408125116697878975788175)
  ·
    refine ⟨24612187675046818463682263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16408125116697878975788175 24612187675046818463682263)
    ·
      refine ⟨36918281512570227695523395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24612187675046818463682263 36918281512570227695523395)
      ·
        refine ⟨55377422268855341543285093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36918281512570227695523395 55377422268855341543285093)
        ·
          refine ⟨10383266675410376539365955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55377422268855341543285093 10383266675410376539365955)
          ·
            refine ⟨15574900013115564809048933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10383266675410376539365955 15574900013115564809048933)
            ·
              refine ⟨2920293752459168401696675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15574900013115564809048933 2920293752459168401696675)
              ·
                refine ⟨4380440628688752602545013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2920293752459168401696675 4380440628688752602545013)
                ·
                  refine ⟨410666308939570556488595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4380440628688752602545013 410666308939570556488595)
                  ·
                    rfl

theorem cell21_1799482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 1, 5].length) (baseStart_1799482 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1799482 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1799482 prefixEnd_1799482 := by exact prefixLift 1799482
  have htrace : WordTrace (prefixWord ++ tailWord_1799482) baseStart_1799482 baseEnd_1799482 := by
    simpa [prefixWord, tailWord_1799482, baseEnd_1799482] using wordTrace_append hprefix tailTrace_1799482
  have hstable : (prefixWord ++ tailWord_1799482).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799482).length < 2 ^ (prefixWord ++ tailWord_1799482).sum := by decide
  have hdescent : baseEnd_1799482 < baseStart_1799482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799648 : List Nat := [2, 1, 1, 3, 1, 1, 2, 6, 4]
def baseStart_1799648 : Nat := 118140960795 + 1799648 * 2 ^ 59
def prefixEnd_1799648 : Nat := 4983230072969 + 3 ^ 40 * 1799648 * 2
def baseEnd_1799648 : Nat := 410704192401191156721589

theorem tailTrace_1799648 : CollatzResearch.WordTrace tailWord_1799648 prefixEnd_1799648 410704192401191156721589 := by
  unfold tailWord_1799648
  simp only [CollatzResearch.WordTrace]
  refine ⟨32819277492095063126847799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43759036656126750835797065 32819277492095063126847799)
  ·
    refine ⟨49228916238142594690271699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32819277492095063126847799 49228916238142594690271699)
    ·
      refine ⟨73843374357213892035407549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49228916238142594690271699 73843374357213892035407549)
      ·
        refine ⟨27691265383955209513277831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73843374357213892035407549 27691265383955209513277831)
        ·
          refine ⟨41536898075932814269916747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27691265383955209513277831 41536898075932814269916747)
          ·
            refine ⟨62305347113899221404875121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41536898075932814269916747 62305347113899221404875121)
            ·
              refine ⟨46729010335424416053656341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62305347113899221404875121 46729010335424416053656341)
              ·
                refine ⟨2190422359473019502515141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 46729010335424416053656341 2190422359473019502515141)
                ·
                  refine ⟨410704192401191156721589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2190422359473019502515141 410704192401191156721589)
                  ·
                    rfl

theorem cell21_1799648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 6, 4].length) (baseStart_1799648 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1799648 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1799648 prefixEnd_1799648 := by exact prefixLift 1799648
  have htrace : WordTrace (prefixWord ++ tailWord_1799648) baseStart_1799648 baseEnd_1799648 := by
    simpa [prefixWord, tailWord_1799648, baseEnd_1799648] using wordTrace_append hprefix tailTrace_1799648
  have hstable : (prefixWord ++ tailWord_1799648).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799648).length < 2 ^ (prefixWord ++ tailWord_1799648).sum := by decide
  have hdescent : baseEnd_1799648 < baseStart_1799648 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799651 : List Nat := [1, 1, 1, 6, 2, 1, 2, 4, 3]
def baseStart_1799651 : Nat := 118140960795 + 1799651 * 2 ^ 59
def prefixEnd_1799651 : Nat := 4983230072969 + 3 ^ 40 * 1799651 * 2
def baseEnd_1799651 : Nat := 410704877042063818171583

theorem tailTrace_1799651 : CollatzResearch.WordTrace tailWord_1799651 prefixEnd_1799651 410704877042063818171583 := by
  unfold tailWord_1799651
  simp only [CollatzResearch.WordTrace]
  refine ⟨65638664403179257766054807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43759109602119505177369871 65638664403179257766054807)
  ·
    refine ⟨98457996604768886649082211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65638664403179257766054807 98457996604768886649082211)
    ·
      refine ⟨147686994907153329973623317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98457996604768886649082211 147686994907153329973623317)
      ·
        refine ⟨6922827886272812342513593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 147686994907153329973623317 6922827886272812342513593)
        ·
          refine ⟨5192120914704609256885195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6922827886272812342513593 5192120914704609256885195)
          ·
            refine ⟨7788181372056913885327793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5192120914704609256885195 7788181372056913885327793)
            ·
              refine ⟨5841136029042685413995845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7788181372056913885327793 5841136029042685413995845)
              ·
                refine ⟨1095213005445503515124221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5841136029042685413995845 1095213005445503515124221)
                ·
                  refine ⟨410704877042063818171583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1095213005445503515124221 410704877042063818171583)
                  ·
                    rfl

theorem cell21_1799651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 4, 3].length) (baseStart_1799651 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1799651 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1799651 prefixEnd_1799651 := by exact prefixLift 1799651
  have htrace : WordTrace (prefixWord ++ tailWord_1799651) baseStart_1799651 baseEnd_1799651 := by
    simpa [prefixWord, tailWord_1799651, baseEnd_1799651] using wordTrace_append hprefix tailTrace_1799651
  have hstable : (prefixWord ++ tailWord_1799651).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799651).length < 2 ^ (prefixWord ++ tailWord_1799651).sum := by decide
  have hdescent : baseEnd_1799651 < baseStart_1799651 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799738 : List Nat := [3, 1, 1, 1, 3, 2, 1, 9]
def baseStart_1799738 : Nat := 118140960795 + 1799738 * 2 ^ 59
def prefixEnd_1799738 : Nat := 4983230072969 + 3 ^ 40 * 1799738 * 2
def baseEnd_1799738 : Nat := 136908243875790333407135

theorem tailTrace_1799738 : CollatzResearch.WordTrace tailWord_1799738 prefixEnd_1799738 136908243875790333407135 := by
  unfold tailWord_1799738
  simp only [CollatzResearch.WordTrace]
  refine ⟨16410459388466017906117967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43761225035909381082981245 16410459388466017906117967)
  ·
    refine ⟨24615689082699026859176951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16410459388466017906117967 24615689082699026859176951)
    ·
      refine ⟨36923533624048540288765427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24615689082699026859176951 36923533624048540288765427)
      ·
        refine ⟨55385300436072810433148141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36923533624048540288765427 55385300436072810433148141)
        ·
          refine ⟨20769487663527303912430553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55385300436072810433148141 20769487663527303912430553)
          ·
            refine ⟨15577115747645477934322915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20769487663527303912430553 15577115747645477934322915)
            ·
              refine ⟨23365673621468216901484373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15577115747645477934322915 23365673621468216901484373)
              ·
                refine ⟨136908243875790333407135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23365673621468216901484373 136908243875790333407135)
                ·
                  rfl

theorem cell21_1799738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 9].length) (baseStart_1799738 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1799738 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1799738 prefixEnd_1799738 := by exact prefixLift 1799738
  have htrace : WordTrace (prefixWord ++ tailWord_1799738) baseStart_1799738 baseEnd_1799738 := by
    simpa [prefixWord, tailWord_1799738, baseEnd_1799738] using wordTrace_append hprefix tailTrace_1799738
  have hstable : (prefixWord ++ tailWord_1799738).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799738).length < 2 ^ (prefixWord ++ tailWord_1799738).sum := by decide
  have hdescent : baseEnd_1799738 < baseStart_1799738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799772 : List Nat := [2, 2, 4, 1, 2, 3, 1, 6]
def baseStart_1799772 : Nat := 118140960795 + 1799772 * 2 ^ 59
def prefixEnd_1799772 : Nat := 4983230072969 + 3 ^ 40 * 1799772 * 2
def baseEnd_1799772 : Nat := 136910830296864832218223

theorem tailTrace_1799772 : CollatzResearch.WordTrace tailWord_1799772 prefixEnd_1799772 136910830296864832218223 := by
  unfold tailWord_1799772
  simp only [CollatzResearch.WordTrace]
  refine ⟨32821538817870447715604785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43762051757160596954139713 32821538817870447715604785)
  ·
    refine ⟨24616154113402835786703589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32821538817870447715604785 24616154113402835786703589)
    ·
      refine ⟨4615528896263031710006923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24616154113402835786703589 4615528896263031710006923)
      ·
        refine ⟨6923293344394547565010385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4615528896263031710006923 6923293344394547565010385)
        ·
          refine ⟨5192470008295910673757789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6923293344394547565010385 5192470008295910673757789)
          ·
            refine ⟨1947176253110966502659171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5192470008295910673757789 1947176253110966502659171)
            ·
              refine ⟨2920764379666449753988757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1947176253110966502659171 2920764379666449753988757)
              ·
                refine ⟨136910830296864832218223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2920764379666449753988757 136910830296864832218223)
                ·
                  rfl

theorem cell21_1799772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 6].length) (baseStart_1799772 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1799772 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1799772 prefixEnd_1799772 := by exact prefixLift 1799772
  have htrace : WordTrace (prefixWord ++ tailWord_1799772) baseStart_1799772 baseEnd_1799772 := by
    simpa [prefixWord, tailWord_1799772, baseEnd_1799772] using wordTrace_append hprefix tailTrace_1799772
  have hstable : (prefixWord ++ tailWord_1799772).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799772).length < 2 ^ (prefixWord ++ tailWord_1799772).sum := by decide
  have hdescent : baseEnd_1799772 < baseStart_1799772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799786 : List Nat := [3, 1, 3, 2, 1, 3, 1, 2, 5]
def baseStart_1799786 : Nat := 118140960795 + 1799786 * 2 ^ 59
def prefixEnd_1799786 : Nat := 4983230072969 + 3 ^ 40 * 1799786 * 2
def baseEnd_1799786 : Nat := 410735685881333583421307

theorem tailTrace_1799786 : CollatzResearch.WordTrace tailWord_1799786 prefixEnd_1799786 410735685881333583421307 := by
  unfold tailWord_1799786
  simp only [CollatzResearch.WordTrace]
  refine ⟨16410897064422543955554803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43762392171793450548146141 16410897064422543955554803)
  ·
    refine ⟨24616345596633815933332205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16410897064422543955554803 24616345596633815933332205)
    ·
      refine ⟨9231129598737680974999577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24616345596633815933332205 9231129598737680974999577)
      ·
        refine ⟨6923347199053260731249683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9231129598737680974999577 6923347199053260731249683)
        ·
          refine ⟨10385020798579891096874525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6923347199053260731249683 10385020798579891096874525)
          ·
            refine ⟨3894382799467459161327947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10385020798579891096874525 3894382799467459161327947)
            ·
              refine ⟨5841574199201188741991921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3894382799467459161327947 5841574199201188741991921)
              ·
                refine ⟨4381180649400891556493941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5841574199201188741991921 4381180649400891556493941)
                ·
                  refine ⟨410735685881333583421307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4381180649400891556493941 410735685881333583421307)
                  ·
                    rfl

theorem cell21_1799786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 2, 5].length) (baseStart_1799786 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1799786 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1799786 prefixEnd_1799786 := by exact prefixLift 1799786
  have htrace : WordTrace (prefixWord ++ tailWord_1799786) baseStart_1799786 baseEnd_1799786 := by
    simpa [prefixWord, tailWord_1799786, baseEnd_1799786] using wordTrace_append hprefix tailTrace_1799786
  have hstable : (prefixWord ++ tailWord_1799786).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799786).length < 2 ^ (prefixWord ++ tailWord_1799786).sum := by decide
  have hdescent : baseEnd_1799786 < baseStart_1799786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799845 : List Nat := [1, 3, 1, 2, 1, 2, 4, 2, 5]
def baseStart_1799845 : Nat := 118140960795 + 1799845 * 2 ^ 59
def prefixEnd_1799845 : Nat := 4983230072969 + 3 ^ 40 * 1799845 * 2
def baseEnd_1799845 : Nat := 410749150485162591937853

theorem tailTrace_1799845 : CollatzResearch.WordTrace tailWord_1799845 prefixEnd_1799845 410749150485162591937853 := by
  unfold tailWord_1799845
  simp only [CollatzResearch.WordTrace]
  refine ⟨65645740164476428898616989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43763826776317619265744659 65645740164476428898616989)
  ·
    refine ⟨24617152561678660836981371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65645740164476428898616989 24617152561678660836981371)
    ·
      refine ⟨36925728842517991255472057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24617152561678660836981371 36925728842517991255472057)
      ·
        refine ⟨27694296631888493441604043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36925728842517991255472057 27694296631888493441604043)
        ·
          refine ⟨41541444947832740162406065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27694296631888493441604043 41541444947832740162406065)
          ·
            refine ⟨31156083710874555121804549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41541444947832740162406065 31156083710874555121804549)
            ·
              refine ⟨5841765695788979085338353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31156083710874555121804549 5841765695788979085338353)
              ·
                refine ⟨4381324271841734314003765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5841765695788979085338353 4381324271841734314003765)
                ·
                  refine ⟨410749150485162591937853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4381324271841734314003765 410749150485162591937853)
                  ·
                    rfl

theorem cell21_1799845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 2, 5].length) (baseStart_1799845 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1799845 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1799845 prefixEnd_1799845 := by exact prefixLift 1799845
  have htrace : WordTrace (prefixWord ++ tailWord_1799845) baseStart_1799845 baseEnd_1799845 := by
    simpa [prefixWord, tailWord_1799845, baseEnd_1799845] using wordTrace_append hprefix tailTrace_1799845
  have hstable : (prefixWord ++ tailWord_1799845).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799845).length < 2 ^ (prefixWord ++ tailWord_1799845).sum := by decide
  have hdescent : baseEnd_1799845 < baseStart_1799845 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799854 : List Nat := [4, 1, 4, 1, 3, 1, 1, 3, 3]
def baseStart_1799854 : Nat := 118140960795 + 1799854 * 2 ^ 59
def prefixEnd_1799854 : Nat := 4983230072969 + 3 ^ 40 * 1799854 * 2
def baseEnd_1799854 : Nat := 410751204407780576287835

theorem tailTrace_1799854 : CollatzResearch.WordTrace tailWord_1799854 prefixEnd_1799854 410751204407780576287835 := by
  unfold tailWord_1799854
  simp only [CollatzResearch.WordTrace]
  refine ⟨8205758552680477929461827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43764045614295882290463077 8205758552680477929461827)
  ·
    refine ⟨12308637829020716894192741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8205758552680477929461827 12308637829020716894192741)
    ·
      refine ⟨2307869592941384417661139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12308637829020716894192741 2307869592941384417661139)
      ·
        refine ⟨3461804389412076626491709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2307869592941384417661139 3461804389412076626491709)
        ·
          refine ⟨1298176646029528734934391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3461804389412076626491709 1298176646029528734934391)
          ·
            refine ⟨1947264969044293102401587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1298176646029528734934391 1947264969044293102401587)
            ·
              refine ⟨2920897453566439653602381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1947264969044293102401587 2920897453566439653602381)
              ·
                refine ⟨1095336545087414870100893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2920897453566439653602381 1095336545087414870100893)
                ·
                  refine ⟨410751204407780576287835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1095336545087414870100893 410751204407780576287835)
                  ·
                    rfl

theorem cell21_1799854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 3, 3].length) (baseStart_1799854 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1799854 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1799854 prefixEnd_1799854 := by exact prefixLift 1799854
  have htrace : WordTrace (prefixWord ++ tailWord_1799854) baseStart_1799854 baseEnd_1799854 := by
    simpa [prefixWord, tailWord_1799854, baseEnd_1799854] using wordTrace_append hprefix tailTrace_1799854
  have hstable : (prefixWord ++ tailWord_1799854).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799854).length < 2 ^ (prefixWord ++ tailWord_1799854).sum := by decide
  have hdescent : baseEnd_1799854 < baseStart_1799854 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799859 : List Nat := [1, 1, 1, 2, 3, 3, 1, 1, 8]
def baseStart_1799859 : Nat := 118140960795 + 1799859 * 2 ^ 59
def prefixEnd_1799859 : Nat := 4983230072969 + 3 ^ 40 * 1799859 * 2
def baseEnd_1799859 : Nat := 410752345475901678704491

theorem tailTrace_1799859 : CollatzResearch.WordTrace tailWord_1799859 prefixEnd_1799859 410752345475901678704491 := by
  unfold tailWord_1799859
  simp only [CollatzResearch.WordTrace]
  refine ⟨65646250786425709289626631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43764167190950472859751087 65646250786425709289626631)
  ·
    refine ⟨98469376179638563934439947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65646250786425709289626631 98469376179638563934439947)
    ·
      refine ⟨147704064269457845901659921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98469376179638563934439947 147704064269457845901659921)
      ·
        refine ⟨110778048202093384426244941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147704064269457845901659921 110778048202093384426244941)
        ·
          refine ⟨41541768075785019159841853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110778048202093384426244941 41541768075785019159841853)
          ·
            refine ⟨15578163028419382184940695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41541768075785019159841853 15578163028419382184940695)
            ·
              refine ⟨23367244542629073277411043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15578163028419382184940695 23367244542629073277411043)
              ·
                refine ⟨35050866813943609916116565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23367244542629073277411043 35050866813943609916116565)
                ·
                  refine ⟨410752345475901678704491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35050866813943609916116565 410752345475901678704491)
                  ·
                    rfl

theorem cell21_1799859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 8].length) (baseStart_1799859 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1799859 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1799859 prefixEnd_1799859 := by exact prefixLift 1799859
  have htrace : WordTrace (prefixWord ++ tailWord_1799859) baseStart_1799859 baseEnd_1799859 := by
    simpa [prefixWord, tailWord_1799859, baseEnd_1799859] using wordTrace_append hprefix tailTrace_1799859
  have hstable : (prefixWord ++ tailWord_1799859).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799859).length < 2 ^ (prefixWord ++ tailWord_1799859).sum := by decide
  have hdescent : baseEnd_1799859 < baseStart_1799859 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799876 : List Nat := [2, 3, 3, 1, 1, 1, 1, 3, 6]
def baseStart_1799876 : Nat := 118140960795 + 1799876 * 2 ^ 59
def prefixEnd_1799876 : Nat := 4983230072969 + 3 ^ 40 * 1799876 * 2
def baseEnd_1799876 : Nat := 410756225107513426921123

theorem tailTrace_1799876 : CollatzResearch.WordTrace tailWord_1799876 prefixEnd_1799876 410756225107513426921123 := by
  unfold tailWord_1799876
  simp only [CollatzResearch.WordTrace]
  refine ⟨32823435413682060596497741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43764580551576080795330321 32823435413682060596497741)
  ·
    refine ⟨12308788280130772723686653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32823435413682060596497741 12308788280130772723686653)
    ·
      refine ⟨4615795605049039771382495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12308788280130772723686653 4615795605049039771382495)
      ·
        refine ⟨6923693407573559657073743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4615795605049039771382495 6923693407573559657073743)
        ·
          refine ⟨10385540111360339485610615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6923693407573559657073743 10385540111360339485610615)
          ·
            refine ⟨15578310167040509228415923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10385540111360339485610615 15578310167040509228415923)
            ·
              refine ⟨23367465250560763842623885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15578310167040509228415923 23367465250560763842623885)
              ·
                refine ⟨8762799468960286440983957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23367465250560763842623885 8762799468960286440983957)
                ·
                  refine ⟨410756225107513426921123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8762799468960286440983957 410756225107513426921123)
                  ·
                    rfl

theorem cell21_1799876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 3, 6].length) (baseStart_1799876 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1799876 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1799876 prefixEnd_1799876 := by exact prefixLift 1799876
  have htrace : WordTrace (prefixWord ++ tailWord_1799876) baseStart_1799876 baseEnd_1799876 := by
    simpa [prefixWord, tailWord_1799876, baseEnd_1799876] using wordTrace_append hprefix tailTrace_1799876
  have hstable : (prefixWord ++ tailWord_1799876).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799876).length < 2 ^ (prefixWord ++ tailWord_1799876).sum := by decide
  have hdescent : baseEnd_1799876 < baseStart_1799876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799879 : List Nat := [1, 1, 4, 1, 1, 1, 7, 2, 3]
def baseStart_1799879 : Nat := 118140960795 + 1799879 * 2 ^ 59
def prefixEnd_1799879 : Nat := 4983230072969 + 3 ^ 40 * 1799879 * 2
def baseEnd_1799879 : Nat := 410756909748386088371117

theorem tailTrace_1799879 : CollatzResearch.WordTrace tailWord_1799879 prefixEnd_1799879 410756909748386088371117 := by
  unfold tailWord_1799879
  simp only [CollatzResearch.WordTrace]
  refine ⟨65646980246353252705354691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43764653497568835136903127 65646980246353252705354691)
  ·
    refine ⟨98470470369529879058032037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65646980246353252705354691 98470470369529879058032037)
    ·
      refine ⟨18463213194286852323381007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98470470369529879058032037 18463213194286852323381007)
      ·
        refine ⟨27694819791430278485071511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18463213194286852323381007 27694819791430278485071511)
        ·
          refine ⟨41542229687145417727607267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27694819791430278485071511 41542229687145417727607267)
          ·
            refine ⟨62313344530718126591410901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41542229687145417727607267 62313344530718126591410901)
            ·
              refine ⟨1460469012438706091986193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 62313344530718126591410901 1460469012438706091986193)
              ·
                refine ⟨1095351759329029568989645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1460469012438706091986193 1095351759329029568989645)
                ·
                  refine ⟨410756909748386088371117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1095351759329029568989645 410756909748386088371117)
                  ·
                    rfl

theorem cell21_1799879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 7, 2, 3].length) (baseStart_1799879 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1799879 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1799879 prefixEnd_1799879 := by exact prefixLift 1799879
  have htrace : WordTrace (prefixWord ++ tailWord_1799879) baseStart_1799879 baseEnd_1799879 := by
    simpa [prefixWord, tailWord_1799879, baseEnd_1799879] using wordTrace_append hprefix tailTrace_1799879
  have hstable : (prefixWord ++ tailWord_1799879).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799879).length < 2 ^ (prefixWord ++ tailWord_1799879).sum := by decide
  have hdescent : baseEnd_1799879 < baseStart_1799879 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799924 : List Nat := [2, 6, 1, 1, 1, 10]
def baseStart_1799924 : Nat := 118140960795 + 1799924 * 2 ^ 59
def prefixEnd_1799924 : Nat := 4983230072969 + 3 ^ 40 * 1799924 * 2
def baseEnd_1799924 : Nat := 15213599235610222597075

theorem tailTrace_1799924 : CollatzResearch.WordTrace tailWord_1799924 prefixEnd_1799924 15213599235610222597075 := by
  unfold tailWord_1799924
  simp only [CollatzResearch.WordTrace]
  refine ⟨32824310765595112695371413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43765747687460150260495217 32824310765595112695371413)
  ·
    refine ⟨1538639567137270907595535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 32824310765595112695371413 1538639567137270907595535)
    ·
      refine ⟨2307959350705906361393303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1538639567137270907595535 2307959350705906361393303)
      ·
        refine ⟨3461939026058859542089955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2307959350705906361393303 3461939026058859542089955)
        ·
          refine ⟨5192908539088289313134933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3461939026058859542089955 5192908539088289313134933)
          ·
            refine ⟨15213599235610222597075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5192908539088289313134933 15213599235610222597075)
            ·
              rfl

theorem cell21_1799924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 10].length) (baseStart_1799924 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1799924 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1799924 prefixEnd_1799924 := by exact prefixLift 1799924
  have htrace : WordTrace (prefixWord ++ tailWord_1799924) baseStart_1799924 baseEnd_1799924 := by
    simpa [prefixWord, tailWord_1799924, baseEnd_1799924] using wordTrace_append hprefix tailTrace_1799924
  have hstable : (prefixWord ++ tailWord_1799924).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799924).length < 2 ^ (prefixWord ++ tailWord_1799924).sum := by decide
  have hdescent : baseEnd_1799924 < baseStart_1799924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799935 : List Nat := [1, 1, 2, 2, 1, 3, 2, 3, 6]
def baseStart_1799935 : Nat := 118140960795 + 1799935 * 2 ^ 59
def prefixEnd_1799935 : Nat := 4983230072969 + 3 ^ 40 * 1799935 * 2
def baseEnd_1799935 : Nat := 410769689711342435437669

theorem tailTrace_1799935 : CollatzResearch.WordTrace tailWord_1799935 prefixEnd_1799935 410769689711342435437669 := by
  unfold tailWord_1799935
  simp only [CollatzResearch.WordTrace]
  refine ⟨65649022734150374269393259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43766015156100249512928839 65649022734150374269393259)
  ·
    refine ⟨98473534101225561404089889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65649022734150374269393259 98473534101225561404089889)
    ·
      refine ⟨73855150575919171053067417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98473534101225561404089889 73855150575919171053067417)
      ·
        refine ⟨55391362931939378289800563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73855150575919171053067417 55391362931939378289800563)
        ·
          refine ⟨83087044397909067434700845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55391362931939378289800563 83087044397909067434700845)
          ·
            refine ⟨31157641649215900288012817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83087044397909067434700845 31157641649215900288012817)
            ·
              refine ⟨23368231236911925216009613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31157641649215900288012817 23368231236911925216009613)
              ·
                refine ⟨8763086713841971956003605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23368231236911925216009613 8763086713841971956003605)
                ·
                  refine ⟨410769689711342435437669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8763086713841971956003605 410769689711342435437669)
                  ·
                    rfl

theorem cell21_1799935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 3, 6].length) (baseStart_1799935 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1799935 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1799935 prefixEnd_1799935 := by exact prefixLift 1799935
  have htrace : WordTrace (prefixWord ++ tailWord_1799935) baseStart_1799935 baseEnd_1799935 := by
    simpa [prefixWord, tailWord_1799935, baseEnd_1799935] using wordTrace_append hprefix tailTrace_1799935
  have hstable : (prefixWord ++ tailWord_1799935).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799935).length < 2 ^ (prefixWord ++ tailWord_1799935).sum := by decide
  have hdescent : baseEnd_1799935 < baseStart_1799935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1799938 : List Nat := [3, 4, 1, 1, 1, 1, 2, 3, 5]
def baseStart_1799938 : Nat := 118140960795 + 1799938 * 2 ^ 59
def prefixEnd_1799938 : Nat := 4983230072969 + 3 ^ 40 * 1799938 * 2
def baseEnd_1799938 : Nat := 410770374352215096887663

theorem tailTrace_1799938 : CollatzResearch.WordTrace tailWord_1799938 prefixEnd_1799938 410770374352215096887663 := by
  unfold tailWord_1799938
  simp only [CollatzResearch.WordTrace]
  refine ⟨16412283038284876445438117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43766088102093003854501645 16412283038284876445438117)
  ·
    refine ⟨3077303069678414333519647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16412283038284876445438117 3077303069678414333519647)
    ·
      refine ⟨4615954604517621500279471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3077303069678414333519647 4615954604517621500279471)
      ·
        refine ⟨6923931906776432250419207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4615954604517621500279471 6923931906776432250419207)
        ·
          refine ⟨10385897860164648375628811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6923931906776432250419207 10385897860164648375628811)
          ·
            refine ⟨15578846790246972563443217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10385897860164648375628811 15578846790246972563443217)
            ·
              refine ⟨11684135092685229422582413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15578846790246972563443217 11684135092685229422582413)
              ·
                refine ⟨4381550659756961033468405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11684135092685229422582413 4381550659756961033468405)
                ·
                  refine ⟨410770374352215096887663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4381550659756961033468405 410770374352215096887663)
                  ·
                    rfl

theorem cell21_1799938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_1799938 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1799938 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1799938 prefixEnd_1799938 := by exact prefixLift 1799938
  have htrace : WordTrace (prefixWord ++ tailWord_1799938) baseStart_1799938 baseEnd_1799938 := by
    simpa [prefixWord, tailWord_1799938, baseEnd_1799938] using wordTrace_append hprefix tailTrace_1799938
  have hstable : (prefixWord ++ tailWord_1799938).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1799938).length < 2 ^ (prefixWord ++ tailWord_1799938).sum := by decide
  have hdescent : baseEnd_1799938 < baseStart_1799938 := by decide
  rcases family_descends (prefixWord ++ tailWord_1799938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1800031 : List Nat := [1, 1, 2, 3, 1, 6, 1, 3, 3]
def baseStart_1800031 : Nat := 118140960795 + 1800031 * 2 ^ 59
def prefixEnd_1800031 : Nat := 4983230072969 + 3 ^ 40 * 1800031 * 2
def baseEnd_1800031 : Nat := 410791598219267601837473

theorem tailTrace_1800031 : CollatzResearch.WordTrace tailWord_1800031 prefixEnd_1800031 410791598219267601837473 := by
  unfold tailWord_1800031
  simp only [CollatzResearch.WordTrace]
  refine ⟨65652524141802582664887947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43768349427868388443258631 65652524141802582664887947)
  ·
    refine ⟨98478786212703873997331921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65652524141802582664887947 98478786212703873997331921)
    ·
      refine ⟨73859089659527905497998941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98478786212703873997331921 73859089659527905497998941)
      ·
        refine ⟨27697158622322964561749603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73859089659527905497998941 27697158622322964561749603)
        ·
          refine ⟨41545737933484446842624405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27697158622322964561749603 41545737933484446842624405)
          ·
            refine ⟨1947456465632083445748019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 41545737933484446842624405 1947456465632083445748019)
            ·
              refine ⟨2921184698448125168622029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1947456465632083445748019 2921184698448125168622029)
              ·
                refine ⟨1095444261918046938233261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2921184698448125168622029 1095444261918046938233261)
                ·
                  refine ⟨410791598219267601837473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1095444261918046938233261 410791598219267601837473)
                  ·
                    rfl

theorem cell21_1800031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 3, 3].length) (baseStart_1800031 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1800031 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1800031 prefixEnd_1800031 := by exact prefixLift 1800031
  have htrace : WordTrace (prefixWord ++ tailWord_1800031) baseStart_1800031 baseEnd_1800031 := by
    simpa [prefixWord, tailWord_1800031, baseEnd_1800031] using wordTrace_append hprefix tailTrace_1800031
  have hstable : (prefixWord ++ tailWord_1800031).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1800031).length < 2 ^ (prefixWord ++ tailWord_1800031).sum := by decide
  have hdescent : baseEnd_1800031 < baseStart_1800031 := by decide
  rcases family_descends (prefixWord ++ tailWord_1800031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1800062 : List Nat := [4, 2, 3, 1, 1, 2, 1, 3, 4]
def baseStart_1800062 : Nat := 118140960795 + 1800062 * 2 ^ 59
def prefixEnd_1800062 : Nat := 4983230072969 + 3 ^ 40 * 1800062 * 2
def baseEnd_1800062 : Nat := 410798672841618436820743

theorem tailTrace_1800062 : CollatzResearch.WordTrace tailWord_1800062 prefixEnd_1800062 410798672841618436820743 := by
  unfold tailWord_1800062
  simp only [CollatzResearch.WordTrace]
  refine ⟨8206706850586284369908305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43769103203126849972844293 8206706850586284369908305)
  ·
    refine ⟨6155030137939713277431229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8206706850586284369908305 6155030137939713277431229)
    ·
      refine ⟨2308136301727392479036711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6155030137939713277431229 2308136301727392479036711)
      ·
        refine ⟨3462204452591088718555067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2308136301727392479036711 3462204452591088718555067)
        ·
          refine ⟨5193306678886633077832601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3462204452591088718555067 5193306678886633077832601)
          ·
            refine ⟨3894980009164974808374451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5193306678886633077832601 3894980009164974808374451)
            ·
              refine ⟨5842470013747462212561677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3894980009164974808374451 5842470013747462212561677)
              ·
                refine ⟨2190926255155298329710629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5842470013747462212561677 2190926255155298329710629)
                ·
                  refine ⟨410798672841618436820743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2190926255155298329710629 410798672841618436820743)
                  ·
                    rfl

theorem cell21_1800062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 3, 4].length) (baseStart_1800062 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1800062 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1800062 prefixEnd_1800062 := by exact prefixLift 1800062
  have htrace : WordTrace (prefixWord ++ tailWord_1800062) baseStart_1800062 baseEnd_1800062 := by
    simpa [prefixWord, tailWord_1800062, baseEnd_1800062] using wordTrace_append hprefix tailTrace_1800062
  have hstable : (prefixWord ++ tailWord_1800062).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1800062).length < 2 ^ (prefixWord ++ tailWord_1800062).sum := by decide
  have hdescent : baseEnd_1800062 < baseStart_1800062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1800062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1800110 : List Nat := [4, 1, 5, 1, 1, 2, 1, 6]
def baseStart_1800110 : Nat := 118140960795 + 1800110 * 2 ^ 59
def prefixEnd_1800110 : Nat := 4983230072969 + 3 ^ 40 * 1800110 * 2
def baseEnd_1800110 : Nat := 136936542365193673340215

theorem tailTrace_1800110 : CollatzResearch.WordTrace tailWord_1800110 prefixEnd_1800110 136936542365193673340215 := by
  unfold tailWord_1800110
  simp only [CollatzResearch.WordTrace]
  refine ⟨8206925688564547394626723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43770270339010919438009189 8206925688564547394626723)
  ·
    refine ⟨12310388532846821091940085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8206925688564547394626723 12310388532846821091940085)
    ·
      refine ⟨1154098924954389477369383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12310388532846821091940085 1154098924954389477369383)
      ·
        refine ⟨1731148387431584216054075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1154098924954389477369383 1731148387431584216054075)
        ·
          refine ⟨2596722581147376324081113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1731148387431584216054075 2596722581147376324081113)
          ·
            refine ⟨1947541935860532243060835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2596722581147376324081113 1947541935860532243060835)
            ·
              refine ⟨2921312903790798364591253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1947541935860532243060835 2921312903790798364591253)
              ·
                refine ⟨136936542365193673340215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2921312903790798364591253 136936542365193673340215)
                ·
                  rfl

theorem cell21_1800110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 6].length) (baseStart_1800110 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1800110 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1800110 prefixEnd_1800110 := by exact prefixLift 1800110
  have htrace : WordTrace (prefixWord ++ tailWord_1800110) baseStart_1800110 baseEnd_1800110 := by
    simpa [prefixWord, tailWord_1800110, baseEnd_1800110] using wordTrace_append hprefix tailTrace_1800110
  have hstable : (prefixWord ++ tailWord_1800110).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1800110).length < 2 ^ (prefixWord ++ tailWord_1800110).sum := by decide
  have hdescent : baseEnd_1800110 < baseStart_1800110 := by decide
  rcases family_descends (prefixWord ++ tailWord_1800110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1800231 : List Nat := [1, 1, 7, 1, 2, 2, 2, 1, 4]
def baseStart_1800231 : Nat := 118140960795 + 1800231 * 2 ^ 59
def prefixEnd_1800231 : Nat := 4983230072969 + 3 ^ 40 * 1800231 * 2
def baseEnd_1800231 : Nat := 410837240944111698503731

theorem tailTrace_1800231 : CollatzResearch.WordTrace tailWord_1800231 prefixEnd_1800231 410837240944111698503731 := by
  unfold tailWord_1800231
  simp only [CollatzResearch.WordTrace]
  refine ⟨65659818741078016822168547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43773212494052011214779031 65659818741078016822168547)
  ·
    refine ⟨98489728111617025233252821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65659818741078016822168547 98489728111617025233252821)
    ·
      refine ⟨2308353002616024028904363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 98489728111617025233252821 2308353002616024028904363)
      ·
        refine ⟨3462529503924036043356545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2308353002616024028904363 3462529503924036043356545)
        ·
          refine ⟨2596897127943027032517409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3462529503924036043356545 2596897127943027032517409)
          ·
            refine ⟨1947672845957270274388057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2596897127943027032517409 1947672845957270274388057)
            ·
              refine ⟨1460754634467952705791043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1947672845957270274388057 1460754634467952705791043)
              ·
                refine ⟨2191131951701929058686565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1460754634467952705791043 2191131951701929058686565)
                ·
                  refine ⟨410837240944111698503731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2191131951701929058686565 410837240944111698503731)
                  ·
                    rfl

theorem cell21_1800231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 2, 1, 4].length) (baseStart_1800231 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1800231 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1800231 prefixEnd_1800231 := by exact prefixLift 1800231
  have htrace : WordTrace (prefixWord ++ tailWord_1800231) baseStart_1800231 baseEnd_1800231 := by
    simpa [prefixWord, tailWord_1800231, baseEnd_1800231] using wordTrace_append hprefix tailTrace_1800231
  have hstable : (prefixWord ++ tailWord_1800231).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1800231).length < 2 ^ (prefixWord ++ tailWord_1800231).sum := by decide
  have hdescent : baseEnd_1800231 < baseStart_1800231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1800231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1800301 : List Nat := [1, 5, 1, 1, 2, 1, 3, 2, 5]
def baseStart_1800301 : Nat := 118140960795 + 1800301 * 2 ^ 59
def prefixEnd_1800301 : Nat := 4983230072969 + 3 ^ 40 * 1800301 * 2
def baseEnd_1800301 : Nat := 410853215897807132336921

theorem tailTrace_1800301 : CollatzResearch.WordTrace tailWord_1800301 prefixEnd_1800301 410853215897807132336921 := by
  unfold tailWord_1800301
  simp only [CollatzResearch.WordTrace]
  refine ⟨65662371850824418777216757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43774914567216279184811171 65662371850824418777216757)
  ·
    refine ⟨6155847361014789260364071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 65662371850824418777216757 6155847361014789260364071)
    ·
      refine ⟨9233771041522183890546107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6155847361014789260364071 9233771041522183890546107)
      ·
        refine ⟨13850656562283275835819161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9233771041522183890546107 13850656562283275835819161)
        ·
          refine ⟨10387992421712456876864371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13850656562283275835819161 10387992421712456876864371)
          ·
            refine ⟨15581988632568685315296557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10387992421712456876864371 15581988632568685315296557)
            ·
              refine ⟨5843245737213256993236209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15581988632568685315296557 5843245737213256993236209)
              ·
                refine ⟨4382434302909942744927157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5843245737213256993236209 4382434302909942744927157)
                ·
                  refine ⟨410853215897807132336921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4382434302909942744927157 410853215897807132336921)
                  ·
                    rfl

theorem cell21_1800301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_1800301 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1800301 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1800301 prefixEnd_1800301 := by exact prefixLift 1800301
  have htrace : WordTrace (prefixWord ++ tailWord_1800301) baseStart_1800301 baseEnd_1800301 := by
    simpa [prefixWord, tailWord_1800301, baseEnd_1800301] using wordTrace_append hprefix tailTrace_1800301
  have hstable : (prefixWord ++ tailWord_1800301).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1800301).length < 2 ^ (prefixWord ++ tailWord_1800301).sum := by decide
  have hdescent : baseEnd_1800301 < baseStart_1800301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1800301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1800329 : List Nat := [1, 2, 1, 1, 4, 2, 10]
def baseStart_1800329 : Nat := 118140960795 + 1800329 * 2 ^ 59
def prefixEnd_1800329 : Nat := 4983230072969 + 3 ^ 40 * 1800329 * 2
def baseEnd_1800329 : Nat := 45651067319920589541133

theorem tailTrace_1800329 : CollatzResearch.WordTrace tailWord_1800329 prefixEnd_1800329 45651067319920589541133 := by
  unfold tailWord_1800329
  simp only [CollatzResearch.WordTrace]
  refine ⟨65663393094722979559236041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43775595396481986372824027 65663393094722979559236041)
  ·
    refine ⟨49247544821042234669427031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65663393094722979559236041 49247544821042234669427031)
    ·
      refine ⟨73871317231563352004140547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49247544821042234669427031 73871317231563352004140547)
      ·
        refine ⟨110806975847345028006210821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73871317231563352004140547 110806975847345028006210821)
        ·
          refine ⟨20776307971377192751164529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110806975847345028006210821 20776307971377192751164529)
          ·
            refine ⟨15582230978532894563373397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20776307971377192751164529 15582230978532894563373397)
            ·
              refine ⟨45651067319920589541133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15582230978532894563373397 45651067319920589541133)
              ·
                rfl

theorem cell21_1800329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 10].length) (baseStart_1800329 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1800329 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1800329 prefixEnd_1800329 := by exact prefixLift 1800329
  have htrace : WordTrace (prefixWord ++ tailWord_1800329) baseStart_1800329 baseEnd_1800329 := by
    simpa [prefixWord, tailWord_1800329, baseEnd_1800329] using wordTrace_append hprefix tailTrace_1800329
  have hstable : (prefixWord ++ tailWord_1800329).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1800329).length < 2 ^ (prefixWord ++ tailWord_1800329).sum := by decide
  have hdescent : baseEnd_1800329 < baseStart_1800329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1800329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1800349 : List Nat := [1, 4, 2, 1, 1, 4, 3, 1, 4]
def baseStart_1800349 : Nat := 118140960795 + 1800349 * 2 ^ 59
def prefixEnd_1800349 : Nat := 4983230072969 + 3 ^ 40 * 1800349 * 2
def baseEnd_1800349 : Nat := 410864170151769715536823

theorem tailTrace_1800349 : CollatzResearch.WordTrace tailWord_1800349 prefixEnd_1800349 410864170151769715536823 := by
  unfold tailWord_1800349
  simp only [CollatzResearch.WordTrace]
  refine ⟨65664122554650522974964101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43776081703100348649976067 65664122554650522974964101)
  ·
    refine ⟨12312022978996973057805769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65664122554650522974964101 12312022978996973057805769)
    ·
      refine ⟨9234017234247729793354327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12312022978996973057805769 9234017234247729793354327)
      ·
        refine ⟨13851025851371594690031491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9234017234247729793354327 13851025851371594690031491)
        ·
          refine ⟨20776538777057392035047237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13851025851371594690031491 20776538777057392035047237)
          ·
            refine ⟨3895601020698261006571357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20776538777057392035047237 3895601020698261006571357)
            ·
              refine ⟨1460850382761847877464259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3895601020698261006571357 1460850382761847877464259)
              ·
                refine ⟨2191275574142771816196389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1460850382761847877464259 2191275574142771816196389)
                ·
                  refine ⟨410864170151769715536823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2191275574142771816196389 410864170151769715536823)
                  ·
                    rfl

theorem cell21_1800349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 3, 1, 4].length) (baseStart_1800349 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1800349 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1800349 prefixEnd_1800349 := by exact prefixLift 1800349
  have htrace : WordTrace (prefixWord ++ tailWord_1800349) baseStart_1800349 baseEnd_1800349 := by
    simpa [prefixWord, tailWord_1800349, baseEnd_1800349] using wordTrace_append hprefix tailTrace_1800349
  have hstable : (prefixWord ++ tailWord_1800349).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1800349).length < 2 ^ (prefixWord ++ tailWord_1800349).sum := by decide
  have hdescent : baseEnd_1800349 < baseStart_1800349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1800349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1800408 : List Nat := [2, 1, 2, 2, 4, 2, 1, 3, 4]
def baseStart_1800408 : Nat := 118140960795 + 1800408 * 2 ^ 59
def prefixEnd_1800408 : Nat := 4983230072969 + 3 ^ 40 * 1800408 * 2
def baseEnd_1800408 : Nat := 410877634755598724053369

theorem tailTrace_1800408 : CollatzResearch.WordTrace tailWord_1800408 prefixEnd_1800408 410877634755598724053369 := by
  unfold tailWord_1800408
  simp only [CollatzResearch.WordTrace]
  refine ⟨32833137230718388025680939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43777516307624517367574585 32833137230718388025680939)
  ·
    refine ⟨49249705846077582038521409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32833137230718388025680939 49249705846077582038521409)
    ·
      refine ⟨36937279384558186528891057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49249705846077582038521409 36937279384558186528891057)
      ·
        refine ⟨27702959538418639896668293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36937279384558186528891057 27702959538418639896668293)
        ·
          refine ⟨5194304913453494980625305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27702959538418639896668293 5194304913453494980625305)
          ·
            refine ⟨3895728685090121235468979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5194304913453494980625305 3895728685090121235468979)
            ·
              refine ⟨5843593027635181853203469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3895728685090121235468979 5843593027635181853203469)
              ·
                refine ⟨2191347385363193194951301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5843593027635181853203469 2191347385363193194951301)
                ·
                  refine ⟨410877634755598724053369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2191347385363193194951301 410877634755598724053369)
                  ·
                    rfl

theorem cell21_1800408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 3, 4].length) (baseStart_1800408 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1800408 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1800408 prefixEnd_1800408 := by exact prefixLift 1800408
  have htrace : WordTrace (prefixWord ++ tailWord_1800408) baseStart_1800408 baseEnd_1800408 := by
    simpa [prefixWord, tailWord_1800408, baseEnd_1800408] using wordTrace_append hprefix tailTrace_1800408
  have hstable : (prefixWord ++ tailWord_1800408).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1800408).length < 2 ^ (prefixWord ++ tailWord_1800408).sum := by decide
  have hdescent : baseEnd_1800408 < baseStart_1800408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1800408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1800481 : List Nat := [1, 2, 3, 2, 1, 1, 2, 9]
def baseStart_1800481 : Nat := 118140960795 + 1800481 * 2 ^ 59
def prefixEnd_1800481 : Nat := 4983230072969 + 3 ^ 40 * 1800481 * 2
def baseEnd_1800481 : Nat := 136964764783388939778851

theorem tailTrace_1800481 : CollatzResearch.WordTrace tailWord_1800481 prefixEnd_1800481 136964764783388939778851 := by
  unfold tailWord_1800481
  simp only [CollatzResearch.WordTrace]
  refine ⟨65668936990172309518769297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43779291326781539679179531 65668936990172309518769297)
  ·
    refine ⟨49251702742629232139076973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65668936990172309518769297 49251702742629232139076973)
    ·
      refine ⟨18469388528485962052153865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49251702742629232139076973 18469388528485962052153865)
      ·
        refine ⟨13852041396364471539115399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18469388528485962052153865 13852041396364471539115399)
        ·
          refine ⟨20778062094546707308673099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13852041396364471539115399 20778062094546707308673099)
          ·
            refine ⟨31167093141820060963009649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20778062094546707308673099 31167093141820060963009649)
            ·
              refine ⟨23375319856365045722257237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31167093141820060963009649 23375319856365045722257237)
              ·
                refine ⟨136964764783388939778851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23375319856365045722257237 136964764783388939778851)
                ·
                  rfl

theorem cell21_1800481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 9].length) (baseStart_1800481 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1800481 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1800481 prefixEnd_1800481 := by exact prefixLift 1800481
  have htrace : WordTrace (prefixWord ++ tailWord_1800481) baseStart_1800481 baseEnd_1800481 := by
    simpa [prefixWord, tailWord_1800481, baseEnd_1800481] using wordTrace_append hprefix tailTrace_1800481
  have hstable : (prefixWord ++ tailWord_1800481).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1800481).length < 2 ^ (prefixWord ++ tailWord_1800481).sum := by decide
  have hdescent : baseEnd_1800481 < baseStart_1800481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1800481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1800498 : List Nat := [3, 2, 1, 1, 5, 1, 8]
def baseStart_1800498 : Nat := 118140960795 + 1800498 * 2 ^ 59
def prefixEnd_1800498 : Nat := 4983230072969 + 3 ^ 40 * 1800498 * 2
def baseEnd_1800498 : Nat := 45655352664642063061465

theorem tailTrace_1800498 : CollatzResearch.WordTrace tailWord_1800498 prefixEnd_1800498 45655352664642063061465 := by
  unfold tailWord_1800498
  simp only [CollatzResearch.WordTrace]
  refine ⟨16417389257777680355534537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43779704687407147614758765 16417389257777680355534537)
  ·
    refine ⟨12313041943333260266650903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16417389257777680355534537 12313041943333260266650903)
    ·
      refine ⟨18469562914999890399976355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12313041943333260266650903 18469562914999890399976355)
      ·
        refine ⟨27704344372499835599964533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18469562914999890399976355 27704344372499835599964533)
        ·
          refine ⟨2597282284921859587496675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27704344372499835599964533 2597282284921859587496675)
          ·
            refine ⟨3895923427382789381245013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2597282284921859587496675 3895923427382789381245013)
            ·
              refine ⟨45655352664642063061465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3895923427382789381245013 45655352664642063061465)
              ·
                rfl

theorem cell21_1800498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 8].length) (baseStart_1800498 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1800498 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1800498 prefixEnd_1800498 := by exact prefixLift 1800498
  have htrace : WordTrace (prefixWord ++ tailWord_1800498) baseStart_1800498 baseEnd_1800498 := by
    simpa [prefixWord, tailWord_1800498, baseEnd_1800498] using wordTrace_append hprefix tailTrace_1800498
  have hstable : (prefixWord ++ tailWord_1800498).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1800498).length < 2 ^ (prefixWord ++ tailWord_1800498).sum := by decide
  have hdescent : baseEnd_1800498 < baseStart_1800498 := by decide
  rcases family_descends (prefixWord ++ tailWord_1800498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1800577 : List Nat := [1, 2, 4, 3, 1, 1, 4, 1, 4]
def baseStart_1800577 : Nat := 118140960795 + 1800577 * 2 ^ 59
def prefixEnd_1800577 : Nat := 4983230072969 + 3 ^ 40 * 1800577 * 2
def baseEnd_1800577 : Nat := 410916202858091985736357

theorem tailTrace_1800577 : CollatzResearch.WordTrace tailWord_1800577 prefixEnd_1800577 410916202858091985736357 := by
  unfold tailWord_1800577
  simp only [CollatzResearch.WordTrace]
  refine ⟨65672438397824517914263985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43781625598549678609509323 65672438397824517914263985)
  ·
    refine ⟨49254328798368388435697989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65672438397824517914263985 49254328798368388435697989)
    ·
      refine ⟨9235186649694072831693373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49254328798368388435697989 9235186649694072831693373)
      ·
        refine ⟨3463194993635277311885015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9235186649694072831693373 3463194993635277311885015)
        ·
          refine ⟨5194792490452915967827523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3463194993635277311885015 5194792490452915967827523)
          ·
            refine ⟨7792188735679373951741285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5194792490452915967827523 7792188735679373951741285)
            ·
              refine ⟨1461035387939882615951491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7792188735679373951741285 1461035387939882615951491)
              ·
                refine ⟨2191553081909823923927237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1461035387939882615951491 2191553081909823923927237)
                ·
                  refine ⟨410916202858091985736357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2191553081909823923927237 410916202858091985736357)
                  ·
                    rfl

theorem cell21_1800577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 4, 1, 4].length) (baseStart_1800577 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1800577 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1800577 prefixEnd_1800577 := by exact prefixLift 1800577
  have htrace : WordTrace (prefixWord ++ tailWord_1800577) baseStart_1800577 baseEnd_1800577 := by
    simpa [prefixWord, tailWord_1800577, baseEnd_1800577] using wordTrace_append hprefix tailTrace_1800577
  have hstable : (prefixWord ++ tailWord_1800577).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1800577).length < 2 ^ (prefixWord ++ tailWord_1800577).sum := by decide
  have hdescent : baseEnd_1800577 < baseStart_1800577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1800577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1800636 : List Nat := [2, 2, 2, 4, 1, 1, 2, 3, 4]
def baseStart_1800636 : Nat := 118140960795 + 1800636 * 2 ^ 59
def prefixEnd_1800636 : Nat := 4983230072969 + 3 ^ 40 * 1800636 * 2
def baseEnd_1800636 : Nat := 410929667461920994252903

theorem tailTrace_1800636 : CollatzResearch.WordTrace tailWord_1800636 prefixEnd_1800636 410929667461920994252903 := by
  unfold tailWord_1800636
  simp only [CollatzResearch.WordTrace]
  refine ⟨32837295152305385495330881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43783060203073847327107841 32837295152305385495330881)
  ·
    refine ⟨24627971364229039121498161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32837295152305385495330881 24627971364229039121498161)
    ·
      refine ⟨18470978523171779341123621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24627971364229039121498161 18470978523171779341123621)
      ·
        refine ⟨3463308473094708626460679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18470978523171779341123621 3463308473094708626460679)
        ·
          refine ⟨5194962709642062939691019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3463308473094708626460679 5194962709642062939691019)
          ·
            refine ⟨7792444064463094409536529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5194962709642062939691019 7792444064463094409536529)
            ·
              refine ⟨5844333048347320807152397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7792444064463094409536529 5844333048347320807152397)
              ·
                refine ⟨2191624893130245302682149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5844333048347320807152397 2191624893130245302682149)
                ·
                  refine ⟨410929667461920994252903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2191624893130245302682149 410929667461920994252903)
                  ·
                    rfl

theorem cell21_1800636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 3, 4].length) (baseStart_1800636 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1800636 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1800636 prefixEnd_1800636 := by exact prefixLift 1800636
  have htrace : WordTrace (prefixWord ++ tailWord_1800636) baseStart_1800636 baseEnd_1800636 := by
    simpa [prefixWord, tailWord_1800636, baseEnd_1800636] using wordTrace_append hprefix tailTrace_1800636
  have hstable : (prefixWord ++ tailWord_1800636).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1800636).length < 2 ^ (prefixWord ++ tailWord_1800636).sum := by decide
  have hdescent : baseEnd_1800636 < baseStart_1800636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1800636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1800650 : List Nat := [3, 1, 2, 1, 2, 2, 5, 5]
def baseStart_1800650 : Nat := 118140960795 + 1800650 * 2 ^ 59
def prefixEnd_1800650 : Nat := 4983230072969 + 3 ^ 40 * 1800650 * 2
def baseEnd_1800650 : Nat := 136977620817553360339847

theorem tailTrace_1800650 : CollatzResearch.WordTrace tailWord_1800650 prefixEnd_1800650 136977620817553360339847 := by
  unfold tailWord_1800650
  simp only [CollatzResearch.WordTrace]
  refine ⟨16418775231640012845417851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43783400617706700921114269 16418775231640012845417851)
  ·
    refine ⟨24628162847460019268126777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16418775231640012845417851 24628162847460019268126777)
    ·
      refine ⟨18471122135595014451095083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24628162847460019268126777 18471122135595014451095083)
      ·
        refine ⟨27706683203392521676642625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18471122135595014451095083 27706683203392521676642625)
        ·
          refine ⟨20780012402544391257481969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27706683203392521676642625 20780012402544391257481969)
          ·
            refine ⟨15585009301908293443111477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20780012402544391257481969 15585009301908293443111477)
            ·
              refine ⟨1461094622053902510291701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15585009301908293443111477 1461094622053902510291701)
              ·
                refine ⟨136977620817553360339847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1461094622053902510291701 136977620817553360339847)
                ·
                  rfl

theorem cell21_1800650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 5, 5].length) (baseStart_1800650 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1800650 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1800650 prefixEnd_1800650 := by exact prefixLift 1800650
  have htrace : WordTrace (prefixWord ++ tailWord_1800650) baseStart_1800650 baseEnd_1800650 := by
    simpa [prefixWord, tailWord_1800650, baseEnd_1800650] using wordTrace_append hprefix tailTrace_1800650
  have hstable : (prefixWord ++ tailWord_1800650).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1800650).length < 2 ^ (prefixWord ++ tailWord_1800650).sum := by decide
  have hdescent : baseEnd_1800650 < baseStart_1800650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1800650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1800788 : List Nat := [2, 4, 1, 1, 1, 4, 2, 2, 4]
def baseStart_1800788 : Nat := 118140960795 + 1800788 * 2 ^ 59
def prefixEnd_1800788 : Nat := 4983230072969 + 3 ^ 40 * 1800788 * 2
def baseEnd_1800788 : Nat := 410964355932802507719259

theorem tailTrace_1800788 : CollatzResearch.WordTrace tailWord_1800788 prefixEnd_1800788 410964355932802507719259 := by
  unfold tailWord_1800788
  simp only [CollatzResearch.WordTrace]
  refine ⟨32840067100030050475097509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43786756133373400633463345 32840067100030050475097509)
  ·
    refine ⟨6157512581255634464080783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32840067100030050475097509 6157512581255634464080783)
    ·
      refine ⟨9236268871883451696121175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6157512581255634464080783 9236268871883451696121175)
      ·
        refine ⟨13854403307825177544181763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9236268871883451696121175 13854403307825177544181763)
        ·
          refine ⟨20781604961737766316272645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13854403307825177544181763 20781604961737766316272645)
          ·
            refine ⟨3896550930325831184301121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20781604961737766316272645 3896550930325831184301121)
            ·
              refine ⟨2922413197744373388225841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3896550930325831184301121 2922413197744373388225841)
              ·
                refine ⟨2191809898308280041169381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2922413197744373388225841 2191809898308280041169381)
                ·
                  refine ⟨410964355932802507719259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2191809898308280041169381 410964355932802507719259)
                  ·
                    rfl

theorem cell21_1800788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 2, 4].length) (baseStart_1800788 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1800788 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1800788 prefixEnd_1800788 := by exact prefixLift 1800788
  have htrace : WordTrace (prefixWord ++ tailWord_1800788) baseStart_1800788 baseEnd_1800788 := by
    simpa [prefixWord, tailWord_1800788, baseEnd_1800788] using wordTrace_append hprefix tailTrace_1800788
  have hstable : (prefixWord ++ tailWord_1800788).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1800788).length < 2 ^ (prefixWord ++ tailWord_1800788).sum := by decide
  have hdescent : baseEnd_1800788 < baseStart_1800788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1800788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1800799 : List Nat := [1, 1, 2, 3, 1, 1, 1, 2, 9]
def baseStart_1800799 : Nat := 118140960795 + 1800799 * 2 ^ 59
def prefixEnd_1800799 : Nat := 4983230072969 + 3 ^ 40 * 1800799 * 2
def baseEnd_1800799 : Nat := 410966866282668933035903

theorem tailTrace_1800799 : CollatzResearch.WordTrace tailWord_1800799 prefixEnd_1800799 410966866282668933035903 := by
  unfold tailWord_1800799
  simp only [CollatzResearch.WordTrace]
  refine ⟨65680535403020249828845451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43787023602013499885896967 65680535403020249828845451)
  ·
    refine ⟨98520803104530374743268177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65680535403020249828845451 98520803104530374743268177)
    ·
      refine ⟨73890602328397781057451133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98520803104530374743268177 73890602328397781057451133)
      ·
        refine ⟨27708975873149167896544175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73890602328397781057451133 27708975873149167896544175)
        ·
          refine ⟨41563463809723751844816263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27708975873149167896544175 41563463809723751844816263)
          ·
            refine ⟨62345195714585627767224395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41563463809723751844816263 62345195714585627767224395)
            ·
              refine ⟨93517793571878441650836593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62345195714585627767224395 93517793571878441650836593)
              ·
                refine ⟨70138345178908831238127445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93517793571878441650836593 70138345178908831238127445)
                ·
                  refine ⟨410966866282668933035903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 70138345178908831238127445 410966866282668933035903)
                  ·
                    rfl

theorem cell21_1800799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 9].length) (baseStart_1800799 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1800799 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1800799 prefixEnd_1800799 := by exact prefixLift 1800799
  have htrace : WordTrace (prefixWord ++ tailWord_1800799) baseStart_1800799 baseEnd_1800799 := by
    simpa [prefixWord, tailWord_1800799, baseEnd_1800799] using wordTrace_append hprefix tailTrace_1800799
  have hstable : (prefixWord ++ tailWord_1800799).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1800799).length < 2 ^ (prefixWord ++ tailWord_1800799).sum := by decide
  have hdescent : baseEnd_1800799 < baseStart_1800799 := by decide
  rcases family_descends (prefixWord ++ tailWord_1800799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1800850 : List Nat := [3, 2, 3, 1, 2, 1, 2, 4, 3]
def baseStart_1800850 : Nat := 118140960795 + 1800850 * 2 ^ 59
def prefixEnd_1800850 : Nat := 4983230072969 + 3 ^ 40 * 1800850 * 2
def baseEnd_1800850 : Nat := 410978505177504177685799

theorem tailTrace_1800850 : CollatzResearch.WordTrace tailWord_1800850 prefixEnd_1800850 410978505177504177685799 := by
  unfold tailWord_1800850
  simp only [CollatzResearch.WordTrace]
  refine ⟨16420598881458871384738001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43788263683890323692634669 16420598881458871384738001)
  ·
    refine ⟨12315449161094153538553501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16420598881458871384738001 12315449161094153538553501)
    ·
      refine ⟨4618293435410307576957563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12315449161094153538553501 4618293435410307576957563)
      ·
        refine ⟨6927440153115461365436345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4618293435410307576957563 6927440153115461365436345)
        ·
          refine ⟨5195580114836596024077259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6927440153115461365436345 5195580114836596024077259)
          ·
            refine ⟨7793370172254894036115889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5195580114836596024077259 7793370172254894036115889)
            ·
              refine ⟨5845027629191170527086917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7793370172254894036115889 5845027629191170527086917)
              ·
                refine ⟨1095942680473344473828797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5845027629191170527086917 1095942680473344473828797)
                ·
                  refine ⟨410978505177504177685799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1095942680473344473828797 410978505177504177685799)
                  ·
                    rfl

theorem cell21_1800850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 4, 3].length) (baseStart_1800850 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1800850 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1800850 prefixEnd_1800850 := by exact prefixLift 1800850
  have htrace : WordTrace (prefixWord ++ tailWord_1800850) baseStart_1800850 baseEnd_1800850 := by
    simpa [prefixWord, tailWord_1800850, baseEnd_1800850] using wordTrace_append hprefix tailTrace_1800850
  have hstable : (prefixWord ++ tailWord_1800850).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1800850).length < 2 ^ (prefixWord ++ tailWord_1800850).sum := by decide
  have hdescent : baseEnd_1800850 < baseStart_1800850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1800850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1801013 : List Nat := [1, 3, 3, 1, 3, 2, 8]
def baseStart_1801013 : Nat := 118140960795 + 1801013 * 2 ^ 59
def prefixEnd_1801013 : Nat := 4983230072969 + 3 ^ 40 * 1801013 * 2
def baseEnd_1801013 : Nat := 45668411555361346274311

theorem tailTrace_1801013 : CollatzResearch.WordTrace tailWord_1801013 prefixEnd_1801013 45668411555361346274311 := by
  unfold tailWord_1801013
  simp only [CollatzResearch.WordTrace]
  refine ⟨65688340624244964377135693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43792227082829976251423795 65688340624244964377135693)
  ·
    refine ⟨24633127734091861641425885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65688340624244964377135693 24633127734091861641425885)
    ·
      refine ⟨9237422900284448115534707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24633127734091861641425885 9237422900284448115534707)
      ·
        refine ⟨13856134350426672173302061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9237422900284448115534707 13856134350426672173302061)
        ·
          refine ⟨5196050381410002064988273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13856134350426672173302061 5196050381410002064988273)
          ·
            refine ⟨3897037786057501548741205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5196050381410002064988273 3897037786057501548741205)
            ·
              refine ⟨45668411555361346274311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3897037786057501548741205 45668411555361346274311)
              ·
                rfl

theorem cell21_1801013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 8].length) (baseStart_1801013 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1801013 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1801013 prefixEnd_1801013 := by exact prefixLift 1801013
  have htrace : WordTrace (prefixWord ++ tailWord_1801013) baseStart_1801013 baseEnd_1801013 := by
    simpa [prefixWord, tailWord_1801013, baseEnd_1801013] using wordTrace_append hprefix tailTrace_1801013
  have hstable : (prefixWord ++ tailWord_1801013).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1801013).length < 2 ^ (prefixWord ++ tailWord_1801013).sum := by decide
  have hdescent : baseEnd_1801013 < baseStart_1801013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1801013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1801061 : List Nat := [1, 3, 1, 3, 1, 1, 5, 3, 3]
def baseStart_1801061 : Nat := 118140960795 + 1801061 * 2 ^ 59
def prefixEnd_1801061 : Nat := 4983230072969 + 3 ^ 40 * 1801061 * 2
def baseEnd_1801061 : Nat := 411026658252214699668701

theorem tailTrace_1801061 : CollatzResearch.WordTrace tailWord_1801061 prefixEnd_1801061 411026658252214699668701 := by
  unfold tailWord_1801061
  simp only [CollatzResearch.WordTrace]
  refine ⟨65690091328071068574883037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43793394218714045716588691 65690091328071068574883037)
  ·
    refine ⟨24633784248026650715581139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65690091328071068574883037 24633784248026650715581139)
    ·
      refine ⟨36950676372039976073371709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24633784248026650715581139 36950676372039976073371709)
      ·
        refine ⟨13856503639514991027514391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36950676372039976073371709 13856503639514991027514391)
        ·
          refine ⟨20784755459272486541271587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13856503639514991027514391 20784755459272486541271587)
          ·
            refine ⟨31177133188908729811907381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20784755459272486541271587 31177133188908729811907381)
            ·
              refine ⟨2922856236460193419866317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31177133188908729811907381 2922856236460193419866317)
              ·
                refine ⟨1096071088672572532449869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2922856236460193419866317 1096071088672572532449869)
                ·
                  refine ⟨411026658252214699668701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1096071088672572532449869 411026658252214699668701)
                  ·
                    rfl

theorem cell21_1801061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 3, 3].length) (baseStart_1801061 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1801061 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1801061 prefixEnd_1801061 := by exact prefixLift 1801061
  have htrace : WordTrace (prefixWord ++ tailWord_1801061) baseStart_1801061 baseEnd_1801061 := by
    simpa [prefixWord, tailWord_1801061, baseEnd_1801061] using wordTrace_append hprefix tailTrace_1801061
  have hstable : (prefixWord ++ tailWord_1801061).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1801061).length < 2 ^ (prefixWord ++ tailWord_1801061).sum := by decide
  have hdescent : baseEnd_1801061 < baseStart_1801061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1801061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1801072 : List Nat := [2, 1, 1, 1, 4, 1, 11]
def baseStart_1801072 : Nat := 118140960795 + 1801072 * 2 ^ 59
def prefixEnd_1801072 : Nat := 4983230072969 + 3 ^ 40 * 1801072 * 2
def baseEnd_1801072 : Nat := 45669907622453458331705

theorem tailTrace_1801072 : CollatzResearch.WordTrace tailWord_1801072 prefixEnd_1801072 45669907622453458331705 := by
  unfold tailWord_1801072
  simp only [CollatzResearch.WordTrace]
  refine ⟨32845246265515608726766735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43793661687354144969022313 32845246265515608726766735)
  ·
    refine ⟨49267869398273413090150103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32845246265515608726766735 49267869398273413090150103)
    ·
      refine ⟨73901804097410119635225155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49267869398273413090150103 73901804097410119635225155)
      ·
        refine ⟨110852706146115179452837733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73901804097410119635225155 110852706146115179452837733)
        ·
          refine ⟨20784882402396596147407075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110852706146115179452837733 20784882402396596147407075)
          ·
            refine ⟨31177323603594894221110613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20784882402396596147407075 31177323603594894221110613)
            ·
              refine ⟨45669907622453458331705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 31177323603594894221110613 45669907622453458331705)
              ·
                rfl

theorem cell21_1801072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 11].length) (baseStart_1801072 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1801072 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1801072 prefixEnd_1801072 := by exact prefixLift 1801072
  have htrace : WordTrace (prefixWord ++ tailWord_1801072) baseStart_1801072 baseEnd_1801072 := by
    simpa [prefixWord, tailWord_1801072, baseEnd_1801072] using wordTrace_append hprefix tailTrace_1801072
  have hstable : (prefixWord ++ tailWord_1801072).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1801072).length < 2 ^ (prefixWord ++ tailWord_1801072).sum := by decide
  have hdescent : baseEnd_1801072 < baseStart_1801072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1801072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1801078 : List Nat := [5, 1, 1, 3, 1, 3, 1, 1, 5]
def baseStart_1801078 : Nat := 118140960795 + 1801078 * 2 ^ 59
def prefixEnd_1801078 : Nat := 4983230072969 + 3 ^ 40 * 1801078 * 2
def baseEnd_1801078 : Nat := 411030537883826447885333

theorem tailTrace_1801078 : CollatzResearch.WordTrace tailWord_1801078 prefixEnd_1801078 411030537883826447885333 := by
  unfold tailWord_1801078
  simp only [CollatzResearch.WordTrace]
  refine ⟨4105669460563092529890743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43793807579339653652167925 4105669460563092529890743)
  ·
    refine ⟨6158504190844638794836115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4105669460563092529890743 6158504190844638794836115)
    ·
      refine ⟨9237756286266958192254173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6158504190844638794836115 9237756286266958192254173)
      ·
        refine ⟨3464158607350109322095315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9237756286266958192254173 3464158607350109322095315)
        ·
          refine ⟨5196237911025163983142973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3464158607350109322095315 5196237911025163983142973)
          ·
            refine ⟨1948589216634436493678615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5196237911025163983142973 1948589216634436493678615)
            ·
              refine ⟨2922883824951654740517923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1948589216634436493678615 2922883824951654740517923)
              ·
                refine ⟨4384325737427482110776885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2922883824951654740517923 4384325737427482110776885)
                ·
                  refine ⟨411030537883826447885333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4384325737427482110776885 411030537883826447885333)
                  ·
                    rfl

theorem cell21_1801078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 1, 5].length) (baseStart_1801078 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1801078 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1801078 prefixEnd_1801078 := by exact prefixLift 1801078
  have htrace : WordTrace (prefixWord ++ tailWord_1801078) baseStart_1801078 baseEnd_1801078 := by
    simpa [prefixWord, tailWord_1801078, baseEnd_1801078] using wordTrace_append hprefix tailTrace_1801078
  have hstable : (prefixWord ++ tailWord_1801078).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1801078).length < 2 ^ (prefixWord ++ tailWord_1801078).sum := by decide
  have hdescent : baseEnd_1801078 < baseStart_1801078 := by decide
  rcases family_descends (prefixWord ++ tailWord_1801078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1801210 : List Nat := [3, 1, 1, 1, 1, 2, 1, 7, 4]
def baseStart_1801210 : Nat := 118140960795 + 1801210 * 2 ^ 59
def prefixEnd_1801210 : Nat := 4983230072969 + 3 ^ 40 * 1801210 * 2
def baseEnd_1801210 : Nat := 411060662082223551685063

theorem tailTrace_1801210 : CollatzResearch.WordTrace tailWord_1801210 prefixEnd_1801210 411060662082223551685063 := by
  unfold tailWord_1801210
  simp only [CollatzResearch.WordTrace]
  refine ⟨16423881451132816755514271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43797017203020844681371389 16423881451132816755514271)
  ·
    refine ⟨24635822176699225133271407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16423881451132816755514271 24635822176699225133271407)
    ·
      refine ⟨36953733265048837699907111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24635822176699225133271407 36953733265048837699907111)
      ·
        refine ⟨55430599897573256549860667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36953733265048837699907111 55430599897573256549860667)
        ·
          refine ⟨83145899846359884824791001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55430599897573256549860667 83145899846359884824791001)
          ·
            refine ⟨62359424884769913618593251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83145899846359884824791001 62359424884769913618593251)
            ·
              refine ⟨93539137327154870427889877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62359424884769913618593251 93539137327154870427889877)
              ·
                refine ⟨2192323531105192275653669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 93539137327154870427889877 2192323531105192275653669)
                ·
                  refine ⟨411060662082223551685063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2192323531105192275653669 411060662082223551685063)
                  ·
                    rfl

theorem cell21_1801210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 7, 4].length) (baseStart_1801210 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1801210 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1801210 prefixEnd_1801210 := by exact prefixLift 1801210
  have htrace : WordTrace (prefixWord ++ tailWord_1801210) baseStart_1801210 baseEnd_1801210 := by
    simpa [prefixWord, tailWord_1801210, baseEnd_1801210] using wordTrace_append hprefix tailTrace_1801210
  have hstable : (prefixWord ++ tailWord_1801210).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1801210).length < 2 ^ (prefixWord ++ tailWord_1801210).sum := by decide
  have hdescent : baseEnd_1801210 < baseStart_1801210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1801210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1801230 : List Nat := [4, 1, 1, 2, 2, 4, 1, 3, 3]
def baseStart_1801230 : Nat := 118140960795 + 1801230 * 2 ^ 59
def prefixEnd_1801230 : Nat := 4983230072969 + 3 ^ 40 * 1801230 * 2
def baseEnd_1801230 : Nat := 411065226354707961351689

theorem tailTrace_1801230 : CollatzResearch.WordTrace tailWord_1801230 prefixEnd_1801230 411065226354707961351689 := by
  unfold tailWord_1801230
  simp only [CollatzResearch.WordTrace]
  refine ⟨8212031908057351304723143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43797503509639206958523429 8212031908057351304723143)
  ·
    refine ⟨12318047862086026957084715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8212031908057351304723143 12318047862086026957084715)
    ·
      refine ⟨18477071793129040435627073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12318047862086026957084715 18477071793129040435627073)
      ·
        refine ⟨13857803844846780326720305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18477071793129040435627073 13857803844846780326720305)
        ·
          refine ⟨10393352883635085245040229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13857803844846780326720305 10393352883635085245040229)
          ·
            refine ⟨1948753665681578483445043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10393352883635085245040229 1948753665681578483445043)
            ·
              refine ⟨2923130498522367725167565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1948753665681578483445043 2923130498522367725167565)
              ·
                refine ⟨1096173936945887896937837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2923130498522367725167565 1096173936945887896937837)
                ·
                  refine ⟨411065226354707961351689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1096173936945887896937837 411065226354707961351689)
                  ·
                    rfl

theorem cell21_1801230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 3, 3].length) (baseStart_1801230 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1801230 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1801230 prefixEnd_1801230 := by exact prefixLift 1801230
  have htrace : WordTrace (prefixWord ++ tailWord_1801230) baseStart_1801230 baseEnd_1801230 := by
    simpa [prefixWord, tailWord_1801230, baseEnd_1801230] using wordTrace_append hprefix tailTrace_1801230
  have hstable : (prefixWord ++ tailWord_1801230).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1801230).length < 2 ^ (prefixWord ++ tailWord_1801230).sum := by decide
  have hdescent : baseEnd_1801230 < baseStart_1801230 := by decide
  rcases family_descends (prefixWord ++ tailWord_1801230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1801258 : List Nat := [3, 1, 4, 1, 3, 1, 2, 6]
def baseStart_1801258 : Nat := 118140960795 + 1801258 * 2 ^ 59
def prefixEnd_1801258 : Nat := 4983230072969 + 3 ^ 40 * 1801258 * 2
def baseEnd_1801258 : Nat := 137023872112062044961655

theorem tailTrace_1801258 : CollatzResearch.WordTrace tailWord_1801258 prefixEnd_1801258 137023872112062044961655 := by
  unfold tailWord_1801258
  simp only [CollatzResearch.WordTrace]
  refine ⟨16424319127089342804951107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43798184338904914146536285 16424319127089342804951107)
  ·
    refine ⟨24636478690634014207426661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16424319127089342804951107 24636478690634014207426661)
    ·
      refine ⟨4619339754493877663892499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24636478690634014207426661 4619339754493877663892499)
      ·
        refine ⟨6929009631740816495838749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4619339754493877663892499 6929009631740816495838749)
        ·
          refine ⟨2598378611902806185939531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6929009631740816495838749 2598378611902806185939531)
          ·
            refine ⟨3897567917854209278909297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2598378611902806185939531 3897567917854209278909297)
            ·
              refine ⟨2923175938390656959181973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3897567917854209278909297 2923175938390656959181973)
              ·
                refine ⟨137023872112062044961655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2923175938390656959181973 137023872112062044961655)
                ·
                  rfl

theorem cell21_1801258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 6].length) (baseStart_1801258 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1801258 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1801258 prefixEnd_1801258 := by exact prefixLift 1801258
  have htrace : WordTrace (prefixWord ++ tailWord_1801258) baseStart_1801258 baseEnd_1801258 := by
    simpa [prefixWord, tailWord_1801258, baseEnd_1801258] using wordTrace_append hprefix tailTrace_1801258
  have hstable : (prefixWord ++ tailWord_1801258).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1801258).length < 2 ^ (prefixWord ++ tailWord_1801258).sum := by decide
  have hdescent : baseEnd_1801258 < baseStart_1801258 := by decide
  rcases family_descends (prefixWord ++ tailWord_1801258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1801334 : List Nat := [5, 1, 1, 2, 1, 1, 5, 5]
def baseStart_1801334 : Nat := 118140960795 + 1801334 * 2 ^ 59
def prefixEnd_1801334 : Nat := 4983230072969 + 3 ^ 40 * 1801334 * 2
def baseEnd_1801334 : Nat := 137029653523875630539381

theorem tailTrace_1801334 : CollatzResearch.WordTrace tailWord_1801334 prefixEnd_1801334 137029653523875630539381 := by
  unfold tailWord_1801334
  simp only [CollatzResearch.WordTrace]
  refine ⟨4106253028505127262473191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43800032304054690799714037 4106253028505127262473191)
  ·
    refine ⟨6159379542757690893709787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4106253028505127262473191 6159379542757690893709787)
    ·
      refine ⟨9239069314136536340564681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6159379542757690893709787 9239069314136536340564681)
      ·
        refine ⟨6929301985602402255423511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9239069314136536340564681 6929301985602402255423511)
        ·
          refine ⟨10393952978403603383135267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6929301985602402255423511 10393952978403603383135267)
          ·
            refine ⟨15590929467605405074702901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10393952978403603383135267 15590929467605405074702901)
            ·
              refine ⟨1461649637588006725753397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15590929467605405074702901 1461649637588006725753397)
              ·
                refine ⟨137029653523875630539381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1461649637588006725753397 137029653523875630539381)
                ·
                  rfl

theorem cell21_1801334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 5, 5].length) (baseStart_1801334 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1801334 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1801334 prefixEnd_1801334 := by exact prefixLift 1801334
  have htrace : WordTrace (prefixWord ++ tailWord_1801334) baseStart_1801334 baseEnd_1801334 := by
    simpa [prefixWord, tailWord_1801334, baseEnd_1801334] using wordTrace_append hprefix tailTrace_1801334
  have hstable : (prefixWord ++ tailWord_1801334).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1801334).length < 2 ^ (prefixWord ++ tailWord_1801334).sum := by decide
  have hdescent : baseEnd_1801334 < baseStart_1801334 := by decide
  rcases family_descends (prefixWord ++ tailWord_1801334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1801376 : List Nat := [2, 1, 1, 4, 2, 1, 2, 8]
def baseStart_1801376 : Nat := 118140960795 + 1801376 * 2 ^ 59
def prefixEnd_1801376 : Nat := 4983230072969 + 3 ^ 40 * 1801376 * 2
def baseEnd_1801376 : Nat := 137032848514614717306019

theorem tailTrace_1801376 : CollatzResearch.WordTrace tailWord_1801376 prefixEnd_1801376 137032848514614717306019 := by
  unfold tailWord_1801376
  simp only [CollatzResearch.WordTrace]
  refine ⟨32850790160964938686299991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43801053547953251581733321 32850790160964938686299991)
  ·
    refine ⟨49276185241447408029449987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32850790160964938686299991 49276185241447408029449987)
    ·
      refine ⟨73914277862171112044174981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49276185241447408029449987 73914277862171112044174981)
      ·
        refine ⟨13858927099157083508282809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73914277862171112044174981 13858927099157083508282809)
        ·
          refine ⟨10394195324367812631212107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13858927099157083508282809 10394195324367812631212107)
          ·
            refine ⟨15591292986551718946818161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10394195324367812631212107 15591292986551718946818161)
            ·
              refine ⟨11693469739913789210113621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15591292986551718946818161 11693469739913789210113621)
              ·
                refine ⟨137032848514614717306019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11693469739913789210113621 137032848514614717306019)
                ·
                  rfl

theorem cell21_1801376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 8].length) (baseStart_1801376 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1801376 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1801376 prefixEnd_1801376 := by exact prefixLift 1801376
  have htrace : WordTrace (prefixWord ++ tailWord_1801376) baseStart_1801376 baseEnd_1801376 := by
    simpa [prefixWord, tailWord_1801376, baseEnd_1801376] using wordTrace_append hprefix tailTrace_1801376
  have hstable : (prefixWord ++ tailWord_1801376).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1801376).length < 2 ^ (prefixWord ++ tailWord_1801376).sum := by decide
  have hdescent : baseEnd_1801376 < baseStart_1801376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1801376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1801393 : List Nat := [1, 2, 2, 5, 1, 2, 1, 7]
def baseStart_1801393 : Nat := 118140960795 + 1801393 * 2 ^ 59
def prefixEnd_1801393 : Nat := 4983230072969 + 3 ^ 40 * 1801393 * 2
def baseEnd_1801393 : Nat := 137034141725151966711563

theorem tailTrace_1801393 : CollatzResearch.WordTrace tailWord_1801393 prefixEnd_1801393 137034141725151966711563 := by
  unfold tailWord_1801393
  simp only [CollatzResearch.WordTrace]
  refine ⟨65702200362868289275968833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43801466908578859517312555 65702200362868289275968833)
  ·
    refine ⟨49276650272151216956976625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65702200362868289275968833 49276650272151216956976625)
    ·
      refine ⟨36957487704113412717732469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49276650272151216956976625 36957487704113412717732469)
      ·
        refine ⟨3464764472260632442287419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36957487704113412717732469 3464764472260632442287419)
        ·
          refine ⟨5197146708390948663431129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3464764472260632442287419 5197146708390948663431129)
          ·
            refine ⟨3897860031293211497573347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5197146708390948663431129 3897860031293211497573347)
            ·
              refine ⟨5846790046939817246360021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3897860031293211497573347 5846790046939817246360021)
              ·
                refine ⟨137034141725151966711563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5846790046939817246360021 137034141725151966711563)
                ·
                  rfl

theorem cell21_1801393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 7].length) (baseStart_1801393 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1801393 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1801393 prefixEnd_1801393 := by exact prefixLift 1801393
  have htrace : WordTrace (prefixWord ++ tailWord_1801393) baseStart_1801393 baseEnd_1801393 := by
    simpa [prefixWord, tailWord_1801393, baseEnd_1801393] using wordTrace_append hprefix tailTrace_1801393
  have hstable : (prefixWord ++ tailWord_1801393).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1801393).length < 2 ^ (prefixWord ++ tailWord_1801393).sum := by decide
  have hdescent : baseEnd_1801393 < baseStart_1801393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1801393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1801430 : List Nat := [5, 2, 1, 2, 2, 2, 2, 1, 4]
def baseStart_1801430 : Nat := 118140960795 + 1801430 * 2 ^ 59
def prefixEnd_1801430 : Nat := 4983230072969 + 3 ^ 40 * 1801430 * 2
def baseEnd_1801430 : Nat := 411110869079552058017947

theorem tailTrace_1801430 : CollatzResearch.WordTrace tailWord_1801430 prefixEnd_1801430 411110869079552058017947 := by
  unfold tailWord_1801430
  simp only [CollatzResearch.WordTrace]
  refine ⟨4106471866483390287191609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43802366575822829730043829 4106471866483390287191609)
  ·
    refine ⟨3079853899862542715393707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4106471866483390287191609 3079853899862542715393707)
    ·
      refine ⟨4619780849793814073090561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3079853899862542715393707 4619780849793814073090561)
      ·
        refine ⟨3464835637345360554817921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4619780849793814073090561 3464835637345360554817921)
        ·
          refine ⟨2598626728009020416113441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3464835637345360554817921 2598626728009020416113441)
          ·
            refine ⟨1948970046006765312085081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2598626728009020416113441 1948970046006765312085081)
            ·
              refine ⟨1461727534505073984063811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1948970046006765312085081 1461727534505073984063811)
              ·
                refine ⟨2192591301757610976095717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1461727534505073984063811 2192591301757610976095717)
                ·
                  refine ⟨411110869079552058017947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2192591301757610976095717 411110869079552058017947)
                  ·
                    rfl

theorem cell21_1801430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_1801430 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1801430 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1801430 prefixEnd_1801430 := by exact prefixLift 1801430
  have htrace : WordTrace (prefixWord ++ tailWord_1801430) baseStart_1801430 baseEnd_1801430 := by
    simpa [prefixWord, tailWord_1801430, baseEnd_1801430] using wordTrace_append hprefix tailTrace_1801430
  have hstable : (prefixWord ++ tailWord_1801430).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1801430).length < 2 ^ (prefixWord ++ tailWord_1801430).sum := by decide
  have hdescent : baseEnd_1801430 < baseStart_1801430 := by decide
  rcases family_descends (prefixWord ++ tailWord_1801430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1801452 : List Nat := [2, 2, 1, 1, 2, 4, 2, 7]
def baseStart_1801452 : Nat := 118140960795 + 1801452 * 2 ^ 59
def prefixEnd_1801452 : Nat := 4983230072969 + 3 ^ 40 * 1801452 * 2
def baseEnd_1801452 : Nat := 137038629926428302883745

theorem tailTrace_1801452 : CollatzResearch.WordTrace tailWord_1801452 prefixEnd_1801452 137038629926428302883745 := by
  unfold tailWord_1801452
  simp only [CollatzResearch.WordTrace]
  refine ⟨32852176134827271176183305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43802901513103028234911073 32852176134827271176183305)
  ·
    refine ⟨24639132101120453382137479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32852176134827271176183305 24639132101120453382137479)
    ·
      refine ⟨36958698151680680073206219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24639132101120453382137479 36958698151680680073206219)
      ·
        refine ⟨55438047227521020109809329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36958698151680680073206219 55438047227521020109809329)
        ·
          refine ⟨41578535420640765082356997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55438047227521020109809329 41578535420640765082356997)
          ·
            refine ⟨7795975391370143452941937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41578535420640765082356997 7795975391370143452941937)
            ·
              refine ⟨5846981543527607589706453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7795975391370143452941937 5846981543527607589706453)
              ·
                refine ⟨137038629926428302883745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5846981543527607589706453 137038629926428302883745)
                ·
                  rfl

theorem cell21_1801452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 7].length) (baseStart_1801452 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1801452 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1801452 prefixEnd_1801452 := by exact prefixLift 1801452
  have htrace : WordTrace (prefixWord ++ tailWord_1801452) baseStart_1801452 baseEnd_1801452 := by
    simpa [prefixWord, tailWord_1801452, baseEnd_1801452] using wordTrace_append hprefix tailTrace_1801452
  have hstable : (prefixWord ++ tailWord_1801452).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1801452).length < 2 ^ (prefixWord ++ tailWord_1801452).sum := by decide
  have hdescent : baseEnd_1801452 < baseStart_1801452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1801452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1801559 : List Nat := [1, 1, 3, 2, 3, 2, 2, 2, 5]
def baseStart_1801559 : Nat := 118140960795 + 1801559 * 2 ^ 59
def prefixEnd_1801559 : Nat := 4983230072969 + 3 ^ 40 * 1801559 * 2
def baseEnd_1801559 : Nat := 411140308637076500367683

theorem tailTrace_1801559 : CollatzResearch.WordTrace tailWord_1801559 prefixEnd_1801559 411140308637076500367683 := by
  unfold tailWord_1801559
  simp only [CollatzResearch.WordTrace]
  refine ⟨65708254880266899626511731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43805503253511266417674487 65708254880266899626511731)
  ·
    refine ⟨98562382320400349439767597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65708254880266899626511731 98562382320400349439767597)
    ·
      refine ⟨36960893370150131039912849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98562382320400349439767597 36960893370150131039912849)
      ·
        refine ⟨27720670027612598279934637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36960893370150131039912849 27720670027612598279934637)
        ·
          refine ⟨10395251260354724354975489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27720670027612598279934637 10395251260354724354975489)
          ·
            refine ⟨7796438445266043266231617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10395251260354724354975489 7796438445266043266231617)
            ·
              refine ⟨5847328833949532449673713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7796438445266043266231617 5847328833949532449673713)
              ·
                refine ⟨4385496625462149337255285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5847328833949532449673713 4385496625462149337255285)
                ·
                  refine ⟨411140308637076500367683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4385496625462149337255285 411140308637076500367683)
                  ·
                    rfl

theorem cell21_1801559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 2, 5].length) (baseStart_1801559 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1801559 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1801559 prefixEnd_1801559 := by exact prefixLift 1801559
  have htrace : WordTrace (prefixWord ++ tailWord_1801559) baseStart_1801559 baseEnd_1801559 := by
    simpa [prefixWord, tailWord_1801559, baseEnd_1801559] using wordTrace_append hprefix tailTrace_1801559
  have hstable : (prefixWord ++ tailWord_1801559).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1801559).length < 2 ^ (prefixWord ++ tailWord_1801559).sum := by decide
  have hdescent : baseEnd_1801559 < baseStart_1801559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1801559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1801573 : List Nat := [1, 3, 1, 3, 1, 2, 1, 1, 8]
def baseStart_1801573 : Nat := 118140960795 + 1801573 * 2 ^ 59
def prefixEnd_1801573 : Nat := 4983230072969 + 3 ^ 40 * 1801573 * 2
def baseEnd_1801573 : Nat := 411143503627815587134321

theorem tailTrace_1801573 : CollatzResearch.WordTrace tailWord_1801573 prefixEnd_1801573 411143503627815587134321 := by
  unfold tailWord_1801573
  simp only [CollatzResearch.WordTrace]
  refine ⟨65708765502216180017521373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43805843668144120011680915 65708765502216180017521373)
  ·
    refine ⟨24640787063331067506570515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65708765502216180017521373 24640787063331067506570515)
    ·
      refine ⟨36961180594996601259855773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24640787063331067506570515 36961180594996601259855773)
      ·
        refine ⟨13860442723123725472445915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36961180594996601259855773 13860442723123725472445915)
        ·
          refine ⟨20790664084685588208668873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13860442723123725472445915 20790664084685588208668873)
          ·
            refine ⟨15592998063514191156501655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20790664084685588208668873 15592998063514191156501655)
            ·
              refine ⟨23389497095271286734752483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15592998063514191156501655 23389497095271286734752483)
              ·
                refine ⟨35084245642906930102128725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23389497095271286734752483 35084245642906930102128725)
                ·
                  refine ⟨411143503627815587134321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35084245642906930102128725 411143503627815587134321)
                  ·
                    rfl

theorem cell21_1801573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 8].length) (baseStart_1801573 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1801573 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1801573 prefixEnd_1801573 := by exact prefixLift 1801573
  have htrace : WordTrace (prefixWord ++ tailWord_1801573) baseStart_1801573 baseEnd_1801573 := by
    simpa [prefixWord, tailWord_1801573, baseEnd_1801573] using wordTrace_append hprefix tailTrace_1801573
  have hstable : (prefixWord ++ tailWord_1801573).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1801573).length < 2 ^ (prefixWord ++ tailWord_1801573).sum := by decide
  have hdescent : baseEnd_1801573 < baseStart_1801573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1801573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1801604 : List Nat := [2, 3, 2, 1, 1, 3, 1, 8]
def baseStart_1801604 : Nat := 118140960795 + 1801604 * 2 ^ 59
def prefixEnd_1801604 : Nat := 4983230072969 + 3 ^ 40 * 1801604 * 2
def baseEnd_1801604 : Nat := 137050192750055474039197

theorem tailTrace_1801604 : CollatzResearch.WordTrace tailWord_1801604 prefixEnd_1801604 137050192750055474039197 := by
  unfold tailWord_1801604
  simp only [CollatzResearch.WordTrace]
  refine ⟨32854948082551936155949933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43806597443402581541266577 32854948082551936155949933)
  ·
    refine ⟨12320605530956976058481225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32854948082551936155949933 12320605530956976058481225)
    ·
      refine ⟨9240454148217732043860919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12320605530956976058481225 9240454148217732043860919)
      ·
        refine ⟨13860681222326598065791379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9240454148217732043860919 13860681222326598065791379)
        ·
          refine ⟨20791021833489897098687069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13860681222326598065791379 20791021833489897098687069)
          ·
            refine ⟨7796633187558711412007651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20791021833489897098687069 7796633187558711412007651)
            ·
              refine ⟨11694949781338067118011477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7796633187558711412007651 11694949781338067118011477)
              ·
                refine ⟨137050192750055474039197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11694949781338067118011477 137050192750055474039197)
                ·
                  rfl

theorem cell21_1801604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 8].length) (baseStart_1801604 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1801604 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1801604 prefixEnd_1801604 := by exact prefixLift 1801604
  have htrace : WordTrace (prefixWord ++ tailWord_1801604) baseStart_1801604 baseEnd_1801604 := by
    simpa [prefixWord, tailWord_1801604, baseEnd_1801604] using wordTrace_append hprefix tailTrace_1801604
  have hstable : (prefixWord ++ tailWord_1801604).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1801604).length < 2 ^ (prefixWord ++ tailWord_1801604).sum := by decide
  have hdescent : baseEnd_1801604 < baseStart_1801604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1801604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1801607 : List Nat := [1, 1, 4, 2, 2, 2, 4, 1, 4]
def baseStart_1801607 : Nat := 118140960795 + 1801607 * 2 ^ 59
def prefixEnd_1801607 : Nat := 4983230072969 + 3 ^ 40 * 1801607 * 2
def baseEnd_1801607 : Nat := 411151262891039083567585

theorem tailTrace_1801607 : CollatzResearch.WordTrace tailWord_1801607 prefixEnd_1801607 411151262891039083567585 := by
  unfold tailWord_1801607
  simp only [CollatzResearch.WordTrace]
  refine ⟨65710005584093003824259075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43806670389395335882839383 65710005584093003824259075)
  ·
    refine ⟨98565008376139505736388613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65710005584093003824259075 98565008376139505736388613)
    ·
      refine ⟨18480939070526157325572865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98565008376139505736388613 18480939070526157325572865)
      ·
        refine ⟨13860704302894617994179649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18480939070526157325572865 13860704302894617994179649)
        ·
          refine ⟨10395528227170963495634737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13860704302894617994179649 10395528227170963495634737)
          ·
            refine ⟨7796646170378222621726053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10395528227170963495634737 7796646170378222621726053)
            ·
              refine ⟨1461871156945916741573635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7796646170378222621726053 1461871156945916741573635)
              ·
                refine ⟨2192806735418875112360453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1461871156945916741573635 2192806735418875112360453)
                ·
                  refine ⟨411151262891039083567585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2192806735418875112360453 411151262891039083567585)
                  ·
                    rfl

theorem cell21_1801607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 4, 1, 4].length) (baseStart_1801607 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1801607 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1801607 prefixEnd_1801607 := by exact prefixLift 1801607
  have htrace : WordTrace (prefixWord ++ tailWord_1801607) baseStart_1801607 baseEnd_1801607 := by
    simpa [prefixWord, tailWord_1801607, baseEnd_1801607] using wordTrace_append hprefix tailTrace_1801607
  have hstable : (prefixWord ++ tailWord_1801607).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1801607).length < 2 ^ (prefixWord ++ tailWord_1801607).sum := by decide
  have hdescent : baseEnd_1801607 < baseStart_1801607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1801607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1801686 : List Nat := [5, 2, 1, 1, 1, 3, 2, 3, 3]
def baseStart_1801686 : Nat := 118140960795 + 1801686 * 2 ^ 59
def prefixEnd_1801686 : Nat := 4983230072969 + 3 ^ 40 * 1801686 * 2
def baseEnd_1801686 : Nat := 411169291767352501750757

theorem tailTrace_1801686 : CollatzResearch.WordTrace tailWord_1801686 prefixEnd_1801686 411169291767352501750757 := by
  unfold tailWord_1801686
  simp only [CollatzResearch.WordTrace]
  refine ⟨4107055434425425019774057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43808591300537866877589941 4107055434425425019774057)
  ·
    refine ⟨3080291575819068764830543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4107055434425425019774057 3080291575819068764830543)
    ·
      refine ⟨4620437363728603147245815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3080291575819068764830543 4620437363728603147245815)
      ·
        refine ⟨6930656045592904720868723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4620437363728603147245815 6930656045592904720868723)
        ·
          refine ⟨10395984068389357081303085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6930656045592904720868723 10395984068389357081303085)
          ·
            refine ⟨3898494025646008905488657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10395984068389357081303085 3898494025646008905488657)
            ·
              refine ⟨2923870519234506679116493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3898494025646008905488657 2923870519234506679116493)
              ·
                refine ⟨1096451444712940004668685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2923870519234506679116493 1096451444712940004668685)
                ·
                  refine ⟨411169291767352501750757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1096451444712940004668685 411169291767352501750757)
                  ·
                    rfl

theorem cell21_1801686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 3, 3].length) (baseStart_1801686 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1801686 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1801686 prefixEnd_1801686 := by exact prefixLift 1801686
  have htrace : WordTrace (prefixWord ++ tailWord_1801686) baseStart_1801686 baseEnd_1801686 := by
    simpa [prefixWord, tailWord_1801686, baseEnd_1801686] using wordTrace_append hprefix tailTrace_1801686
  have hstable : (prefixWord ++ tailWord_1801686).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1801686).length < 2 ^ (prefixWord ++ tailWord_1801686).sum := by decide
  have hdescent : baseEnd_1801686 < baseStart_1801686 := by decide
  rcases family_descends (prefixWord ++ tailWord_1801686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1801815 : List Nat := [1, 1, 3, 2, 2, 12]
def baseStart_1801815 : Nat := 118140960795 + 1801815 * 2 ^ 59
def prefixEnd_1801815 : Nat := 4983230072969 + 3 ^ 40 * 1801815 * 2
def baseEnd_1801815 : Nat := 15229582641662109040759

theorem tailTrace_1801815 : CollatzResearch.WordTrace tailWord_1801815 prefixEnd_1801815 15229582641662109040759 := by
  unfold tailWord_1801815
  simp only [CollatzResearch.WordTrace]
  refine ⟨65717591967339455347830899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43811727978226303565220599 65717591967339455347830899)
  ·
    refine ⟨98576387951009183021746349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65717591967339455347830899 98576387951009183021746349)
    ·
      refine ⟨36966145481628443633154881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98576387951009183021746349 36966145481628443633154881)
      ·
        refine ⟨27724609111221332724866161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36966145481628443633154881 27724609111221332724866161)
        ·
          refine ⟨20793456833415999543649621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27724609111221332724866161 20793456833415999543649621)
          ·
            refine ⟨15229582641662109040759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 20793456833415999543649621 15229582641662109040759)
            ·
              rfl

theorem cell21_1801815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 12].length) (baseStart_1801815 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1801815 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1801815 prefixEnd_1801815 := by exact prefixLift 1801815
  have htrace : WordTrace (prefixWord ++ tailWord_1801815) baseStart_1801815 baseEnd_1801815 := by
    simpa [prefixWord, tailWord_1801815, baseEnd_1801815] using wordTrace_append hprefix tailTrace_1801815
  have hstable : (prefixWord ++ tailWord_1801815).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1801815).length < 2 ^ (prefixWord ++ tailWord_1801815).sum := by decide
  have hdescent : baseEnd_1801815 < baseStart_1801815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1801815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1801880 : List Nat := [2, 1, 2, 4, 1, 2, 2, 4, 3]
def baseStart_1801880 : Nat := 118140960795 + 1801880 * 2 ^ 59
def prefixEnd_1801880 : Nat := 4983230072969 + 3 ^ 40 * 1801880 * 2
def baseEnd_1801880 : Nat := 411213565210451275517027

theorem tailTrace_1801880 : CollatzResearch.WordTrace tailWord_1801880 prefixEnd_1801880 411213565210451275517027 := by
  unfold tailWord_1801880
  simp only [CollatzResearch.WordTrace]
  refine ⟨32859981356051985724473547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43813308474735980965964729 32859981356051985724473547)
  ·
    refine ⟨49289972034077978586710321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32859981356051985724473547 49289972034077978586710321)
    ·
      refine ⟨36967479025558483940032741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49289972034077978586710321 36967479025558483940032741)
      ·
        refine ⟨6931402317292215738756139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36967479025558483940032741 6931402317292215738756139)
        ·
          refine ⟨10397103475938323608134209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6931402317292215738756139 10397103475938323608134209)
          ·
            refine ⟨7797827606953742706100657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10397103475938323608134209 7797827606953742706100657)
            ·
              refine ⟨5848370705215307029575493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7797827606953742706100657 5848370705215307029575493)
              ·
                refine ⟨1096569507227870068045405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5848370705215307029575493 1096569507227870068045405)
                ·
                  refine ⟨411213565210451275517027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1096569507227870068045405 411213565210451275517027)
                  ·
                    rfl

theorem cell21_1801880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 4, 3].length) (baseStart_1801880 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1801880 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1801880 prefixEnd_1801880 := by exact prefixLift 1801880
  have htrace : WordTrace (prefixWord ++ tailWord_1801880) baseStart_1801880 baseEnd_1801880 := by
    simpa [prefixWord, tailWord_1801880, baseEnd_1801880] using wordTrace_append hprefix tailTrace_1801880
  have hstable : (prefixWord ++ tailWord_1801880).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1801880).length < 2 ^ (prefixWord ++ tailWord_1801880).sum := by decide
  have hdescent : baseEnd_1801880 < baseStart_1801880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1801880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1801891 : List Nat := [1, 1, 1, 4, 1, 1, 4, 8]
def baseStart_1801891 : Nat := 118140960795 + 1801891 * 2 ^ 59
def prefixEnd_1801891 : Nat := 4983230072969 + 3 ^ 40 * 1801891 * 2
def baseEnd_1801891 : Nat := 137072025186772566944557

theorem tailTrace_1801891 : CollatzResearch.WordTrace tailWord_1801891 prefixEnd_1801891 137072025186772566944557 := by
  unfold tailWord_1801891
  simp only [CollatzResearch.WordTrace]
  refine ⟨65720363915064120327597527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43813575943376080218398351 65720363915064120327597527)
  ·
    refine ⟨98580545872596180491396291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65720363915064120327597527 98580545872596180491396291)
    ·
      refine ⟨147870818808894270737094437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98580545872596180491396291 147870818808894270737094437)
      ·
        refine ⟨27725778526667675763205207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 147870818808894270737094437 27725778526667675763205207)
        ·
          refine ⟨41588667790001513644807811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27725778526667675763205207 41588667790001513644807811)
          ·
            refine ⟨62383001685002270467211717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41588667790001513644807811 62383001685002270467211717)
            ·
              refine ⟨11696812815937925712602197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62383001685002270467211717 11696812815937925712602197)
              ·
                refine ⟨137072025186772566944557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11696812815937925712602197 137072025186772566944557)
                ·
                  rfl

theorem cell21_1801891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 8].length) (baseStart_1801891 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1801891 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1801891 prefixEnd_1801891 := by exact prefixLift 1801891
  have htrace : WordTrace (prefixWord ++ tailWord_1801891) baseStart_1801891 baseEnd_1801891 := by
    simpa [prefixWord, tailWord_1801891, baseEnd_1801891] using wordTrace_append hprefix tailTrace_1801891
  have hstable : (prefixWord ++ tailWord_1801891).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1801891).length < 2 ^ (prefixWord ++ tailWord_1801891).sum := by decide
  have hdescent : baseEnd_1801891 < baseStart_1801891 := by decide
  rcases family_descends (prefixWord ++ tailWord_1801891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1801967 : List Nat := [1, 1, 2, 1, 5, 1, 1, 9]
def baseStart_1801967 : Nat := 118140960795 + 1801967 * 2 ^ 59
def prefixEnd_1801967 : Nat := 4983230072969 + 3 ^ 40 * 1801967 * 2
def baseEnd_1801967 : Nat := 137077806598586152522283

theorem tailTrace_1801967 : CollatzResearch.WordTrace tailWord_1801967 prefixEnd_1801967 137077806598586152522283 := by
  unfold tailWord_1801967
  simp only [CollatzResearch.WordTrace]
  refine ⟨65723135862788785307364155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43815423908525856871576103 65723135862788785307364155)
  ·
    refine ⟨98584703794183177961046233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65723135862788785307364155 98584703794183177961046233)
    ·
      refine ⟨73938527845637383470784675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98584703794183177961046233 73938527845637383470784675)
      ·
        refine ⟨110907791768456075206177013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73938527845637383470784675 110907791768456075206177013)
        ·
          refine ⟨10397605478292757050579095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 110907791768456075206177013 10397605478292757050579095)
          ·
            refine ⟨15596408217439135575868643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10397605478292757050579095 15596408217439135575868643)
            ·
              refine ⟨23394612326158703363802965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15596408217439135575868643 23394612326158703363802965)
              ·
                refine ⟨137077806598586152522283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23394612326158703363802965 137077806598586152522283)
                ·
                  rfl

theorem cell21_1801967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 9].length) (baseStart_1801967 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1801967 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1801967 prefixEnd_1801967 := by exact prefixLift 1801967
  have htrace : WordTrace (prefixWord ++ tailWord_1801967) baseStart_1801967 baseEnd_1801967 := by
    simpa [prefixWord, tailWord_1801967, baseEnd_1801967] using wordTrace_append hprefix tailTrace_1801967
  have hstable : (prefixWord ++ tailWord_1801967).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1801967).length < 2 ^ (prefixWord ++ tailWord_1801967).sum := by decide
  have hdescent : baseEnd_1801967 < baseStart_1801967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1801967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1802046 : List Nat := [4, 2, 1, 2, 2, 2, 1, 1, 6]
def baseStart_1802046 : Nat := 118140960795 + 1802046 * 2 ^ 59
def prefixEnd_1802046 : Nat := 4983230072969 + 3 ^ 40 * 1802046 * 2
def baseEnd_1802046 : Nat := 411251448672071875750021

theorem tailTrace_1802046 : CollatzResearch.WordTrace tailWord_1802046 prefixEnd_1802046 411251448672071875750021 := by
  unfold tailWord_1802046
  simp only [CollatzResearch.WordTrace]
  refine ⟨8215752153687822724936249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43817344819668387866326661 8215752153687822724936249)
  ·
    refine ⟨6161814115265867043702187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8215752153687822724936249 6161814115265867043702187)
    ·
      refine ⟨9242721172898800565553281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6161814115265867043702187 9242721172898800565553281)
      ·
        refine ⟨6932040879674100424164961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9242721172898800565553281 6932040879674100424164961)
        ·
          refine ⟨5199030659755575318123721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6932040879674100424164961 5199030659755575318123721)
          ·
            refine ⟨3899272994816681488592791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5199030659755575318123721 3899272994816681488592791)
            ·
              refine ⟨5848909492225022232889187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3899272994816681488592791 5848909492225022232889187)
              ·
                refine ⟨8773364238337533349333781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5848909492225022232889187 8773364238337533349333781)
                ·
                  refine ⟨411251448672071875750021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8773364238337533349333781 411251448672071875750021)
                  ·
                    rfl

theorem cell21_1802046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 1, 6].length) (baseStart_1802046 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1802046 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1802046 prefixEnd_1802046 := by exact prefixLift 1802046
  have htrace : WordTrace (prefixWord ++ tailWord_1802046) baseStart_1802046 baseEnd_1802046 := by
    simpa [prefixWord, tailWord_1802046, baseEnd_1802046] using wordTrace_append hprefix tailTrace_1802046
  have hstable : (prefixWord ++ tailWord_1802046).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1802046).length < 2 ^ (prefixWord ++ tailWord_1802046).sum := by decide
  have hdescent : baseEnd_1802046 < baseStart_1802046 := by decide
  rcases family_descends (prefixWord ++ tailWord_1802046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1802074 : List Nat := [3, 1, 1, 2, 1, 3, 1, 4, 5]
def baseStart_1802074 : Nat := 118140960795 + 1802074 * 2 ^ 59
def prefixEnd_1802074 : Nat := 4983230072969 + 3 ^ 40 * 1802074 * 2
def baseEnd_1802074 : Nat := 411257838653550049283297

theorem tailTrace_1802074 : CollatzResearch.WordTrace tailWord_1802074 prefixEnd_1802074 411257838653550049283297 := by
  unfold tailWord_1802074
  simp only [CollatzResearch.WordTrace]
  refine ⟨16431759618350285645377319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43818025648934095054339517 16431759618350285645377319)
  ·
    refine ⟨24647639427525428468065979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16431759618350285645377319 24647639427525428468065979)
    ·
      refine ⟨36971459141288142702098969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24647639427525428468065979 36971459141288142702098969)
      ·
        refine ⟨27728594355966107026574227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36971459141288142702098969 27728594355966107026574227)
        ·
          refine ⟨41592891533949160539861341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27728594355966107026574227 41592891533949160539861341)
          ·
            refine ⟨15597334325230935202448003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41592891533949160539861341 15597334325230935202448003)
            ·
              refine ⟨23396001487846402803672005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15597334325230935202448003 23396001487846402803672005)
              ·
                refine ⟨4386750278971200525688501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23396001487846402803672005 4386750278971200525688501)
                ·
                  refine ⟨411257838653550049283297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4386750278971200525688501 411257838653550049283297)
                  ·
                    rfl

theorem cell21_1802074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 4, 5].length) (baseStart_1802074 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1802074 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1802074 prefixEnd_1802074 := by exact prefixLift 1802074
  have htrace : WordTrace (prefixWord ++ tailWord_1802074) baseStart_1802074 baseEnd_1802074 := by
    simpa [prefixWord, tailWord_1802074, baseEnd_1802074] using wordTrace_append hprefix tailTrace_1802074
  have hstable : (prefixWord ++ tailWord_1802074).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1802074).length < 2 ^ (prefixWord ++ tailWord_1802074).sum := by decide
  have hdescent : baseEnd_1802074 < baseStart_1802074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1802074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1802105 : List Nat := [1, 2, 1, 3, 2, 2, 2, 4, 4]
def baseStart_1802105 : Nat := 118140960795 + 1802105 * 2 ^ 59
def prefixEnd_1802105 : Nat := 4983230072969 + 3 ^ 40 * 1802105 * 2
def baseEnd_1802105 : Nat := 411264913275900884266567

theorem tailTrace_1802105 : CollatzResearch.WordTrace tailWord_1802105 prefixEnd_1802105 411264913275900884266567 := by
  unfold tailWord_1802105
  simp only [CollatzResearch.WordTrace]
  refine ⟨65728169136288834875887769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43818779424192556583925179 65728169136288834875887769)
  ·
    refine ⟨49296126852216626156915827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65728169136288834875887769 49296126852216626156915827)
    ·
      refine ⟨73944190278324939235373741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49296126852216626156915827 73944190278324939235373741)
      ·
        refine ⟨27729071354371852213265153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73944190278324939235373741 27729071354371852213265153)
        ·
          refine ⟨20796803515778889159948865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27729071354371852213265153 20796803515778889159948865)
          ·
            refine ⟨15597602636834166869961649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20796803515778889159948865 15597602636834166869961649)
            ·
              refine ⟨11698201977625625152471237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15597602636834166869961649 11698201977625625152471237)
              ·
                refine ⟨2193412870804804716088357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11698201977625625152471237 2193412870804804716088357)
                ·
                  refine ⟨411264913275900884266567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2193412870804804716088357 411264913275900884266567)
                  ·
                    rfl

theorem cell21_1802105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 4, 4].length) (baseStart_1802105 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1802105 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1802105 prefixEnd_1802105 := by exact prefixLift 1802105
  have htrace : WordTrace (prefixWord ++ tailWord_1802105) baseStart_1802105 baseEnd_1802105 := by
    simpa [prefixWord, tailWord_1802105, baseEnd_1802105] using wordTrace_append hprefix tailTrace_1802105
  have hstable : (prefixWord ++ tailWord_1802105).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1802105).length < 2 ^ (prefixWord ++ tailWord_1802105).sum := by decide
  have hdescent : baseEnd_1802105 < baseStart_1802105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1802105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1802215 : List Nat := [1, 1, 5, 2, 3, 2, 1, 2, 4]
def baseStart_1802215 : Nat := 118140960795 + 1802215 * 2 ^ 59
def prefixEnd_1802215 : Nat := 4983230072969 + 3 ^ 40 * 1802215 * 2
def baseEnd_1802215 : Nat := 411290016774565137433009

theorem tailTrace_1802215 : CollatzResearch.WordTrace tailWord_1802215 prefixEnd_1802215 411290016774565137433009 := by
  unfold tailWord_1802215
  simp only [CollatzResearch.WordTrace]
  refine ⟨65732181165890323662392099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43821454110593549108261399 65732181165890323662392099)
  ·
    refine ⟨98598271748835485493588149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65732181165890323662392099 98598271748835485493588149)
    ·
      refine ⟨9243587976453326765023889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 98598271748835485493588149 9243587976453326765023889)
      ·
        refine ⟨6932690982339995073767917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9243587976453326765023889 6932690982339995073767917)
        ·
          refine ⟨2599759118377498152662969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6932690982339995073767917 2599759118377498152662969)
          ·
            refine ⟨1949819338783123614497227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2599759118377498152662969 1949819338783123614497227)
            ·
              refine ⟨2924729008174685421745841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1949819338783123614497227 2924729008174685421745841)
              ·
                refine ⟨2193546756131014066309381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2924729008174685421745841 2193546756131014066309381)
                ·
                  refine ⟨411290016774565137433009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2193546756131014066309381 411290016774565137433009)
                  ·
                    rfl

theorem cell21_1802215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 2, 4].length) (baseStart_1802215 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1802215 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1802215 prefixEnd_1802215 := by exact prefixLift 1802215
  have htrace : WordTrace (prefixWord ++ tailWord_1802215) baseStart_1802215 baseEnd_1802215 := by
    simpa [prefixWord, tailWord_1802215, baseEnd_1802215] using wordTrace_append hprefix tailTrace_1802215
  have hstable : (prefixWord ++ tailWord_1802215).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1802215).length < 2 ^ (prefixWord ++ tailWord_1802215).sum := by decide
  have hdescent : baseEnd_1802215 < baseStart_1802215 := by decide
  rcases family_descends (prefixWord ++ tailWord_1802215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1802316 : List Nat := [2, 2, 1, 3, 1, 1, 2, 1, 8]
def baseStart_1802316 : Nat := 118140960795 + 1802316 * 2 ^ 59
def prefixEnd_1802316 : Nat := 4983230072969 + 3 ^ 40 * 1802316 * 2
def baseEnd_1802316 : Nat := 411313066350611406249469

theorem tailTrace_1802316 : CollatzResearch.WordTrace tailWord_1802316 prefixEnd_1802316 411313066350611406249469 := by
  unfold tailWord_1802316
  simp only [CollatzResearch.WordTrace]
  refine ⟨32867932469262208955909401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43823909959016278607879201 32867932469262208955909401)
  ·
    refine ⟨24650949351946656716932051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32867932469262208955909401 24650949351946656716932051)
    ·
      refine ⟨36976424027919985075398077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24650949351946656716932051 36976424027919985075398077)
      ·
        refine ⟨13866159010469994403274279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36976424027919985075398077 13866159010469994403274279)
        ·
          refine ⟨20799238515704991604911419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13866159010469994403274279 20799238515704991604911419)
          ·
            refine ⟨31198857773557487407367129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20799238515704991604911419 31198857773557487407367129)
            ·
              refine ⟨23399143330168115555525347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31198857773557487407367129 23399143330168115555525347)
              ·
                refine ⟨35098714995252173333288021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23399143330168115555525347 35098714995252173333288021)
                ·
                  refine ⟨411313066350611406249469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35098714995252173333288021 411313066350611406249469)
                  ·
                    rfl

theorem cell21_1802316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 8].length) (baseStart_1802316 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1802316 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1802316 prefixEnd_1802316 := by exact prefixLift 1802316
  have htrace : WordTrace (prefixWord ++ tailWord_1802316) baseStart_1802316 baseEnd_1802316 := by
    simpa [prefixWord, tailWord_1802316, baseEnd_1802316] using wordTrace_append hprefix tailTrace_1802316
  have hstable : (prefixWord ++ tailWord_1802316).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1802316).length < 2 ^ (prefixWord ++ tailWord_1802316).sum := by decide
  have hdescent : baseEnd_1802316 < baseStart_1802316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1802316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1802336 : List Nat := [2, 1, 1, 3, 2, 3, 4, 2, 3]
def baseStart_1802336 : Nat := 118140960795 + 1802336 * 2 ^ 59
def prefixEnd_1802336 : Nat := 4983230072969 + 3 ^ 40 * 1802336 * 2
def baseEnd_1802336 : Nat := 411317630623095815916095

theorem tailTrace_1802336 : CollatzResearch.WordTrace tailWord_1802336 prefixEnd_1802336 411317630623095815916095 := by
  unfold tailWord_1802336
  simp only [CollatzResearch.WordTrace]
  refine ⟨32868297199225980663773431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43824396265634640885031241 32868297199225980663773431)
  ·
    refine ⟨49302445798838970995660147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32868297199225980663773431 49302445798838970995660147)
    ·
      refine ⟨73953668698258456493490221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49302445798838970995660147 73953668698258456493490221)
      ·
        refine ⟨27732625761846921185058833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73953668698258456493490221 27732625761846921185058833)
        ·
          refine ⟨20799469321385190888794125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27732625761846921185058833 20799469321385190888794125)
          ·
            refine ⟨7799800995519446583297797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20799469321385190888794125 7799800995519446583297797)
            ·
              refine ⟨1462462686659896234368337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7799800995519446583297797 1462462686659896234368337)
              ·
                refine ⟨1096847014994922175776253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1462462686659896234368337 1096847014994922175776253)
                ·
                  refine ⟨411317630623095815916095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1096847014994922175776253 411317630623095815916095)
                  ·
                    rfl

theorem cell21_1802336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 4, 2, 3].length) (baseStart_1802336 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1802336 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1802336 prefixEnd_1802336 := by exact prefixLift 1802336
  have htrace : WordTrace (prefixWord ++ tailWord_1802336) baseStart_1802336 baseEnd_1802336 := by
    simpa [prefixWord, tailWord_1802336, baseEnd_1802336] using wordTrace_append hprefix tailTrace_1802336
  have hstable : (prefixWord ++ tailWord_1802336).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1802336).length < 2 ^ (prefixWord ++ tailWord_1802336).sum := by decide
  have hdescent : baseEnd_1802336 < baseStart_1802336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1802336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1802364 : List Nat := [2, 2, 2, 1, 1, 5, 3, 5]
def baseStart_1802364 : Nat := 118140960795 + 1802364 * 2 ^ 59
def prefixEnd_1802364 : Nat := 4983230072969 + 3 ^ 40 * 1802364 * 2
def baseEnd_1802364 : Nat := 137108006868191329816457

theorem tailTrace_1802364 : CollatzResearch.WordTrace tailWord_1802364 prefixEnd_1802364 137108006868191329816457 := by
  unfold tailWord_1802364
  simp only [CollatzResearch.WordTrace]
  refine ⟨32868807821175261054783073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43825077094900348073044097 32868807821175261054783073)
  ·
    refine ⟨24651605865881445791087305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32868807821175261054783073 24651605865881445791087305)
    ·
      refine ⟨18488704399411084343315479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24651605865881445791087305 18488704399411084343315479)
      ·
        refine ⟨27733056599116626514973219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18488704399411084343315479 27733056599116626514973219)
        ·
          refine ⟨41599584898674939772459829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27733056599116626514973219 41599584898674939772459829)
          ·
            refine ⟨3899961084250775603668109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41599584898674939772459829 3899961084250775603668109)
            ·
              refine ⟨1462485406594040851375541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3899961084250775603668109 1462485406594040851375541)
              ·
                refine ⟨137108006868191329816457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1462485406594040851375541 137108006868191329816457)
                ·
                  rfl

theorem cell21_1802364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 3, 5].length) (baseStart_1802364 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1802364 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1802364 prefixEnd_1802364 := by exact prefixLift 1802364
  have htrace : WordTrace (prefixWord ++ tailWord_1802364) baseStart_1802364 baseEnd_1802364 := by
    simpa [prefixWord, tailWord_1802364, baseEnd_1802364] using wordTrace_append hprefix tailTrace_1802364
  have hstable : (prefixWord ++ tailWord_1802364).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1802364).length < 2 ^ (prefixWord ++ tailWord_1802364).sum := by decide
  have hdescent : baseEnd_1802364 < baseStart_1802364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1802364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1802423 : List Nat := [1, 1, 3, 1, 4, 3, 1, 7]
def baseStart_1802423 : Nat := 118140960795 + 1802423 * 2 ^ 59
def prefixEnd_1802423 : Nat := 4983230072969 + 3 ^ 40 * 1802423 * 2
def baseEnd_1802423 : Nat := 137112495069467665988639

theorem tailTrace_1802423 : CollatzResearch.WordTrace tailWord_1802423 prefixEnd_1802423 137112495069467665988639 := by
  unfold tailWord_1802423
  simp only [CollatzResearch.WordTrace]
  refine ⟨65739767549136775185963923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43826511699424516790642615 65739767549136775185963923)
  ·
    refine ⟨98609651323705162778945885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65739767549136775185963923 98609651323705162778945885)
    ·
      refine ⟨36978619246389436042104707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98609651323705162778945885 36978619246389436042104707)
      ·
        refine ⟨55467928869584154063157061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36978619246389436042104707 55467928869584154063157061)
        ·
          refine ⟨10400236663047028886841949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55467928869584154063157061 10400236663047028886841949)
          ·
            refine ⟨3900088748642635832565731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10400236663047028886841949 3900088748642635832565731)
            ·
              refine ⟨5850133122963953748848597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3900088748642635832565731 5850133122963953748848597)
              ·
                refine ⟨137112495069467665988639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5850133122963953748848597 137112495069467665988639)
                ·
                  rfl

theorem cell21_1802423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 7].length) (baseStart_1802423 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1802423 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1802423 prefixEnd_1802423 := by exact prefixLift 1802423
  have htrace : WordTrace (prefixWord ++ tailWord_1802423) baseStart_1802423 baseEnd_1802423 := by
    simpa [prefixWord, tailWord_1802423, baseEnd_1802423] using wordTrace_append hprefix tailTrace_1802423
  have hstable : (prefixWord ++ tailWord_1802423).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1802423).length < 2 ^ (prefixWord ++ tailWord_1802423).sum := by decide
  have hdescent : baseEnd_1802423 < baseStart_1802423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1802423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1802437 : List Nat := [1, 3, 1, 1, 1, 1, 4, 2, 7]
def baseStart_1802437 : Nat := 118140960795 + 1802437 * 2 ^ 59
def prefixEnd_1802437 : Nat := 4983230072969 + 3 ^ 40 * 1802437 * 2
def baseEnd_1802437 : Nat := 411340680199142084732555

theorem tailTrace_1802437 : CollatzResearch.WordTrace tailWord_1802437 prefixEnd_1802437 411340680199142084732555 := by
  unfold tailWord_1802437
  simp only [CollatzResearch.WordTrace]
  refine ⟨65740278171086055576973565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43826852114057370384649043 65740278171086055576973565)
  ·
    refine ⟨24652604314157270841365087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65740278171086055576973565 24652604314157270841365087)
    ·
      refine ⟨36978906471235906262047631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24652604314157270841365087 36978906471235906262047631)
      ·
        refine ⟨55468359706853859393071447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36978906471235906262047631 55468359706853859393071447)
        ·
          refine ⟨83202539560280789089607171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55468359706853859393071447 83202539560280789089607171)
          ·
            refine ⟨124803809340421183634410757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83202539560280789089607171 124803809340421183634410757)
            ·
              refine ⟨23400714251328971931452017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 124803809340421183634410757 23400714251328971931452017)
              ·
                refine ⟨17550535688496728948589013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23400714251328971931452017 17550535688496728948589013)
                ·
                  refine ⟨411340680199142084732555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17550535688496728948589013 411340680199142084732555)
                  ·
                    rfl

theorem cell21_1802437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 2, 7].length) (baseStart_1802437 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1802437 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1802437 prefixEnd_1802437 := by exact prefixLift 1802437
  have htrace : WordTrace (prefixWord ++ tailWord_1802437) baseStart_1802437 baseEnd_1802437 := by
    simpa [prefixWord, tailWord_1802437, baseEnd_1802437] using wordTrace_append hprefix tailTrace_1802437
  have hstable : (prefixWord ++ tailWord_1802437).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1802437).length < 2 ^ (prefixWord ++ tailWord_1802437).sum := by decide
  have hdescent : baseEnd_1802437 < baseStart_1802437 := by decide
  rcases family_descends (prefixWord ++ tailWord_1802437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1802530 : List Nat := [3, 3, 1, 1, 3, 1, 1, 1, 7]
def baseStart_1802530 : Nat := 118140960795 + 1802530 * 2 ^ 59
def prefixEnd_1802530 : Nat := 4983230072969 + 3 ^ 40 * 1802530 * 2
def baseEnd_1802530 : Nat := 411361904066194589682365

theorem tailTrace_1802530 : CollatzResearch.WordTrace tailWord_1802530 prefixEnd_1802530 411361904066194589682365 := by
  unfold tailWord_1802530
  simp only [CollatzResearch.WordTrace]
  refine ⟨16435917539937283115027261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43829113439832754973406029 16435917539937283115027261)
  ·
    refine ⟨6163469077476481168135223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16435917539937283115027261 6163469077476481168135223)
    ·
      refine ⟨9245203616214721752202835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6163469077476481168135223 9245203616214721752202835)
      ·
        refine ⟨13867805424322082628304253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9245203616214721752202835 13867805424322082628304253)
        ·
          refine ⟨5200427034120780985614095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13867805424322082628304253 5200427034120780985614095)
          ·
            refine ⟨7800640551181171478421143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5200427034120780985614095 7800640551181171478421143)
            ·
              refine ⟨11700960826771757217631715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7800640551181171478421143 11700960826771757217631715)
              ·
                refine ⟨17551441240157635826447573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11700960826771757217631715 17551441240157635826447573)
                ·
                  refine ⟨411361904066194589682365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17551441240157635826447573 411361904066194589682365)
                  ·
                    rfl

theorem cell21_1802530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_1802530 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1802530 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1802530 prefixEnd_1802530 := by exact prefixLift 1802530
  have htrace : WordTrace (prefixWord ++ tailWord_1802530) baseStart_1802530 baseEnd_1802530 := by
    simpa [prefixWord, tailWord_1802530, baseEnd_1802530] using wordTrace_append hprefix tailTrace_1802530
  have hstable : (prefixWord ++ tailWord_1802530).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1802530).length < 2 ^ (prefixWord ++ tailWord_1802530).sum := by decide
  have hdescent : baseEnd_1802530 < baseStart_1802530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1802530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1802547 : List Nat := [1, 1, 1, 2, 5, 1, 4, 3, 3]
def baseStart_1802547 : Nat := 118140960795 + 1802547 * 2 ^ 59
def prefixEnd_1802547 : Nat := 4983230072969 + 3 ^ 40 * 1802547 * 2
def baseEnd_1802547 : Nat := 411365783697806337898997

theorem tailTrace_1802547 : CollatzResearch.WordTrace tailWord_1802547 prefixEnd_1802547 411365783697806337898997 := by
  unfold tailWord_1802547
  simp only [CollatzResearch.WordTrace]
  refine ⟨65744290200687544363477895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43829526800458362908985263 65744290200687544363477895)
  ·
    refine ⟨98616435301031316545216843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65744290200687544363477895 98616435301031316545216843)
    ·
      refine ⟨147924652951546974817825265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98616435301031316545216843 147924652951546974817825265)
      ·
        refine ⟨110943489713660231113368949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147924652951546974817825265 110943489713660231113368949)
        ·
          refine ⟨10400952160655646666878339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 110943489713660231113368949 10400952160655646666878339)
          ·
            refine ⟨15601428240983470000317509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10400952160655646666878339 15601428240983470000317509)
            ·
              refine ⟨2925267795184400625059533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15601428240983470000317509 2925267795184400625059533)
              ·
                refine ⟨1096975423194150234397325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2925267795184400625059533 1096975423194150234397325)
                ·
                  refine ⟨411365783697806337898997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1096975423194150234397325 411365783697806337898997)
                  ·
                    rfl

theorem cell21_1802547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 3, 3].length) (baseStart_1802547 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1802547 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1802547 prefixEnd_1802547 := by exact prefixLift 1802547
  have htrace : WordTrace (prefixWord ++ tailWord_1802547) baseStart_1802547 baseEnd_1802547 := by
    simpa [prefixWord, tailWord_1802547, baseEnd_1802547] using wordTrace_append hprefix tailTrace_1802547
  have hstable : (prefixWord ++ tailWord_1802547).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1802547).length < 2 ^ (prefixWord ++ tailWord_1802547).sum := by decide
  have hdescent : baseEnd_1802547 < baseStart_1802547 := by decide
  rcases family_descends (prefixWord ++ tailWord_1802547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1802564 : List Nat := [2, 3, 4, 1, 2, 1, 2, 1, 5]
def baseStart_1802564 : Nat := 118140960795 + 1802564 * 2 ^ 59
def prefixEnd_1802564 : Nat := 4983230072969 + 3 ^ 40 * 1802564 * 2
def baseEnd_1802564 : Nat := 411369663329418086115629

theorem tailTrace_1802564 : CollatzResearch.WordTrace tailWord_1802564 prefixEnd_1802564 411369663329418086115629 := by
  unfold tailWord_1802564
  simp only [CollatzResearch.WordTrace]
  refine ⟨32872455120812978133423373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43829940161083970844564497 32872455120812978133423373)
  ·
    refine ⟨12327170670304866800033765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32872455120812978133423373 12327170670304866800033765)
    ·
      refine ⟨2311344500682162525006331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12327170670304866800033765 2311344500682162525006331)
      ·
        refine ⟨3467016751023243787509497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2311344500682162525006331 3467016751023243787509497)
        ·
          refine ⟨2600262563267432840632123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3467016751023243787509497 2600262563267432840632123)
          ·
            refine ⟨3900393844901149260948185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2600262563267432840632123 3900393844901149260948185)
            ·
              refine ⟨2925295383675861945711139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3900393844901149260948185 2925295383675861945711139)
              ·
                refine ⟨4387943075513792918566709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2925295383675861945711139 4387943075513792918566709)
                ·
                  refine ⟨411369663329418086115629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4387943075513792918566709 411369663329418086115629)
                  ·
                    rfl

theorem cell21_1802564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 1, 5].length) (baseStart_1802564 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1802564 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1802564 prefixEnd_1802564 := by exact prefixLift 1802564
  have htrace : WordTrace (prefixWord ++ tailWord_1802564) baseStart_1802564 baseEnd_1802564 := by
    simpa [prefixWord, tailWord_1802564, baseEnd_1802564] using wordTrace_append hprefix tailTrace_1802564
  have hstable : (prefixWord ++ tailWord_1802564).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1802564).length < 2 ^ (prefixWord ++ tailWord_1802564).sum := by decide
  have hdescent : baseEnd_1802564 < baseStart_1802564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1802564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1802730 : List Nat := [3, 1, 3, 1, 3, 3, 1, 2, 4]
def baseStart_1802730 : Nat := 118140960795 + 1802730 * 2 ^ 59
def prefixEnd_1802730 : Nat := 4983230072969 + 3 ^ 40 * 1802730 * 2
def baseEnd_1802730 : Nat := 411407546791038686348623

theorem tailTrace_1802730 : CollatzResearch.WordTrace tailWord_1802730 prefixEnd_1802730 411407546791038686348623 := by
  unfold tailWord_1802730
  simp only [CollatzResearch.WordTrace]
  refine ⟨16437741189756141654347411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43833976506016377744926429 16437741189756141654347411)
  ·
    refine ⟨24656611784634212481521117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16437741189756141654347411 24656611784634212481521117)
    ·
      refine ⟨9246229419237829680570419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24656611784634212481521117 9246229419237829680570419)
      ·
        refine ⟨13869344128856744520855629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9246229419237829680570419 13869344128856744520855629)
        ·
          refine ⟨5201004048321279195320861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13869344128856744520855629 5201004048321279195320861)
          ·
            refine ⟨1950376518120479698245323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5201004048321279195320861 1950376518120479698245323)
            ·
              refine ⟨2925564777180719547367985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1950376518120479698245323 2925564777180719547367985)
              ·
                refine ⟨2194173582885539660525989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2925564777180719547367985 2194173582885539660525989)
                ·
                  refine ⟨411407546791038686348623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2194173582885539660525989 411407546791038686348623)
                  ·
                    rfl

theorem cell21_1802730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 2, 4].length) (baseStart_1802730 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1802730 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1802730 prefixEnd_1802730 := by exact prefixLift 1802730
  have htrace : WordTrace (prefixWord ++ tailWord_1802730) baseStart_1802730 baseEnd_1802730 := by
    simpa [prefixWord, tailWord_1802730, baseEnd_1802730] using wordTrace_append hprefix tailTrace_1802730
  have hstable : (prefixWord ++ tailWord_1802730).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1802730).length < 2 ^ (prefixWord ++ tailWord_1802730).sum := by decide
  have hdescent : baseEnd_1802730 < baseStart_1802730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1802730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1802806 : List Nat := [5, 1, 2, 1, 2, 2, 1, 3, 4]
def baseStart_1802806 : Nat := 118140960795 + 1802806 * 2 ^ 59
def prefixEnd_1802806 : Nat := 4983230072969 + 3 ^ 40 * 1802806 * 2
def baseEnd_1802806 : Nat := 411424891026479443081801

theorem tailTrace_1802806 : CollatzResearch.WordTrace tailWord_1802806 prefixEnd_1802806 411424891026479443081801 := by
  unfold tailWord_1802806
  simp only [CollatzResearch.WordTrace]
  refine ⟨4109608544171826974822267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43835824471166154398104181 4109608544171826974822267)
  ·
    refine ⟨6164412816257740462233401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4109608544171826974822267 6164412816257740462233401)
    ·
      refine ⟨4623309612193305346675051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6164412816257740462233401 4623309612193305346675051)
      ·
        refine ⟨6934964418289958020012577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4623309612193305346675051 6934964418289958020012577)
        ·
          refine ⟨5201223313717468515009433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6934964418289958020012577 5201223313717468515009433)
          ·
            refine ⟨3900917485288101386257075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5201223313717468515009433 3900917485288101386257075)
            ·
              refine ⟨5851376227932152079385613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3900917485288101386257075 5851376227932152079385613)
              ·
                refine ⟨2194266085474557029769605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5851376227932152079385613 2194266085474557029769605)
                ·
                  refine ⟨411424891026479443081801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2194266085474557029769605 411424891026479443081801)
                  ·
                    rfl

theorem cell21_1802806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 3, 4].length) (baseStart_1802806 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1802806 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1802806 prefixEnd_1802806 := by exact prefixLift 1802806
  have htrace : WordTrace (prefixWord ++ tailWord_1802806) baseStart_1802806 baseEnd_1802806 := by
    simpa [prefixWord, tailWord_1802806, baseEnd_1802806] using wordTrace_append hprefix tailTrace_1802806
  have hstable : (prefixWord ++ tailWord_1802806).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1802806).length < 2 ^ (prefixWord ++ tailWord_1802806).sum := by decide
  have hdescent : baseEnd_1802806 < baseStart_1802806 := by decide
  rcases family_descends (prefixWord ++ tailWord_1802806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1802831 : List Nat := [1, 1, 2, 1, 1, 2, 4, 1, 8]
def baseStart_1802831 : Nat := 118140960795 + 1802831 * 2 ^ 59
def prefixEnd_1802831 : Nat := 4983230072969 + 3 ^ 40 * 1802831 * 2
def baseEnd_1802831 : Nat := 411430596367084955165083

theorem tailTrace_1802831 : CollatzResearch.WordTrace tailWord_1802831 prefixEnd_1802831 411430596367084955165083 := by
  unfold tailWord_1802831
  simp only [CollatzResearch.WordTrace]
  refine ⟨65754648531658660866816347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43836432354439107244544231 65754648531658660866816347)
  ·
    refine ⟨98631972797487991300224521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65754648531658660866816347 98631972797487991300224521)
    ·
      refine ⟨73973979598115993475168391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98631972797487991300224521 73973979598115993475168391)
      ·
        refine ⟨110960969397173990212752587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73973979598115993475168391 110960969397173990212752587)
        ·
          refine ⟨166441454095760985319128881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110960969397173990212752587 166441454095760985319128881)
          ·
            refine ⟨124831090571820738989346661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166441454095760985319128881 124831090571820738989346661)
            ·
              refine ⟨23405829482216388560502499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 124831090571820738989346661 23405829482216388560502499)
              ·
                refine ⟨35108744223324582840753749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23405829482216388560502499 35108744223324582840753749)
                ·
                  refine ⟨411430596367084955165083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35108744223324582840753749 411430596367084955165083)
                  ·
                    rfl

theorem cell21_1802831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 8].length) (baseStart_1802831 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1802831 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1802831 prefixEnd_1802831 := by exact prefixLift 1802831
  have htrace : WordTrace (prefixWord ++ tailWord_1802831) baseStart_1802831 baseEnd_1802831 := by
    simpa [prefixWord, tailWord_1802831, baseEnd_1802831] using wordTrace_append hprefix tailTrace_1802831
  have hstable : (prefixWord ++ tailWord_1802831).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1802831).length < 2 ^ (prefixWord ++ tailWord_1802831).sum := by decide
  have hdescent : baseEnd_1802831 < baseStart_1802831 := by decide
  rcases family_descends (prefixWord ++ tailWord_1802831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1802848 : List Nat := [2, 1, 1, 3, 2, 1, 3, 4, 4]
def baseStart_1802848 : Nat := 118140960795 + 1802848 * 2 ^ 59
def prefixEnd_1802848 : Nat := 4983230072969 + 3 ^ 40 * 1802848 * 2
def baseEnd_1802848 : Nat := 411434475998696703381715

theorem tailTrace_1802848 : CollatzResearch.WordTrace tailWord_1802848 prefixEnd_1802848 411434475998696703381715 := by
  unfold tailWord_1802848
  simp only [CollatzResearch.WordTrace]
  refine ⟨32877634286298536385092599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43836845715064715180123465 32877634286298536385092599)
  ·
    refine ⟨49316451429447804577638899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32877634286298536385092599 49316451429447804577638899)
    ·
      refine ⟨73974677144171706866458349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49316451429447804577638899 73974677144171706866458349)
      ·
        refine ⟨27740503929064390074921881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73974677144171706866458349 27740503929064390074921881)
        ·
          refine ⟨20805377946798292556191411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27740503929064390074921881 20805377946798292556191411)
          ·
            refine ⟨31208066920197438834287117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20805377946798292556191411 31208066920197438834287117)
            ·
              refine ⟨11703025095074039562857669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31208066920197438834287117 11703025095074039562857669)
              ·
                refine ⟨2194317205326382418035813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11703025095074039562857669 2194317205326382418035813)
                ·
                  refine ⟨411434475998696703381715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2194317205326382418035813 411434475998696703381715)
                  ·
                    rfl

theorem cell21_1802848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 4, 4].length) (baseStart_1802848 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1802848 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1802848 prefixEnd_1802848 := by exact prefixLift 1802848
  have htrace : WordTrace (prefixWord ++ tailWord_1802848) baseStart_1802848 baseEnd_1802848 := by
    simpa [prefixWord, tailWord_1802848, baseEnd_1802848] using wordTrace_append hprefix tailTrace_1802848
  have hstable : (prefixWord ++ tailWord_1802848).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1802848).length < 2 ^ (prefixWord ++ tailWord_1802848).sum := by decide
  have hdescent : baseEnd_1802848 < baseStart_1802848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1802848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1802938 : List Nat := [3, 1, 1, 1, 2, 3, 3, 7]
def baseStart_1802938 : Nat := 118140960795 + 1802938 * 2 ^ 59
def prefixEnd_1802938 : Nat := 4983230072969 + 3 ^ 40 * 1802938 * 2
def baseEnd_1802938 : Nat := 137151671741625515627177

theorem tailTrace_1802938 : CollatzResearch.WordTrace tailWord_1802938 prefixEnd_1802938 137151671741625515627177 := by
  unfold tailWord_1802938
  simp only [CollatzResearch.WordTrace]
  refine ⟨16439637785567754535240367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43839034094847345427307645 16439637785567754535240367)
  ·
    refine ⟨24659456678351631802860551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16439637785567754535240367 24659456678351631802860551)
    ·
      refine ⟨36989185017527447704290827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24659456678351631802860551 36989185017527447704290827)
      ·
        refine ⟨55483777526291171556436241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36989185017527447704290827 55483777526291171556436241)
        ·
          refine ⟨41612833144718378667327181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55483777526291171556436241 41612833144718378667327181)
          ·
            refine ⟨15604812429269392000247693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41612833144718378667327181 15604812429269392000247693)
            ·
              refine ⟨5851804660976022000092885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15604812429269392000247693 5851804660976022000092885)
              ·
                refine ⟨137151671741625515627177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5851804660976022000092885 137151671741625515627177)
                ·
                  rfl

theorem cell21_1802938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 7].length) (baseStart_1802938 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1802938 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1802938 prefixEnd_1802938 := by exact prefixLift 1802938
  have htrace : WordTrace (prefixWord ++ tailWord_1802938) baseStart_1802938 baseEnd_1802938 := by
    simpa [prefixWord, tailWord_1802938, baseEnd_1802938] using wordTrace_append hprefix tailTrace_1802938
  have hstable : (prefixWord ++ tailWord_1802938).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1802938).length < 2 ^ (prefixWord ++ tailWord_1802938).sum := by decide
  have hdescent : baseEnd_1802938 < baseStart_1802938 := by decide
  rcases family_descends (prefixWord ++ tailWord_1802938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1802972 : List Nat := [2, 2, 5, 1, 1, 2, 2, 6]
def baseStart_1802972 : Nat := 118140960795 + 1802972 * 2 ^ 59
def prefixEnd_1802972 : Nat := 4983230072969 + 3 ^ 40 * 1802972 * 2
def baseEnd_1802972 : Nat := 137154258162700014438265

theorem tailTrace_1802972 : CollatzResearch.WordTrace tailWord_1802972 prefixEnd_1802972 137154258162700014438265 := by
  unfold tailWord_1802972
  simp only [CollatzResearch.WordTrace]
  refine ⟨32879895612073920973849585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43839860816098561298466113 32879895612073920973849585)
  ·
    refine ⟨24659921709055440730387189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32879895612073920973849585 24659921709055440730387189)
    ·
      refine ⟨2311867660223947568473799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24659921709055440730387189 2311867660223947568473799)
      ·
        refine ⟨3467801490335921352710699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2311867660223947568473799 3467801490335921352710699)
        ·
          refine ⟨5201702235503882029066049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3467801490335921352710699 5201702235503882029066049)
          ·
            refine ⟨3901276676627911521799537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5201702235503882029066049 3901276676627911521799537)
            ·
              refine ⟨2925957507470933641349653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3901276676627911521799537 2925957507470933641349653)
              ·
                refine ⟨137154258162700014438265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2925957507470933641349653 137154258162700014438265)
                ·
                  rfl

theorem cell21_1802972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 6].length) (baseStart_1802972 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1802972 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1802972 prefixEnd_1802972 := by exact prefixLift 1802972
  have htrace : WordTrace (prefixWord ++ tailWord_1802972) baseStart_1802972 baseEnd_1802972 := by
    simpa [prefixWord, tailWord_1802972, baseEnd_1802972] using wordTrace_append hprefix tailTrace_1802972
  have hstable : (prefixWord ++ tailWord_1802972).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1802972).length < 2 ^ (prefixWord ++ tailWord_1802972).sum := by decide
  have hdescent : baseEnd_1802972 < baseStart_1802972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1802972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803045 : List Nat := [1, 3, 1, 2, 3, 1, 3, 2, 5]
def baseStart_1803045 : Nat := 118140960795 + 1803045 * 2 ^ 59
def prefixEnd_1803045 : Nat := 4983230072969 + 3 ^ 40 * 1803045 * 2
def baseEnd_1803045 : Nat := 411479434082668138597979

theorem tailTrace_1803045 : CollatzResearch.WordTrace tailWord_1803045 prefixEnd_1803045 411479434082668138597979 := by
  unfold tailWord_1803045
  simp only [CollatzResearch.WordTrace]
  refine ⟨65762453752883375415106589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43841635835255583610071059 65762453752883375415106589)
  ·
    refine ⟨24660920157331265780664971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65762453752883375415106589 24660920157331265780664971)
    ·
      refine ⟨36991380235996898670997457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24660920157331265780664971 36991380235996898670997457)
      ·
        refine ⟨27743535176997674003248093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36991380235996898670997457 27743535176997674003248093)
        ·
          refine ⟨10403825691374127751218035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27743535176997674003248093 10403825691374127751218035)
          ·
            refine ⟨15605738537061191626827053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10403825691374127751218035 15605738537061191626827053)
            ·
              refine ⟨5852151951397946860060145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15605738537061191626827053 5852151951397946860060145)
              ·
                refine ⟨4389113963548460145045109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5852151951397946860060145 4389113963548460145045109)
                ·
                  refine ⟨411479434082668138597979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4389113963548460145045109 411479434082668138597979)
                  ·
                    rfl

theorem cell21_1803045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 2, 5].length) (baseStart_1803045 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1803045 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1803045 prefixEnd_1803045 := by exact prefixLift 1803045
  have htrace : WordTrace (prefixWord ++ tailWord_1803045) baseStart_1803045 baseEnd_1803045 := by
    simpa [prefixWord, tailWord_1803045, baseEnd_1803045] using wordTrace_append hprefix tailTrace_1803045
  have hstable : (prefixWord ++ tailWord_1803045).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803045).length < 2 ^ (prefixWord ++ tailWord_1803045).sum := by decide
  have hdescent : baseEnd_1803045 < baseStart_1803045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803090 : List Nat := [3, 2, 2, 1, 1, 2, 2, 8]
def baseStart_1803090 : Nat := 118140960795 + 1803090 * 2 ^ 59
def prefixEnd_1803090 : Nat := 4983230072969 + 3 ^ 40 * 1803090 * 2
def baseEnd_1803090 : Nat := 137163234565252686782629

theorem tailTrace_1803090 : CollatzResearch.WordTrace tailWord_1803090 prefixEnd_1803090 137163234565252686782629 := by
  unfold tailWord_1803090
  simp only [CollatzResearch.WordTrace]
  refine ⟨16441023759430087025123681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43842730025146898733663149 16441023759430087025123681)
  ·
    refine ⟨12330767819572565268842761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16441023759430087025123681 12330767819572565268842761)
    ·
      refine ⟨9248075864679423951632071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12330767819572565268842761 9248075864679423951632071)
      ·
        refine ⟨13872113797019135927448107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9248075864679423951632071 13872113797019135927448107)
        ·
          refine ⟨20808170695528703891172161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13872113797019135927448107 20808170695528703891172161)
          ·
            refine ⟨15606128021646527918379121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20808170695528703891172161 15606128021646527918379121)
            ·
              refine ⟨11704596016234895938784341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15606128021646527918379121 11704596016234895938784341)
              ·
                refine ⟨137163234565252686782629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11704596016234895938784341 137163234565252686782629)
                ·
                  rfl

theorem cell21_1803090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 8].length) (baseStart_1803090 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1803090 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1803090 prefixEnd_1803090 := by exact prefixLift 1803090
  have htrace : WordTrace (prefixWord ++ tailWord_1803090) baseStart_1803090 baseEnd_1803090 := by
    simpa [prefixWord, tailWord_1803090, baseEnd_1803090] using wordTrace_append hprefix tailTrace_1803090
  have hstable : (prefixWord ++ tailWord_1803090).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803090).length < 2 ^ (prefixWord ++ tailWord_1803090).sum := by decide
  have hdescent : baseEnd_1803090 < baseStart_1803090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803093 : List Nat := [1, 3, 2, 2, 2, 1, 5, 1, 4]
def baseStart_1803093 : Nat := 118140960795 + 1803093 * 2 ^ 59
def prefixEnd_1803093 : Nat := 4983230072969 + 3 ^ 40 * 1803093 * 2
def baseEnd_1803093 : Nat := 411490388336630721797881

theorem tailTrace_1803093 : CollatzResearch.WordTrace tailWord_1803093 prefixEnd_1803093 411490388336630721797881 := by
  unfold tailWord_1803093
  simp only [CollatzResearch.WordTrace]
  refine ⟨65764204456709479612853933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43842802971139653075235955 65764204456709479612853933)
  ·
    refine ⟨24661576671266054854820225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65764204456709479612853933 24661576671266054854820225)
    ·
      refine ⟨18496182503449541141115169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24661576671266054854820225 18496182503449541141115169)
      ·
        refine ⟨13872136877587155855836377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18496182503449541141115169 13872136877587155855836377)
        ·
          refine ⟨10404102658190366891877283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13872136877587155855836377 10404102658190366891877283)
          ·
            refine ⟨15606153987285550337815925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10404102658190366891877283 15606153987285550337815925)
            ·
              refine ⟨1463076936308020344170243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15606153987285550337815925 1463076936308020344170243)
              ·
                refine ⟨2194615404462030516255365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1463076936308020344170243 2194615404462030516255365)
                ·
                  refine ⟨411490388336630721797881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2194615404462030516255365 411490388336630721797881)
                  ·
                    rfl

theorem cell21_1803093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 5, 1, 4].length) (baseStart_1803093 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1803093 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1803093 prefixEnd_1803093 := by exact prefixLift 1803093
  have htrace : WordTrace (prefixWord ++ tailWord_1803093) baseStart_1803093 baseEnd_1803093 := by
    simpa [prefixWord, tailWord_1803093, baseEnd_1803093] using wordTrace_append hprefix tailTrace_1803093
  have hstable : (prefixWord ++ tailWord_1803093).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803093).length < 2 ^ (prefixWord ++ tailWord_1803093).sum := by decide
  have hdescent : baseEnd_1803093 < baseStart_1803093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803107 : List Nat := [1, 1, 1, 5, 3, 1, 4, 5]
def baseStart_1803107 : Nat := 118140960795 + 1803107 * 2 ^ 59
def prefixEnd_1803107 : Nat := 4983230072969 + 3 ^ 40 * 1803107 * 2
def baseEnd_1803107 : Nat := 137164527775789936188173

theorem tailTrace_1803107 : CollatzResearch.WordTrace tailWord_1803107 prefixEnd_1803107 137164527775789936188173 := by
  unfold tailWord_1803107
  simp only [CollatzResearch.WordTrace]
  refine ⟨65764715078658760003863575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43843143385772506669242383 65764715078658760003863575)
  ·
    refine ⟨98647072617988140005795363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65764715078658760003863575 98647072617988140005795363)
    ·
      refine ⟨147970608926982210008693045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98647072617988140005795363 147970608926982210008693045)
      ·
        refine ⟨13872244586904582188314973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 147970608926982210008693045 13872244586904582188314973)
        ·
          refine ⟨5202091720089218320618115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13872244586904582188314973 5202091720089218320618115)
          ·
            refine ⟨7803137580133827480927173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5202091720089218320618115 7803137580133827480927173)
            ·
              refine ⟨1463088296275092652673845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7803137580133827480927173 1463088296275092652673845)
              ·
                refine ⟨137164527775789936188173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1463088296275092652673845 137164527775789936188173)
                ·
                  rfl

theorem cell21_1803107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 4, 5].length) (baseStart_1803107 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1803107 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1803107 prefixEnd_1803107 := by exact prefixLift 1803107
  have htrace : WordTrace (prefixWord ++ tailWord_1803107) baseStart_1803107 baseEnd_1803107 := by
    simpa [prefixWord, tailWord_1803107, baseEnd_1803107] using wordTrace_append hprefix tailTrace_1803107
  have hstable : (prefixWord ++ tailWord_1803107).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803107).length < 2 ^ (prefixWord ++ tailWord_1803107).sum := by decide
  have hdescent : baseEnd_1803107 < baseStart_1803107 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803135 : List Nat := [1, 1, 2, 2, 1, 1, 6, 1, 6]
def baseStart_1803135 : Nat := 118140960795 + 1803135 * 2 ^ 59
def prefixEnd_1803135 : Nat := 4983230072969 + 3 ^ 40 * 1803135 * 2
def baseEnd_1803135 : Nat := 411499973308847982097795

theorem tailTrace_1803135 : CollatzResearch.WordTrace tailWord_1803135 prefixEnd_1803135 411499973308847982097795 := by
  unfold tailWord_1803135
  simp only [CollatzResearch.WordTrace]
  refine ⟨65765736322557320785882859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43843824215038213857255239 65765736322557320785882859)
  ·
    refine ⟨98648604483835981178824289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65765736322557320785882859 98648604483835981178824289)
    ·
      refine ⟨73986453362876985884118217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98648604483835981178824289 73986453362876985884118217)
      ·
        refine ⟨55489840022157739413088663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73986453362876985884118217 55489840022157739413088663)
        ·
          refine ⟨83234760033236609119632995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55489840022157739413088663 83234760033236609119632995)
          ·
            refine ⟨124852140049854913679449493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83234760033236609119632995 124852140049854913679449493)
            ·
              refine ⟨5852444064836949078724195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 124852140049854913679449493 5852444064836949078724195)
              ·
                refine ⟨8778666097255423618086293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5852444064836949078724195 8778666097255423618086293)
                ·
                  refine ⟨411499973308847982097795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8778666097255423618086293 411499973308847982097795)
                  ·
                    rfl

theorem cell21_1803135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 1, 6].length) (baseStart_1803135 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1803135 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1803135 prefixEnd_1803135 := by exact prefixLift 1803135
  have htrace : WordTrace (prefixWord ++ tailWord_1803135) baseStart_1803135 baseEnd_1803135 := by
    simpa [prefixWord, tailWord_1803135, baseEnd_1803135] using wordTrace_append hprefix tailTrace_1803135
  have hstable : (prefixWord ++ tailWord_1803135).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803135).length < 2 ^ (prefixWord ++ tailWord_1803135).sum := by decide
  have hdescent : baseEnd_1803135 < baseStart_1803135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803180 : List Nat := [2, 2, 1, 1, 1, 1, 2, 4, 7]
def baseStart_1803180 : Nat := 118140960795 + 1803180 * 2 ^ 59
def prefixEnd_1803180 : Nat := 4983230072969 + 3 ^ 40 * 1803180 * 2
def baseEnd_1803180 : Nat := 411510242921937903847703

theorem tailTrace_1803180 : CollatzResearch.WordTrace tailWord_1803180 prefixEnd_1803180 411510242921937903847703 := by
  unfold tailWord_1803180
  simp only [CollatzResearch.WordTrace]
  refine ⟨32883688803697146735635497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43844918404929528980847329 32883688803697146735635497)
  ·
    refine ⟨24662766602772860051726623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32883688803697146735635497 24662766602772860051726623)
    ·
      refine ⟨36994149904159290077589935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24662766602772860051726623 36994149904159290077589935)
      ·
        refine ⟨55491224856238935116384903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36994149904159290077589935 55491224856238935116384903)
        ·
          refine ⟨83236837284358402674577355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55491224856238935116384903 83236837284358402674577355)
          ·
            refine ⟨124855255926537604011866033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83236837284358402674577355 124855255926537604011866033)
            ·
              refine ⟨93641441944903203008899525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124855255926537604011866033 93641441944903203008899525)
              ·
                refine ⟨17557770364669350564168661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93641441944903203008899525 17557770364669350564168661)
                ·
                  refine ⟨411510242921937903847703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17557770364669350564168661 411510242921937903847703)
                  ·
                    rfl

theorem cell21_1803180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 7].length) (baseStart_1803180 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1803180 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1803180 prefixEnd_1803180 := by exact prefixLift 1803180
  have htrace : WordTrace (prefixWord ++ tailWord_1803180) baseStart_1803180 baseEnd_1803180 := by
    simpa [prefixWord, tailWord_1803180, baseEnd_1803180] using wordTrace_append hprefix tailTrace_1803180
  have hstable : (prefixWord ++ tailWord_1803180).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803180).length < 2 ^ (prefixWord ++ tailWord_1803180).sum := by decide
  have hdescent : baseEnd_1803180 < baseStart_1803180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803231 : List Nat := [1, 1, 2, 3, 5, 1, 2, 3, 3]
def baseStart_1803231 : Nat := 118140960795 + 1803231 * 2 ^ 59
def prefixEnd_1803231 : Nat := 4983230072969 + 3 ^ 40 * 1803231 * 2
def baseEnd_1803231 : Nat := 411521881816773148497599

theorem tailTrace_1803231 : CollatzResearch.WordTrace tailWord_1803231 prefixEnd_1803231 411521881816773148497599 := by
  unfold tailWord_1803231
  simp only [CollatzResearch.WordTrace]
  refine ⟨65769237730209529181377547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43846158486806352787585031 65769237730209529181377547)
  ·
    refine ⟨98653856595314293772066321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65769237730209529181377547 98653856595314293772066321)
    ·
      refine ⟨73990392446485720329049741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98653856595314293772066321 73990392446485720329049741)
      ·
        refine ⟨27746397167432145123393653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73990392446485720329049741 27746397167432145123393653)
        ·
          refine ⟨2601224734446763605318155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27746397167432145123393653 2601224734446763605318155)
          ·
            refine ⟨3901837101670145407977233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2601224734446763605318155 3901837101670145407977233)
            ·
              refine ⟨2926377826252609055982925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3901837101670145407977233 2926377826252609055982925)
              ·
                refine ⟨1097391684844728395993597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2926377826252609055982925 1097391684844728395993597)
                ·
                  refine ⟨411521881816773148497599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1097391684844728395993597 411521881816773148497599)
                  ·
                    rfl

theorem cell21_1803231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 3, 3].length) (baseStart_1803231 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1803231 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1803231 prefixEnd_1803231 := by exact prefixLift 1803231
  have htrace : WordTrace (prefixWord ++ tailWord_1803231) baseStart_1803231 baseEnd_1803231 := by
    simpa [prefixWord, tailWord_1803231, baseEnd_1803231] using wordTrace_append hprefix tailTrace_1803231
  have hstable : (prefixWord ++ tailWord_1803231).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803231).length < 2 ^ (prefixWord ++ tailWord_1803231).sum := by decide
  have hdescent : baseEnd_1803231 < baseStart_1803231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803242 : List Nat := [3, 1, 3, 1, 2, 3, 8]
def baseStart_1803242 : Nat := 118140960795 + 1803242 * 2 ^ 59
def prefixEnd_1803242 : Nat := 4983230072969 + 3 ^ 40 * 1803242 * 2
def baseEnd_1803242 : Nat := 45724932462959952646027

theorem tailTrace_1803242 : CollatzResearch.WordTrace tailWord_1803242 prefixEnd_1803242 45724932462959952646027 := by
  unfold tailWord_1803242
  simp only [CollatzResearch.WordTrace]
  refine ⟨16442409733292419515006995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43846425955446452040018653 16442409733292419515006995)
  ·
    refine ⟨24663614599938629272510493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16442409733292419515006995 24663614599938629272510493)
    ·
      refine ⟨9248855474976985977191435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24663614599938629272510493 9248855474976985977191435)
      ·
        refine ⟨13873283212465478965787153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9248855474976985977191435 13873283212465478965787153)
        ·
          refine ⟨10404962409349109224340365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13873283212465478965787153 10404962409349109224340365)
          ·
            refine ⟨3901860903505915959127637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10404962409349109224340365 3901860903505915959127637)
            ·
              refine ⟨45724932462959952646027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3901860903505915959127637 45724932462959952646027)
              ·
                rfl

theorem cell21_1803242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 8].length) (baseStart_1803242 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1803242 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1803242 prefixEnd_1803242 := by exact prefixLift 1803242
  have htrace : WordTrace (prefixWord ++ tailWord_1803242) baseStart_1803242 baseEnd_1803242 := by
    simpa [prefixWord, tailWord_1803242, baseEnd_1803242] using wordTrace_append hprefix tailTrace_1803242
  have hstable : (prefixWord ++ tailWord_1803242).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803242).length < 2 ^ (prefixWord ++ tailWord_1803242).sum := by decide
  have hdescent : baseEnd_1803242 < baseStart_1803242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803282 : List Nat := [3, 2, 5, 1, 1, 2, 1, 3, 3]
def baseStart_1803282 : Nat := 118140960795 + 1803282 * 2 ^ 59
def prefixEnd_1803282 : Nat := 4983230072969 + 3 ^ 40 * 1803282 * 2
def baseEnd_1803282 : Nat := 411533520711608393147495

theorem tailTrace_1803282 : CollatzResearch.WordTrace tailWord_1803282 prefixEnd_1803282 411533520711608393147495 := by
  unfold tailWord_1803282
  simp only [CollatzResearch.WordTrace]
  refine ⟨16442774463256191222871025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43847398568683176594322733 16442774463256191222871025)
  ·
    refine ⟨12332080847442143417153269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16442774463256191222871025 12332080847442143417153269)
    ·
      refine ⟨1156132579447700945358119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12332080847442143417153269 1156132579447700945358119)
      ·
        refine ⟨1734198869171551418037179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1156132579447700945358119 1734198869171551418037179)
        ·
          refine ⟨2601298303757327127055769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1734198869171551418037179 2601298303757327127055769)
          ·
            refine ⟨1950973727817995345291827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2601298303757327127055769 1950973727817995345291827)
            ·
              refine ⟨2926460591726993017937741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1950973727817995345291827 2926460591726993017937741)
              ·
                refine ⟨1097422721897622381726653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2926460591726993017937741 1097422721897622381726653)
                ·
                  refine ⟨411533520711608393147495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1097422721897622381726653 411533520711608393147495)
                  ·
                    rfl

theorem cell21_1803282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 3, 3].length) (baseStart_1803282 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1803282 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1803282 prefixEnd_1803282 := by exact prefixLift 1803282
  have htrace : WordTrace (prefixWord ++ tailWord_1803282) baseStart_1803282 baseEnd_1803282 := by
    simpa [prefixWord, tailWord_1803282, baseEnd_1803282] using wordTrace_append hprefix tailTrace_1803282
  have hstable : (prefixWord ++ tailWord_1803282).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803282).length < 2 ^ (prefixWord ++ tailWord_1803282).sum := by decide
  have hdescent : baseEnd_1803282 < baseStart_1803282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803321 : List Nat := [1, 2, 1, 5, 2, 1, 4, 1, 4]
def baseStart_1803321 : Nat := 118140960795 + 1803321 * 2 ^ 59
def prefixEnd_1803321 : Nat := 4983230072969 + 3 ^ 40 * 1803321 * 2
def baseEnd_1803321 : Nat := 411542421042952991997415

theorem tailTrace_1803321 : CollatzResearch.WordTrace tailWord_1803321 prefixEnd_1803321 411542421042952991997415 := by
  unfold tailWord_1803321
  simp only [CollatzResearch.WordTrace]
  refine ⟨65772520299883474552153817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43848346866588983034769211 65772520299883474552153817)
  ·
    refine ⟨49329390224912605914115363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65772520299883474552153817 49329390224912605914115363)
    ·
      refine ⟨73994085337368908871173045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49329390224912605914115363 73994085337368908871173045)
      ·
        refine ⟨6936945500378335206672473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 73994085337368908871173045 6936945500378335206672473)
        ·
          refine ⟨5202709125283751405004355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6936945500378335206672473 5202709125283751405004355)
          ·
            refine ⟨7804063687925627107506533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5202709125283751405004355 7804063687925627107506533)
            ·
              refine ⟨1463261941486055082657475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7804063687925627107506533 1463261941486055082657475)
              ·
                refine ⟨2194892912229082623986213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1463261941486055082657475 2194892912229082623986213)
                ·
                  refine ⟨411542421042952991997415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2194892912229082623986213 411542421042952991997415)
                  ·
                    rfl

theorem cell21_1803321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 4, 1, 4].length) (baseStart_1803321 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1803321 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1803321 prefixEnd_1803321 := by exact prefixLift 1803321
  have htrace : WordTrace (prefixWord ++ tailWord_1803321) baseStart_1803321 baseEnd_1803321 := by
    simpa [prefixWord, tailWord_1803321, baseEnd_1803321] using wordTrace_append hprefix tailTrace_1803321
  have hstable : (prefixWord ++ tailWord_1803321).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803321).length < 2 ^ (prefixWord ++ tailWord_1803321).sum := by decide
  have hdescent : baseEnd_1803321 < baseStart_1803321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803358 : List Nat := [4, 4, 1, 1, 1, 3, 2, 2, 3]
def baseStart_1803358 : Nat := 118140960795 + 1803358 * 2 ^ 59
def prefixEnd_1803358 : Nat := 4983230072969 + 3 ^ 40 * 1803358 * 2
def baseEnd_1803358 : Nat := 411550864947049149880673

theorem tailTrace_1803358 : CollatzResearch.WordTrace tailWord_1803358 prefixEnd_1803358 411550864947049149880673 := by
  unfold tailWord_1803358
  simp only [CollatzResearch.WordTrace]
  refine ⟨8221733725093678733906341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43849246533832953247500485 8221733725093678733906341)
  ·
    refine ⟨1541575073455064762607439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8221733725093678733906341 1541575073455064762607439)
    ·
      refine ⟨2312362610182597143911159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1541575073455064762607439 2312362610182597143911159)
      ·
        refine ⟨3468543915273895715866739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2312362610182597143911159 3468543915273895715866739)
        ·
          refine ⟨5202815872910843573800109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3468543915273895715866739 5202815872910843573800109)
          ·
            refine ⟨1951055952341566340175041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5202815872910843573800109 1951055952341566340175041)
            ·
              refine ⟨1463291964256174755131281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1951055952341566340175041 1463291964256174755131281)
              ·
                refine ⟨1097468973192131066348461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1463291964256174755131281 1097468973192131066348461)
                ·
                  refine ⟨411550864947049149880673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1097468973192131066348461 411550864947049149880673)
                  ·
                    rfl

theorem cell21_1803358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_1803358 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1803358 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1803358 prefixEnd_1803358 := by exact prefixLift 1803358
  have htrace : WordTrace (prefixWord ++ tailWord_1803358) baseStart_1803358 baseEnd_1803358 := by
    simpa [prefixWord, tailWord_1803358, baseEnd_1803358] using wordTrace_append hprefix tailTrace_1803358
  have hstable : (prefixWord ++ tailWord_1803358).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803358).length < 2 ^ (prefixWord ++ tailWord_1803358).sum := by decide
  have hdescent : baseEnd_1803358 < baseStart_1803358 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803377 : List Nat := [1, 2, 2, 2, 1, 1, 2, 10]
def baseStart_1803377 : Nat := 118140960795 + 1803377 * 2 ^ 59
def prefixEnd_1803377 : Nat := 4983230072969 + 3 ^ 40 * 1803377 * 2
def baseEnd_1803377 : Nat := 137185067001969779687989

theorem tailTrace_1803377 : CollatzResearch.WordTrace tailWord_1803377 prefixEnd_1803377 137185067001969779687989 := by
  unfold tailWord_1803377
  simp only [CollatzResearch.WordTrace]
  refine ⟨65774562787680596116192385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43849708525120397410794923 65774562787680596116192385)
  ·
    refine ⟨49330922090760447087144289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65774562787680596116192385 49330922090760447087144289)
    ·
      refine ⟨36998191568070335315358217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49330922090760447087144289 36998191568070335315358217)
      ·
        refine ⟨27748643676052751486518663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36998191568070335315358217 27748643676052751486518663)
        ·
          refine ⟨41622965514079127229777995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27748643676052751486518663 41622965514079127229777995)
          ·
            refine ⟨62434448271118690844666993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41622965514079127229777995 62434448271118690844666993)
            ·
              refine ⟨46825836203339018133500245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62434448271118690844666993 46825836203339018133500245)
              ·
                refine ⟨137185067001969779687989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 46825836203339018133500245 137185067001969779687989)
                ·
                  rfl

theorem cell21_1803377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 10].length) (baseStart_1803377 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1803377 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1803377 prefixEnd_1803377 := by exact prefixLift 1803377
  have htrace : WordTrace (prefixWord ++ tailWord_1803377) baseStart_1803377 baseEnd_1803377 := by
    simpa [prefixWord, tailWord_1803377, baseEnd_1803377] using wordTrace_append hprefix tailTrace_1803377
  have hstable : (prefixWord ++ tailWord_1803377).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803377).length < 2 ^ (prefixWord ++ tailWord_1803377).sum := by decide
  have hdescent : baseEnd_1803377 < baseStart_1803377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803425 : List Nat := [1, 2, 3, 3, 1, 1, 4, 1, 5]
def baseStart_1803425 : Nat := 118140960795 + 1803425 * 2 ^ 59
def prefixEnd_1803425 : Nat := 4983230072969 + 3 ^ 40 * 1803425 * 2
def baseEnd_1803425 : Nat := 411566155259871922263869

theorem tailTrace_1803425 : CollatzResearch.WordTrace tailWord_1803425 prefixEnd_1803425 411566155259871922263869 := by
  unfold tailWord_1803425
  simp only [CollatzResearch.WordTrace]
  refine ⟨65776313491506700313939729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43850875661004466875959819 65776313491506700313939729)
  ·
    refine ⟨49332235118630025235454797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65776313491506700313939729 49332235118630025235454797)
    ·
      refine ⟨18499588169486259463295549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49332235118630025235454797 18499588169486259463295549)
      ·
        refine ⟨6937345563557347298735831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18499588169486259463295549 6937345563557347298735831)
        ·
          refine ⟨10406018345336020948103747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6937345563557347298735831 10406018345336020948103747)
          ·
            refine ⟨15609027518004031422155621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10406018345336020948103747 15609027518004031422155621)
            ·
              refine ⟨2926692659625755891654179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15609027518004031422155621 2926692659625755891654179)
              ·
                refine ⟨4390038989438633837481269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2926692659625755891654179 4390038989438633837481269)
                ·
                  refine ⟨411566155259871922263869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4390038989438633837481269 411566155259871922263869)
                  ·
                    rfl

theorem cell21_1803425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 1, 5].length) (baseStart_1803425 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1803425 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1803425 prefixEnd_1803425 := by exact prefixLift 1803425
  have htrace : WordTrace (prefixWord ++ tailWord_1803425) baseStart_1803425 baseEnd_1803425 := by
    simpa [prefixWord, tailWord_1803425, baseEnd_1803425] using wordTrace_append hprefix tailTrace_1803425
  have hstable : (prefixWord ++ tailWord_1803425).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803425).length < 2 ^ (prefixWord ++ tailWord_1803425).sum := by decide
  have hdescent : baseEnd_1803425 < baseStart_1803425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803439 : List Nat := [1, 1, 2, 1, 2, 3, 2, 5, 4]
def baseStart_1803439 : Nat := 118140960795 + 1803439 * 2 ^ 59
def prefixEnd_1803439 : Nat := 4983230072969 + 3 ^ 40 * 1803439 * 2
def baseEnd_1803439 : Nat := 411569350250611009030507

theorem tailTrace_1803439 : CollatzResearch.WordTrace tailWord_1803439 prefixEnd_1803439 411569350250611009030507 := by
  unfold tailWord_1803439
  simp only [CollatzResearch.WordTrace]
  refine ⟨65776824113455980704949371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43851216075637320469966247 65776824113455980704949371)
  ·
    refine ⟨98665236170183971057424057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65776824113455980704949371 98665236170183971057424057)
    ·
      refine ⟨73998927127637978293068043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98665236170183971057424057 73998927127637978293068043)
      ·
        refine ⟨110998390691456967439602065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73998927127637978293068043 110998390691456967439602065)
        ·
          refine ⟨83248793018592725579701549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110998390691456967439602065 83248793018592725579701549)
          ·
            refine ⟨31218297381972272092388081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83248793018592725579701549 31218297381972272092388081)
            ·
              refine ⟨23413723036479204069291061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31218297381972272092388081 23413723036479204069291061)
              ·
                refine ⟨2195036534669925381496037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23413723036479204069291061 2195036534669925381496037)
                ·
                  refine ⟨411569350250611009030507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2195036534669925381496037 411569350250611009030507)
                  ·
                    rfl

theorem cell21_1803439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 5, 4].length) (baseStart_1803439 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1803439 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1803439 prefixEnd_1803439 := by exact prefixLift 1803439
  have htrace : WordTrace (prefixWord ++ tailWord_1803439) baseStart_1803439 baseEnd_1803439 := by
    simpa [prefixWord, tailWord_1803439, baseEnd_1803439] using wordTrace_append hprefix tailTrace_1803439
  have hstable : (prefixWord ++ tailWord_1803439).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803439).length < 2 ^ (prefixWord ++ tailWord_1803439).sum := by decide
  have hdescent : baseEnd_1803439 < baseStart_1803439 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803462 : List Nat := [6, 1, 2, 2, 2, 1, 7]
def baseStart_1803462 : Nat := 118140960795 + 1803462 * 2 ^ 59
def prefixEnd_1803462 : Nat := 4983230072969 + 3 ^ 40 * 1803462 * 2
def baseEnd_1803462 : Nat := 45730511018218675571903

theorem tailTrace_1803462 : CollatzResearch.WordTrace tailWord_1803462 prefixEnd_1803462 45730511018218675571903 := by
  unfold tailWord_1803462
  simp only [CollatzResearch.WordTrace]
  refine ⟨2055551968511645488532395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 43851775328248437088691093 2055551968511645488532395)
  ·
    refine ⟨3083327952767468232798593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2055551968511645488532395 3083327952767468232798593)
    ·
      refine ⟨2312495964575601174598945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3083327952767468232798593 2312495964575601174598945)
      ·
        refine ⟨1734371973431700880949209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2312495964575601174598945 1734371973431700880949209)
        ·
          refine ⟨1300778980073775660711907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1734371973431700880949209 1300778980073775660711907)
          ·
            refine ⟨1951168470110663491067861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1300778980073775660711907 1951168470110663491067861)
            ·
              refine ⟨45730511018218675571903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1951168470110663491067861 45730511018218675571903)
              ·
                rfl

theorem cell21_1803462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 7].length) (baseStart_1803462 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1803462 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1803462 prefixEnd_1803462 := by exact prefixLift 1803462
  have htrace : WordTrace (prefixWord ++ tailWord_1803462) baseStart_1803462 baseEnd_1803462 := by
    simpa [prefixWord, tailWord_1803462, baseEnd_1803462] using wordTrace_append hprefix tailTrace_1803462
  have hstable : (prefixWord ++ tailWord_1803462).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803462).length < 2 ^ (prefixWord ++ tailWord_1803462).sum := by decide
  have hdescent : baseEnd_1803462 < baseStart_1803462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803476 : List Nat := [2, 4, 1, 4, 2, 1, 1, 1, 5]
def baseStart_1803476 : Nat := 118140960795 + 1803476 * 2 ^ 59
def prefixEnd_1803476 : Nat := 4983230072969 + 3 ^ 40 * 1803476 * 2
def baseEnd_1803476 : Nat := 411577794154707166913765

theorem tailTrace_1803476 : CollatzResearch.WordTrace tailWord_1803476 prefixEnd_1803476 411577794154707166913765 := by
  unfold tailWord_1803476
  simp only [CollatzResearch.WordTrace]
  refine ⟨32889086807160968012023141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43852115742881290682697521 32889086807160968012023141)
  ·
    refine ⟨6166703776342681502254339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32889086807160968012023141 6166703776342681502254339)
    ·
      refine ⟨9250055664514022253381509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6166703776342681502254339 9250055664514022253381509)
      ·
        refine ⟨1734385437096379172509033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9250055664514022253381509 1734385437096379172509033)
        ·
          refine ⟨1300789077822284379381775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1734385437096379172509033 1300789077822284379381775)
          ·
            refine ⟨1951183616733426569072663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1300789077822284379381775 1951183616733426569072663)
            ·
              refine ⟨2926775425100139853608995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1951183616733426569072663 2926775425100139853608995)
              ·
                refine ⟨4390163137650209780413493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2926775425100139853608995 4390163137650209780413493)
                ·
                  refine ⟨411577794154707166913765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4390163137650209780413493 411577794154707166913765)
                  ·
                    rfl

theorem cell21_1803476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 1, 5].length) (baseStart_1803476 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1803476 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1803476 prefixEnd_1803476 := by exact prefixLift 1803476
  have htrace : WordTrace (prefixWord ++ tailWord_1803476) baseStart_1803476 baseEnd_1803476 := by
    simpa [prefixWord, tailWord_1803476, baseEnd_1803476] using wordTrace_append hprefix tailTrace_1803476
  have hstable : (prefixWord ++ tailWord_1803476).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803476).length < 2 ^ (prefixWord ++ tailWord_1803476).sum := by decide
  have hdescent : baseEnd_1803476 < baseStart_1803476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803532 : List Nat := [2, 2, 1, 2, 2, 4, 2, 2, 4]
def baseStart_1803532 : Nat := 118140960795 + 1803532 * 2 ^ 59
def prefixEnd_1803532 : Nat := 4983230072969 + 3 ^ 40 * 1803532 * 2
def baseEnd_1803532 : Nat := 411590574117663513980317

theorem tailTrace_1803532 : CollatzResearch.WordTrace tailWord_1803532 prefixEnd_1803532 411590574117663513980317 := by
  unfold tailWord_1803532
  simp only [CollatzResearch.WordTrace]
  refine ⟨32890108051059528794042425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43853477401412705058723233 32890108051059528794042425)
  ·
    refine ⟨24667581038294646595531819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32890108051059528794042425 24667581038294646595531819)
    ·
      refine ⟨37001371557441969893297729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24667581038294646595531819 37001371557441969893297729)
      ·
        refine ⟨27751028668081477419973297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37001371557441969893297729 27751028668081477419973297)
        ·
          refine ⟨20813271501061108064979973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27751028668081477419973297 20813271501061108064979973)
          ·
            refine ⟨3902488406448957762183745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20813271501061108064979973 3902488406448957762183745)
            ·
              refine ⟨2926866304836718321637809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3902488406448957762183745 2926866304836718321637809)
              ·
                refine ⟨2195149728627538741228357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2926866304836718321637809 2195149728627538741228357)
                ·
                  refine ⟨411590574117663513980317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2195149728627538741228357 411590574117663513980317)
                  ·
                    rfl

theorem cell21_1803532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 2, 4].length) (baseStart_1803532 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1803532 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1803532 prefixEnd_1803532 := by exact prefixLift 1803532
  have htrace : WordTrace (prefixWord ++ tailWord_1803532) baseStart_1803532 baseEnd_1803532 := by
    simpa [prefixWord, tailWord_1803532, baseEnd_1803532] using wordTrace_append hprefix tailTrace_1803532
  have hstable : (prefixWord ++ tailWord_1803532).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803532).length < 2 ^ (prefixWord ++ tailWord_1803532).sum := by decide
  have hdescent : baseEnd_1803532 < baseStart_1803532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803546 : List Nat := [3, 1, 1, 3, 3, 1, 3, 6]
def baseStart_1803546 : Nat := 118140960795 + 1803546 * 2 ^ 59
def prefixEnd_1803546 : Nat := 4983230072969 + 3 ^ 40 * 1803546 * 2
def baseEnd_1803546 : Nat := 137197923036134200248985

theorem tailTrace_1803546 : CollatzResearch.WordTrace tailWord_1803546 prefixEnd_1803546 137197923036134200248985 := by
  unfold tailWord_1803546
  simp only [CollatzResearch.WordTrace]
  refine ⟨16445181681017084494773623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43853817816045558652729661 16445181681017084494773623)
  ·
    refine ⟨24667772521525626742160435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16445181681017084494773623 24667772521525626742160435)
    ·
      refine ⟨37001658782288440113240653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24667772521525626742160435 37001658782288440113240653)
      ·
        refine ⟨13875622043358165042465245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37001658782288440113240653 13875622043358165042465245)
        ·
          refine ⟨5203358266259311890924467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13875622043358165042465245 5203358266259311890924467)
          ·
            refine ⟨7805037399388967836386701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5203358266259311890924467 7805037399388967836386701)
            ·
              refine ⟨2926889024770862938645013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7805037399388967836386701 2926889024770862938645013)
              ·
                refine ⟨137197923036134200248985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2926889024770862938645013 137197923036134200248985)
                ·
                  rfl

theorem cell21_1803546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 6].length) (baseStart_1803546 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1803546 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1803546 prefixEnd_1803546 := by exact prefixLift 1803546
  have htrace : WordTrace (prefixWord ++ tailWord_1803546) baseStart_1803546 baseEnd_1803546 := by
    simpa [prefixWord, tailWord_1803546, baseEnd_1803546] using wordTrace_append hprefix tailTrace_1803546
  have hstable : (prefixWord ++ tailWord_1803546).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803546).length < 2 ^ (prefixWord ++ tailWord_1803546).sum := by decide
  have hdescent : baseEnd_1803546 < baseStart_1803546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803591 : List Nat := [1, 1, 4, 1, 2, 4, 1, 1, 6]
def baseStart_1803591 : Nat := 118140960795 + 1803591 * 2 ^ 59
def prefixEnd_1803591 : Nat := 4983230072969 + 3 ^ 40 * 1803591 * 2
def baseEnd_1803591 : Nat := 411604038721492522496863

theorem tailTrace_1803591 : CollatzResearch.WordTrace tailWord_1803591 prefixEnd_1803591 411604038721492522496863 := by
  unfold tailWord_1803591
  simp only [CollatzResearch.WordTrace]
  refine ⟨65782368008905310664482627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43854912005936873776321751 65782368008905310664482627)
  ·
    refine ⟨98673552013357965996723941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65782368008905310664482627 98673552013357965996723941)
    ·
      refine ⟨18501291002504618624385739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98673552013357965996723941 18501291002504618624385739)
      ·
        refine ⟨27751936503756927936578609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18501291002504618624385739 27751936503756927936578609)
        ·
          refine ⟨20813952377817695952433957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27751936503756927936578609 20813952377817695952433957)
          ·
            refine ⟨3902616070840817991081367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20813952377817695952433957 3902616070840817991081367)
            ·
              refine ⟨5853924106261226986622051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3902616070840817991081367 5853924106261226986622051)
              ·
                refine ⟨8780886159391840479933077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5853924106261226986622051 8780886159391840479933077)
                ·
                  refine ⟨411604038721492522496863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8780886159391840479933077 411604038721492522496863)
                  ·
                    rfl

theorem cell21_1803591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 1, 6].length) (baseStart_1803591 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1803591 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1803591 prefixEnd_1803591 := by exact prefixLift 1803591
  have htrace : WordTrace (prefixWord ++ tailWord_1803591) baseStart_1803591 baseEnd_1803591 := by
    simpa [prefixWord, tailWord_1803591, baseEnd_1803591] using wordTrace_append hprefix tailTrace_1803591
  have hstable : (prefixWord ++ tailWord_1803591).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803591).length < 2 ^ (prefixWord ++ tailWord_1803591).sum := by decide
  have hdescent : baseEnd_1803591 < baseStart_1803591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803608 : List Nat := [2, 1, 2, 2, 1, 1, 7, 1, 4]
def baseStart_1803608 : Nat := 118140960795 + 1803608 * 2 ^ 59
def prefixEnd_1803608 : Nat := 4983230072969 + 3 ^ 40 * 1803608 * 2
def baseEnd_1803608 : Nat := 411607918353104270713495

theorem tailTrace_1803608 : CollatzResearch.WordTrace tailWord_1803608 prefixEnd_1803608 411607918353104270713495 := by
  unfold tailWord_1803608
  simp only [CollatzResearch.WordTrace]
  refine ⟨32891494024921861283925739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43855325366562481711900985 32891494024921861283925739)
  ·
    refine ⟨49337241037382791925888609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32891494024921861283925739 49337241037382791925888609)
    ·
      refine ⟨37002930778037093944416457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49337241037382791925888609 37002930778037093944416457)
      ·
        refine ⟨27752198083527820458312343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37002930778037093944416457 27752198083527820458312343)
        ·
          refine ⟨41628297125291730687468515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27752198083527820458312343 41628297125291730687468515)
          ·
            refine ⟨62442445687937596031202773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41628297125291730687468515 62442445687937596031202773)
            ·
              refine ⟨1463494820811037406981315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 62442445687937596031202773 1463494820811037406981315)
              ·
                refine ⟨2195242231216556110471973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1463494820811037406981315 2195242231216556110471973)
                ·
                  refine ⟨411607918353104270713495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2195242231216556110471973 411607918353104270713495)
                  ·
                    rfl

theorem cell21_1803608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 7, 1, 4].length) (baseStart_1803608 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1803608 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1803608 prefixEnd_1803608 := by exact prefixLift 1803608
  have htrace : WordTrace (prefixWord ++ tailWord_1803608) baseStart_1803608 baseEnd_1803608 := by
    simpa [prefixWord, tailWord_1803608, baseEnd_1803608] using wordTrace_append hprefix tailTrace_1803608
  have hstable : (prefixWord ++ tailWord_1803608).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803608).length < 2 ^ (prefixWord ++ tailWord_1803608).sum := by decide
  have hdescent : baseEnd_1803608 < baseStart_1803608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803653 : List Nat := [1, 3, 1, 1, 3, 1, 2, 6, 3]
def baseStart_1803653 : Nat := 118140960795 + 1803653 * 2 ^ 59
def prefixEnd_1803653 : Nat := 4983230072969 + 3 ^ 40 * 1803653 * 2
def baseEnd_1803653 : Nat := 411618187966194192463403

theorem tailTrace_1803653 : CollatzResearch.WordTrace tailWord_1803653 prefixEnd_1803653 411618187966194192463403 := by
  unfold tailWord_1803653
  simp only [CollatzResearch.WordTrace]
  refine ⟨65784629334680695253239613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43856419556453796835493075 65784629334680695253239613)
  ·
    refine ⟨24669236000505260719964855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65784629334680695253239613 24669236000505260719964855)
    ·
      refine ⟨37003854000757891079947283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24669236000505260719964855 37003854000757891079947283)
      ·
        refine ⟨55505781001136836619920925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37003854000757891079947283 55505781001136836619920925)
        ·
          refine ⟨20814667875426313732470347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55505781001136836619920925 20814667875426313732470347)
          ·
            refine ⟨31222001813139470598705521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20814667875426313732470347 31222001813139470598705521)
            ·
              refine ⟨23416501359854602949029141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31222001813139470598705521 23416501359854602949029141)
              ·
                refine ⟨1097648501243184513235741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 23416501359854602949029141 1097648501243184513235741)
                ·
                  refine ⟨411618187966194192463403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1097648501243184513235741 411618187966194192463403)
                  ·
                    rfl

theorem cell21_1803653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 6, 3].length) (baseStart_1803653 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1803653 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1803653 prefixEnd_1803653 := by exact prefixLift 1803653
  have htrace : WordTrace (prefixWord ++ tailWord_1803653) baseStart_1803653 baseEnd_1803653 := by
    simpa [prefixWord, tailWord_1803653, baseEnd_1803653] using wordTrace_append hprefix tailTrace_1803653
  have hstable : (prefixWord ++ tailWord_1803653).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803653).length < 2 ^ (prefixWord ++ tailWord_1803653).sum := by decide
  have hdescent : baseEnd_1803653 < baseStart_1803653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803760 : List Nat := [2, 1, 1, 1, 3, 6, 1, 2, 4]
def baseStart_1803760 : Nat := 118140960795 + 1803760 * 2 ^ 59
def prefixEnd_1803760 : Nat := 4983230072969 + 3 ^ 40 * 1803760 * 2
def baseEnd_1803760 : Nat := 411642606823985784179851

theorem tailTrace_1803760 : CollatzResearch.WordTrace tailWord_1803760 prefixEnd_1803760 411642606823985784179851 := by
  unfold tailWord_1803760
  simp only [CollatzResearch.WordTrace]
  refine ⟨32894265972646526263692367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43859021296862035018256489 32894265972646526263692367)
  ·
    refine ⟨49341398958969789395538551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32894265972646526263692367 49341398958969789395538551)
    ·
      refine ⟨74012098438454684093307827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49341398958969789395538551 74012098438454684093307827)
      ·
        refine ⟨111018147657682026139961741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74012098438454684093307827 111018147657682026139961741)
        ·
          refine ⟨41631805371630759802485653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111018147657682026139961741 41631805371630759802485653)
          ·
            refine ⟨1951490876795191865741515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 41631805371630759802485653 1951490876795191865741515)
            ·
              refine ⟨2927236315192787798612273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1951490876795191865741515 2927236315192787798612273)
              ·
                refine ⟨2195427236394590848959205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2927236315192787798612273 2195427236394590848959205)
                ·
                  refine ⟨411642606823985784179851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2195427236394590848959205 411642606823985784179851)
                  ·
                    rfl

theorem cell21_1803760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 2, 4].length) (baseStart_1803760 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1803760 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1803760 prefixEnd_1803760 := by exact prefixLift 1803760
  have htrace : WordTrace (prefixWord ++ tailWord_1803760) baseStart_1803760 baseEnd_1803760 := by
    simpa [prefixWord, tailWord_1803760, baseEnd_1803760] using wordTrace_append hprefix tailTrace_1803760
  have hstable : (prefixWord ++ tailWord_1803760).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803760).length < 2 ^ (prefixWord ++ tailWord_1803760).sum := by decide
  have hdescent : baseEnd_1803760 < baseStart_1803760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803771 : List Nat := [1, 1, 1, 1, 1, 3, 2, 2, 9]
def baseStart_1803771 : Nat := 118140960795 + 1803771 * 2 ^ 59
def prefixEnd_1803771 : Nat := 4983230072969 + 3 ^ 40 * 1803771 * 2
def baseEnd_1803771 : Nat := 411645117173852209496495

theorem tailTrace_1803771 : CollatzResearch.WordTrace tailWord_1803771 prefixEnd_1803771 411645117173852209496495 := by
  unfold tailWord_1803771
  simp only [CollatzResearch.WordTrace]
  refine ⟨65788933148253201406035167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43859288765502134270690111 65788933148253201406035167)
  ·
    refine ⟨98683399722379802109052751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65788933148253201406035167 98683399722379802109052751)
    ·
      refine ⟨148025099583569703163579127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98683399722379802109052751 148025099583569703163579127)
      ·
        refine ⟨222037649375354554745368691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148025099583569703163579127 222037649375354554745368691)
        ·
          refine ⟨333056474063031832118053037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222037649375354554745368691 333056474063031832118053037)
          ·
            refine ⟨124896177773636937044269889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 333056474063031832118053037 124896177773636937044269889)
            ·
              refine ⟨93672133330227702783202417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124896177773636937044269889 93672133330227702783202417)
              ·
                refine ⟨70254099997670777087401813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93672133330227702783202417 70254099997670777087401813)
                ·
                  refine ⟨411645117173852209496495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 70254099997670777087401813 411645117173852209496495)
                  ·
                    rfl

theorem cell21_1803771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 9].length) (baseStart_1803771 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1803771 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1803771 prefixEnd_1803771 := by exact prefixLift 1803771
  have htrace : WordTrace (prefixWord ++ tailWord_1803771) baseStart_1803771 baseEnd_1803771 := by
    simpa [prefixWord, tailWord_1803771, baseEnd_1803771] using wordTrace_append hprefix tailTrace_1803771
  have hstable : (prefixWord ++ tailWord_1803771).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803771).length < 2 ^ (prefixWord ++ tailWord_1803771).sum := by decide
  have hdescent : baseEnd_1803771 < baseStart_1803771 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803777 : List Nat := [1, 2, 4, 1, 4, 1, 3, 1, 4]
def baseStart_1803777 : Nat := 118140960795 + 1803777 * 2 ^ 59
def prefixEnd_1803777 : Nat := 4983230072969 + 3 ^ 40 * 1803777 * 2
def baseEnd_1803777 : Nat := 411646486455597532396483

theorem tailTrace_1803777 : CollatzResearch.WordTrace tailWord_1803777 prefixEnd_1803777 411646486455597532396483 := by
  unfold tailWord_1803777
  simp only [CollatzResearch.WordTrace]
  refine ⟨65789151986231464430753585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43859434657487642953835723 65789151986231464430753585)
  ·
    refine ⟨49341863989673598323065189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65789151986231464430753585 49341863989673598323065189)
    ·
      refine ⟨9251599498063799685574723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49341863989673598323065189 9251599498063799685574723)
      ·
        refine ⟨13877399247095699528362085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9251599498063799685574723 13877399247095699528362085)
        ·
          refine ⟨2602012358830443661567891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13877399247095699528362085 2602012358830443661567891)
          ·
            refine ⟨3903018538245665492351837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2602012358830443661567891 3903018538245665492351837)
            ·
              refine ⟨1463631951842124559631939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3903018538245665492351837 1463631951842124559631939)
              ·
                refine ⟨2195447927763186839447909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1463631951842124559631939 2195447927763186839447909)
                ·
                  refine ⟨411646486455597532396483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2195447927763186839447909 411646486455597532396483)
                  ·
                    rfl

theorem cell21_1803777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 3, 1, 4].length) (baseStart_1803777 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1803777 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1803777 prefixEnd_1803777 := by exact prefixLift 1803777
  have htrace : WordTrace (prefixWord ++ tailWord_1803777) baseStart_1803777 baseEnd_1803777 := by
    simpa [prefixWord, tailWord_1803777, baseEnd_1803777] using wordTrace_append hprefix tailTrace_1803777
  have hstable : (prefixWord ++ tailWord_1803777).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803777).length < 2 ^ (prefixWord ++ tailWord_1803777).sum := by decide
  have hdescent : baseEnd_1803777 < baseStart_1803777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803822 : List Nat := [4, 1, 3, 1, 2, 3, 1, 1, 5]
def baseStart_1803822 : Nat := 118140960795 + 1803822 * 2 ^ 59
def prefixEnd_1803822 : Nat := 4983230072969 + 3 ^ 40 * 1803822 * 2
def baseEnd_1803822 : Nat := 411656756068687454146391

theorem tailTrace_1803822 : CollatzResearch.WordTrace tailWord_1803822 prefixEnd_1803822 411656756068687454146391 := by
  unfold tailWord_1803822
  simp only [CollatzResearch.WordTrace]
  refine ⟨8223849158883554639517715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43860528847378958077427813 8223849158883554639517715)
  ·
    refine ⟨12335773738325331959276573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8223849158883554639517715 12335773738325331959276573)
    ·
      refine ⟨4625915151871999484728715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12335773738325331959276573 4625915151871999484728715)
      ·
        refine ⟨6938872727807999227093073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4625915151871999484728715 6938872727807999227093073)
        ·
          refine ⟨5204154545855999420319805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6938872727807999227093073 5204154545855999420319805)
          ·
            refine ⟨1951557954695999782619927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5204154545855999420319805 1951557954695999782619927)
            ·
              refine ⟨2927336932043999673929891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1951557954695999782619927 2927336932043999673929891)
              ·
                refine ⟨4391005398065999510894837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2927336932043999673929891 4391005398065999510894837)
                ·
                  refine ⟨411656756068687454146391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4391005398065999510894837 411656756068687454146391)
                  ·
                    rfl

theorem cell21_1803822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 1, 5].length) (baseStart_1803822 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1803822 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1803822 prefixEnd_1803822 := by exact prefixLift 1803822
  have htrace : WordTrace (prefixWord ++ tailWord_1803822) baseStart_1803822 baseEnd_1803822 := by
    simpa [prefixWord, tailWord_1803822, baseEnd_1803822] using wordTrace_append hprefix tailTrace_1803822
  have hstable : (prefixWord ++ tailWord_1803822).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803822).length < 2 ^ (prefixWord ++ tailWord_1803822).sum := by decide
  have hdescent : baseEnd_1803822 < baseStart_1803822 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803833 : List Nat := [1, 2, 1, 5, 1, 2, 1, 8]
def baseStart_1803833 : Nat := 118140960795 + 1803833 * 2 ^ 59
def prefixEnd_1803833 : Nat := 4983230072969 + 3 ^ 40 * 1803833 * 2
def baseEnd_1803833 : Nat := 137219755472851293154345

theorem tailTrace_1803833 : CollatzResearch.WordTrace tailWord_1803833 prefixEnd_1803833 137219755472851293154345 := by
  unfold tailWord_1803833
  simp only [CollatzResearch.WordTrace]
  refine ⟨65791194474028585994792153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43860796316019057329861435 65791194474028585994792153)
  ·
    refine ⟨49343395855521439496094115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65791194474028585994792153 49343395855521439496094115)
    ·
      refine ⟨74015093783282159244141173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49343395855521439496094115 74015093783282159244141173)
      ·
        refine ⟨6938915042182702429138235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 74015093783282159244141173 6938915042182702429138235)
        ·
          refine ⟨10408372563274053643707353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6938915042182702429138235 10408372563274053643707353)
          ·
            refine ⟨7806279422455540232780515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10408372563274053643707353 7806279422455540232780515)
            ·
              refine ⟨11709419133683310349170773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7806279422455540232780515 11709419133683310349170773)
              ·
                refine ⟨137219755472851293154345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11709419133683310349170773 137219755472851293154345)
                ·
                  rfl

theorem cell21_1803833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 8].length) (baseStart_1803833 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1803833 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1803833 prefixEnd_1803833 := by exact prefixLift 1803833
  have htrace : WordTrace (prefixWord ++ tailWord_1803833) baseStart_1803833 baseEnd_1803833 := by
    simpa [prefixWord, tailWord_1803833, baseEnd_1803833] using wordTrace_append hprefix tailTrace_1803833
  have hstable : (prefixWord ++ tailWord_1803833).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803833).length < 2 ^ (prefixWord ++ tailWord_1803833).sum := by decide
  have hdescent : baseEnd_1803833 < baseStart_1803833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803836 : List Nat := [2, 2, 2, 2, 4, 1, 1, 3, 4]
def baseStart_1803836 : Nat := 118140960795 + 1803836 * 2 ^ 59
def prefixEnd_1803836 : Nat := 4983230072969 + 3 ^ 40 * 1803836 * 2
def baseEnd_1803836 : Nat := 411659951059426540913029

theorem tailTrace_1803836 : CollatzResearch.WordTrace tailWord_1803836 prefixEnd_1803836 411659951059426540913029 := by
  unfold tailWord_1803836
  simp only [CollatzResearch.WordTrace]
  refine ⟨32895651946508858753575681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43860869262011811671434241 32895651946508858753575681)
  ·
    refine ⟨24671738959881644065181761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32895651946508858753575681 24671738959881644065181761)
    ·
      refine ⟨18503804219911233048886321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24671738959881644065181761 18503804219911233048886321)
      ·
        refine ⟨13877853164933424786664741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18503804219911233048886321 13877853164933424786664741)
        ·
          refine ⟨2602097468425017147499639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13877853164933424786664741 2602097468425017147499639)
          ·
            refine ⟨3903146202637525721249459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2602097468425017147499639 3903146202637525721249459)
            ·
              refine ⟨5854719303956288581874189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3903146202637525721249459 5854719303956288581874189)
              ·
                refine ⟨2195519738983608218202821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5854719303956288581874189 2195519738983608218202821)
                ·
                  refine ⟨411659951059426540913029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2195519738983608218202821 411659951059426540913029)
                  ·
                    rfl

theorem cell21_1803836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 3, 4].length) (baseStart_1803836 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1803836 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1803836 prefixEnd_1803836 := by exact prefixLift 1803836
  have htrace : WordTrace (prefixWord ++ tailWord_1803836) baseStart_1803836 baseEnd_1803836 := by
    simpa [prefixWord, tailWord_1803836, baseEnd_1803836] using wordTrace_append hprefix tailTrace_1803836
  have hstable : (prefixWord ++ tailWord_1803836).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803836).length < 2 ^ (prefixWord ++ tailWord_1803836).sum := by decide
  have hdescent : baseEnd_1803836 < baseStart_1803836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803940 : List Nat := [2, 3, 1, 2, 2, 2, 1, 3, 5]
def baseStart_1803940 : Nat := 118140960795 + 1803940 * 2 ^ 59
def prefixEnd_1803940 : Nat := 4983230072969 + 3 ^ 40 * 1803940 * 2
def baseEnd_1803940 : Nat := 411683685276345471179483

theorem tailTrace_1803940 : CollatzResearch.WordTrace tailWord_1803940 prefixEnd_1803940 411683685276345471179483 := by
  unfold tailWord_1803940
  simp only [CollatzResearch.WordTrace]
  refine ⟨32897548542320471634468637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43863398056427295512624849 32897548542320471634468637)
  ·
    refine ⟨12336580703370176862925739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32897548542320471634468637 12336580703370176862925739)
    ·
      refine ⟨18504871055055265294388609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12336580703370176862925739 18504871055055265294388609)
      ·
        refine ⟨13878653291291448970791457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18504871055055265294388609 13878653291291448970791457)
        ·
          refine ⟨10408989968468586728093593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13878653291291448970791457 10408989968468586728093593)
          ·
            refine ⟨7806742476351440046070195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10408989968468586728093593 7806742476351440046070195)
            ·
              refine ⟨11710113714527160069105293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7806742476351440046070195 11710113714527160069105293)
              ·
                refine ⟨4391292642947685025914485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11710113714527160069105293 4391292642947685025914485)
                ·
                  refine ⟨411683685276345471179483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4391292642947685025914485 411683685276345471179483)
                  ·
                    rfl

theorem cell21_1803940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 3, 5].length) (baseStart_1803940 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1803940 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1803940 prefixEnd_1803940 := by exact prefixLift 1803940
  have htrace : WordTrace (prefixWord ++ tailWord_1803940) baseStart_1803940 baseEnd_1803940 := by
    simpa [prefixWord, tailWord_1803940, baseEnd_1803940] using wordTrace_append hprefix tailTrace_1803940
  have hstable : (prefixWord ++ tailWord_1803940).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803940).length < 2 ^ (prefixWord ++ tailWord_1803940).sum := by decide
  have hdescent : baseEnd_1803940 < baseStart_1803940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1803985 : List Nat := [1, 2, 2, 1, 2, 6, 7]
def baseStart_1803985 : Nat := 118140960795 + 1803985 * 2 ^ 59
def prefixEnd_1803985 : Nat := 4983230072969 + 3 ^ 40 * 1803985 * 2
def baseEnd_1803985 : Nat := 45743772765492821436599

theorem tailTrace_1803985 : CollatzResearch.WordTrace tailWord_1803985 prefixEnd_1803985 45743772765492821436599 := by
  unfold tailWord_1803985
  simp only [CollatzResearch.WordTrace]
  refine ⟨65796738369477915954325409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43864492246318610636216939 65796738369477915954325409)
  ·
    refine ⟨49347553777108436965744057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65796738369477915954325409 49347553777108436965744057)
    ·
      refine ⟨37010665332831327724308043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49347553777108436965744057 37010665332831327724308043)
      ·
        refine ⟨55515997999246991586462065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37010665332831327724308043 55515997999246991586462065)
        ·
          refine ⟨41636998499435243689846549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55515997999246991586462065 41636998499435243689846549)
          ·
            refine ⟨1951734304661027047961557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 41636998499435243689846549 1951734304661027047961557)
            ·
              refine ⟨45743772765492821436599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1951734304661027047961557 45743772765492821436599)
              ·
                rfl

theorem cell21_1803985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 7].length) (baseStart_1803985 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1803985 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1803985 prefixEnd_1803985 := by exact prefixLift 1803985
  have htrace : WordTrace (prefixWord ++ tailWord_1803985) baseStart_1803985 baseEnd_1803985 := by
    simpa [prefixWord, tailWord_1803985, baseEnd_1803985] using wordTrace_append hprefix tailTrace_1803985
  have hstable : (prefixWord ++ tailWord_1803985).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1803985).length < 2 ^ (prefixWord ++ tailWord_1803985).sum := by decide
  have hdescent : baseEnd_1803985 < baseStart_1803985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1803985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1804106 : List Nat := [3, 1, 2, 1, 1, 1, 5, 1, 6]
def baseStart_1804106 : Nat := 118140960795 + 1804106 * 2 ^ 59
def prefixEnd_1804106 : Nat := 4983230072969 + 3 ^ 40 * 1804106 * 2
def baseEnd_1804106 : Nat := 411721568737966071412477

theorem tailTrace_1804106 : CollatzResearch.WordTrace tailWord_1804106 prefixEnd_1804106 411721568737966071412477 := by
  unfold tailWord_1804106
  simp only [CollatzResearch.WordTrace]
  refine ⟨16450287900509888404870043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43867434401359702412986781 16450287900509888404870043)
  ·
    refine ⟨24675431850764832607305065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16450287900509888404870043 24675431850764832607305065)
    ·
      refine ⟨18506573888073624455478799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24675431850764832607305065 18506573888073624455478799)
      ·
        refine ⟨27759860832110436683218199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18506573888073624455478799 27759860832110436683218199)
        ·
          refine ⟨41639791248165655024827299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27759860832110436683218199 41639791248165655024827299)
          ·
            refine ⟨62459686872248482537240949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41639791248165655024827299 62459686872248482537240949)
            ·
              refine ⟨5855595644273295237866339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62459686872248482537240949 5855595644273295237866339)
              ·
                refine ⟨8783393466409942856799509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5855595644273295237866339 8783393466409942856799509)
                ·
                  refine ⟨411721568737966071412477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8783393466409942856799509 411721568737966071412477)
                  ·
                    rfl

theorem cell21_1804106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 1, 6].length) (baseStart_1804106 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1804106 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1804106 prefixEnd_1804106 := by exact prefixLift 1804106
  have htrace : WordTrace (prefixWord ++ tailWord_1804106) baseStart_1804106 baseEnd_1804106 := by
    simpa [prefixWord, tailWord_1804106, baseEnd_1804106] using wordTrace_append hprefix tailTrace_1804106
  have hstable : (prefixWord ++ tailWord_1804106).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1804106).length < 2 ^ (prefixWord ++ tailWord_1804106).sum := by decide
  have hdescent : baseEnd_1804106 < baseStart_1804106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1804106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1804109 : List Nat := [1, 6, 1, 2, 1, 1, 1, 3, 5]
def baseStart_1804109 : Nat := 118140960795 + 1804109 * 2 ^ 59
def prefixEnd_1804109 : Nat := 4983230072969 + 3 ^ 40 * 1804109 * 2
def baseEnd_1804109 : Nat := 411722253378838732862471

theorem tailTrace_1804109 : CollatzResearch.WordTrace tailWord_1804109 prefixEnd_1804109 411722253378838732862471 := by
  unfold tailWord_1804109
  simp only [CollatzResearch.WordTrace]
  refine ⟨65801261021028685131839381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43867507347352456754559587 65801261021028685131839381)
  ·
    refine ⟨3084434110360719615554971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 65801261021028685131839381 3084434110360719615554971)
    ·
      refine ⟨4626651165541079423332457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3084434110360719615554971 4626651165541079423332457)
      ·
        refine ⟨3469988374155809567499343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4626651165541079423332457 3469988374155809567499343)
        ·
          refine ⟨5204982561233714351249015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3469988374155809567499343 5204982561233714351249015)
          ·
            refine ⟨7807473841850571526873523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5204982561233714351249015 7807473841850571526873523)
            ·
              refine ⟨11711210762775857290310285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7807473841850571526873523 11711210762775857290310285)
              ·
                refine ⟨4391704036040946483866357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11711210762775857290310285 4391704036040946483866357)
                ·
                  refine ⟨411722253378838732862471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4391704036040946483866357 411722253378838732862471)
                  ·
                    rfl

theorem cell21_1804109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_1804109 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1804109 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1804109 prefixEnd_1804109 := by exact prefixLift 1804109
  have htrace : WordTrace (prefixWord ++ tailWord_1804109) baseStart_1804109 baseEnd_1804109 := by
    simpa [prefixWord, tailWord_1804109, baseEnd_1804109] using wordTrace_append hprefix tailTrace_1804109
  have hstable : (prefixWord ++ tailWord_1804109).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1804109).length < 2 ^ (prefixWord ++ tailWord_1804109).sum := by decide
  have hdescent : baseEnd_1804109 < baseStart_1804109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1804109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1804174 : List Nat := [4, 1, 1, 5, 1, 2, 2, 1, 4]
def baseStart_1804174 : Nat := 118140960795 + 1804174 * 2 ^ 59
def prefixEnd_1804174 : Nat := 4983230072969 + 3 ^ 40 * 1804174 * 2
def baseEnd_1804174 : Nat := 411737087264413064279005

theorem tailTrace_1804174 : CollatzResearch.WordTrace tailWord_1804174 prefixEnd_1804174 411737087264413064279005 := by
  unfold tailWord_1804174
  simp only [CollatzResearch.WordTrace]
  refine ⟨8225453970724150154119447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43869087843862134155303717 8225453970724150154119447)
  ·
    refine ⟨12338180956086225231179171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8225453970724150154119447 12338180956086225231179171)
    ·
      refine ⟨18507271434129337846768757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12338180956086225231179171 18507271434129337846768757)
      ·
        refine ⟨1735056696949625423134571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18507271434129337846768757 1735056696949625423134571)
        ·
          refine ⟨2602585045424438134701857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1735056696949625423134571 2602585045424438134701857)
          ·
            refine ⟨1951938784068328601026393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2602585045424438134701857 1951938784068328601026393)
            ·
              refine ⟨1463954088051246450769795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1951938784068328601026393 1463954088051246450769795)
              ·
                refine ⟨2195931132076869676154693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1463954088051246450769795 2195931132076869676154693)
                ·
                  refine ⟨411737087264413064279005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2195931132076869676154693 411737087264413064279005)
                  ·
                    rfl

theorem cell21_1804174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 2, 1, 4].length) (baseStart_1804174 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1804174 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1804174 prefixEnd_1804174 := by exact prefixLift 1804174
  have htrace : WordTrace (prefixWord ++ tailWord_1804174) baseStart_1804174 baseEnd_1804174 := by
    simpa [prefixWord, tailWord_1804174, baseEnd_1804174] using wordTrace_append hprefix tailTrace_1804174
  have hstable : (prefixWord ++ tailWord_1804174).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1804174).length < 2 ^ (prefixWord ++ tailWord_1804174).sum := by decide
  have hdescent : baseEnd_1804174 < baseStart_1804174 := by decide
  rcases family_descends (prefixWord ++ tailWord_1804174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1804244 : List Nat := [2, 4, 1, 2, 1, 1, 3, 2, 5]
def baseStart_1804244 : Nat := 118140960795 + 1804244 * 2 ^ 59
def prefixEnd_1804244 : Nat := 4983230072969 + 3 ^ 40 * 1804244 * 2
def baseEnd_1804244 : Nat := 411753062218108498112195

theorem tailTrace_1804244 : CollatzResearch.WordTrace tailWord_1804244 prefixEnd_1804244 411753062218108498112195 := by
  unfold tailWord_1804244
  simp only [CollatzResearch.WordTrace]
  refine ⟨32903092437769801594001893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43870789917026402125335857 32903092437769801594001893)
  ·
    refine ⟨6169329832081837798875355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32903092437769801594001893 6169329832081837798875355)
    ·
      refine ⟨9253994748122756698313033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6169329832081837798875355 9253994748122756698313033)
      ·
        refine ⟨6940496061092067523734775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9253994748122756698313033 6940496061092067523734775)
        ·
          refine ⟨10410744091638101285602163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6940496061092067523734775 10410744091638101285602163)
          ·
            refine ⟨15616116137457151928403245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10410744091638101285602163 15616116137457151928403245)
            ·
              refine ⟨5856043551546431973151217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15616116137457151928403245 5856043551546431973151217)
              ·
                refine ⟨4392032663659823979863413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5856043551546431973151217 4392032663659823979863413)
                ·
                  refine ⟨411753062218108498112195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4392032663659823979863413 411753062218108498112195)
                  ·
                    rfl

theorem cell21_1804244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_1804244 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1804244 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1804244 prefixEnd_1804244 := by exact prefixLift 1804244
  have htrace : WordTrace (prefixWord ++ tailWord_1804244) baseStart_1804244 baseEnd_1804244 := by
    simpa [prefixWord, tailWord_1804244, baseEnd_1804244] using wordTrace_append hprefix tailTrace_1804244
  have hstable : (prefixWord ++ tailWord_1804244).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1804244).length < 2 ^ (prefixWord ++ tailWord_1804244).sum := by decide
  have hdescent : baseEnd_1804244 < baseStart_1804244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1804244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1804351 : List Nat := [1, 1, 2, 2, 3, 1, 6, 1, 4]
def baseStart_1804351 : Nat := 118140960795 + 1804351 * 2 ^ 59
def prefixEnd_1804351 : Nat := 4983230072969 + 3 ^ 40 * 1804351 * 2
def baseEnd_1804351 : Nat := 411777481075900089828643

theorem tailTrace_1804351 : CollatzResearch.WordTrace tailWord_1804351 prefixEnd_1804351 411777481075900089828643 := by
  unfold tailWord_1804351
  simp only [CollatzResearch.WordTrace]
  refine ⟨65810087486151960462148907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43873391657434640308099271 65810087486151960462148907)
  ·
    refine ⟨98715131229227940693223361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65810087486151960462148907 98715131229227940693223361)
    ·
      refine ⟨74036348421920955519917521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98715131229227940693223361 74036348421920955519917521)
      ·
        refine ⟨55527261316440716639938141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74036348421920955519917521 55527261316440716639938141)
        ·
          refine ⟨20822722993665268739976803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55527261316440716639938141 20822722993665268739976803)
          ·
            refine ⟨31234084490497903109965205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20822722993665268739976803 31234084490497903109965205)
            ·
              refine ⟨1464097710492089208279619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 31234084490497903109965205 1464097710492089208279619)
              ·
                refine ⟨2196146565738133812419429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1464097710492089208279619 2196146565738133812419429)
                ·
                  refine ⟨411777481075900089828643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2196146565738133812419429 411777481075900089828643)
                  ·
                    rfl

theorem cell21_1804351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 6, 1, 4].length) (baseStart_1804351 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1804351 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1804351 prefixEnd_1804351 := by exact prefixLift 1804351
  have htrace : WordTrace (prefixWord ++ tailWord_1804351) baseStart_1804351 baseEnd_1804351 := by
    simpa [prefixWord, tailWord_1804351, baseEnd_1804351] using wordTrace_append hprefix tailTrace_1804351
  have hstable : (prefixWord ++ tailWord_1804351).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1804351).length < 2 ^ (prefixWord ++ tailWord_1804351).sum := by decide
  have hdescent : baseEnd_1804351 < baseStart_1804351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1804351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1804365 : List Nat := [1, 6, 1, 1, 1, 1, 1, 9]
def baseStart_1804365 : Nat := 118140960795 + 1804365 * 2 ^ 59
def prefixEnd_1804365 : Nat := 4983230072969 + 3 ^ 40 * 1804365 * 2
def baseEnd_1804365 : Nat := 137260225355546392198427

theorem tailTrace_1804365 : CollatzResearch.WordTrace tailWord_1804365 prefixEnd_1804365 137260225355546392198427 := by
  unfold tailWord_1804365
  simp only [CollatzResearch.WordTrace]
  refine ⟨65810598108101240853158549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43873732072067493902105699 65810598108101240853158549)
  ·
    refine ⟨3084871786317245664991807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 65810598108101240853158549 3084871786317245664991807)
    ·
      refine ⟨4627307679475868497487711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3084871786317245664991807 4627307679475868497487711)
      ·
        refine ⟨6940961519213802746231567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4627307679475868497487711 6940961519213802746231567)
        ·
          refine ⟨10411442278820704119347351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6940961519213802746231567 10411442278820704119347351)
          ·
            refine ⟨15617163418231056179021027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10411442278820704119347351 15617163418231056179021027)
            ·
              refine ⟨23425745127346584268531541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15617163418231056179021027 23425745127346584268531541)
              ·
                refine ⟨137260225355546392198427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23425745127346584268531541 137260225355546392198427)
                ·
                  rfl

theorem cell21_1804365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 9].length) (baseStart_1804365 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1804365 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1804365 prefixEnd_1804365 := by exact prefixLift 1804365
  have htrace : WordTrace (prefixWord ++ tailWord_1804365) baseStart_1804365 baseEnd_1804365 := by
    simpa [prefixWord, tailWord_1804365, baseEnd_1804365] using wordTrace_append hprefix tailTrace_1804365
  have hstable : (prefixWord ++ tailWord_1804365).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1804365).length < 2 ^ (prefixWord ++ tailWord_1804365).sum := by decide
  have hdescent : baseEnd_1804365 < baseStart_1804365 := by decide
  rcases family_descends (prefixWord ++ tailWord_1804365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1804382 : List Nat := [4, 4, 1, 1, 11]
def baseStart_1804382 : Nat := 118140960795 + 1804382 * 2 ^ 59
def prefixEnd_1804382 : Nat := 4983230072969 + 3 ^ 40 * 1804382 * 2
def baseEnd_1804382 : Nat := 5083759946891986726073

theorem tailTrace_1804382 : CollatzResearch.WordTrace tailWord_1804382 prefixEnd_1804382 5083759946891986726073 := by
  unfold tailWord_1804382
  simp only [CollatzResearch.WordTrace]
  refine ⟨8226402268629956594565925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43874145432693101837684933 8226402268629956594565925)
  ·
    refine ⟨1542450425368116861481111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8226402268629956594565925 1542450425368116861481111)
    ·
      refine ⟨2313675638052175292221667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1542450425368116861481111 2313675638052175292221667)
      ·
        refine ⟨3470513457078262938332501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2313675638052175292221667 3470513457078262938332501)
        ·
          refine ⟨5083759946891986726073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 3470513457078262938332501 5083759946891986726073)
          ·
            rfl

theorem cell21_1804382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 11].length) (baseStart_1804382 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1804382 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1804382 prefixEnd_1804382 := by exact prefixLift 1804382
  have htrace : WordTrace (prefixWord ++ tailWord_1804382) baseStart_1804382 baseEnd_1804382 := by
    simpa [prefixWord, tailWord_1804382, baseEnd_1804382] using wordTrace_append hprefix tailTrace_1804382
  have hstable : (prefixWord ++ tailWord_1804382).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1804382).length < 2 ^ (prefixWord ++ tailWord_1804382).sum := by decide
  have hdescent : baseEnd_1804382 < baseStart_1804382 := by decide
  rcases family_descends (prefixWord ++ tailWord_1804382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1804430 : List Nat := [4, 1, 1, 3, 3, 1, 2, 3, 3]
def baseStart_1804430 : Nat := 118140960795 + 1804430 * 2 ^ 59
def prefixEnd_1804430 : Nat := 4983230072969 + 3 ^ 40 * 1804430 * 2
def baseEnd_1804430 : Nat := 411795509952213508011815

theorem tailTrace_1804430 : CollatzResearch.WordTrace tailWord_1804430 prefixEnd_1804430 411795509952213508011815 := by
  unfold tailWord_1804430
  simp only [CollatzResearch.WordTrace]
  refine ⟨8226621106608219619284343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43875312568577171302849829 8226621106608219619284343)
  ·
    refine ⟨12339931659912329428926515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8226621106608219619284343 12339931659912329428926515)
    ·
      refine ⟨18509897489868494143389773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12339931659912329428926515 18509897489868494143389773)
      ·
        refine ⟨6941211558700685303771165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18509897489868494143389773 6941211558700685303771165)
        ·
          refine ⟨2602954334512756988914187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6941211558700685303771165 2602954334512756988914187)
          ·
            refine ⟨3904431501769135483371281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2602954334512756988914187 3904431501769135483371281)
            ·
              refine ⟨2928323626326851612528461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3904431501769135483371281 2928323626326851612528461)
              ·
                refine ⟨1098121359872569354698173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2928323626326851612528461 1098121359872569354698173)
                ·
                  refine ⟨411795509952213508011815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1098121359872569354698173 411795509952213508011815)
                  ·
                    rfl

theorem cell21_1804430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 3, 3].length) (baseStart_1804430 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1804430 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1804430 prefixEnd_1804430 := by exact prefixLift 1804430
  have htrace : WordTrace (prefixWord ++ tailWord_1804430) baseStart_1804430 baseEnd_1804430 := by
    simpa [prefixWord, tailWord_1804430, baseEnd_1804430] using wordTrace_append hprefix tailTrace_1804430
  have hstable : (prefixWord ++ tailWord_1804430).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1804430).length < 2 ^ (prefixWord ++ tailWord_1804430).sum := by decide
  have hdescent : baseEnd_1804430 < baseStart_1804430 := by decide
  rcases family_descends (prefixWord ++ tailWord_1804430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1804517 : List Nat := [1, 3, 1, 4, 2, 2, 2, 6]
def baseStart_1804517 : Nat := 118140960795 + 1804517 * 2 ^ 59
def prefixEnd_1804517 : Nat := 4983230072969 + 3 ^ 40 * 1804517 * 2
def baseEnd_1804517 : Nat := 137271788179173563353879

theorem tailTrace_1804517 : CollatzResearch.WordTrace tailWord_1804517 prefixEnd_1804517 137271788179173563353879 := by
  unfold tailWord_1804517
  simp only [CollatzResearch.WordTrace]
  refine ⟨65816142003550570812691805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43877428002367047208461203 65816142003550570812691805)
  ·
    refine ⟨24681053251331464054759427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65816142003550570812691805 24681053251331464054759427)
    ·
      refine ⟨37021579876997196082139141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24681053251331464054759427 37021579876997196082139141)
      ·
        refine ⟨6941546226936974265401089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37021579876997196082139141 6941546226936974265401089)
        ·
          refine ⟨5206159670202730699050817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6941546226936974265401089 5206159670202730699050817)
          ·
            refine ⟨3904619752652048024288113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5206159670202730699050817 3904619752652048024288113)
            ·
              refine ⟨2928464814489036018216085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3904619752652048024288113 2928464814489036018216085)
              ·
                refine ⟨137271788179173563353879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2928464814489036018216085 137271788179173563353879)
                ·
                  rfl

theorem cell21_1804517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 6].length) (baseStart_1804517 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1804517 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1804517 prefixEnd_1804517 := by exact prefixLift 1804517
  have htrace : WordTrace (prefixWord ++ tailWord_1804517) baseStart_1804517 baseEnd_1804517 := by
    simpa [prefixWord, tailWord_1804517, baseEnd_1804517] using wordTrace_append hprefix tailTrace_1804517
  have hstable : (prefixWord ++ tailWord_1804517).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1804517).length < 2 ^ (prefixWord ++ tailWord_1804517).sum := by decide
  have hdescent : baseEnd_1804517 < baseStart_1804517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1804517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1804520 : List Nat := [2, 1, 4, 1, 2, 4, 2, 1, 4]
def baseStart_1804520 : Nat := 118140960795 + 1804520 * 2 ^ 59
def prefixEnd_1804520 : Nat := 4983230072969 + 3 ^ 40 * 1804520 * 2
def baseEnd_1804520 : Nat := 411816049178393351511631

theorem tailTrace_1804520 : CollatzResearch.WordTrace tailWord_1804520 prefixEnd_1804520 411816049178393351511631 := by
  unfold tailWord_1804520
  simp only [CollatzResearch.WordTrace]
  refine ⟨32908125711269851162525507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43877500948359801550034009 32908125711269851162525507)
  ·
    refine ⟨49362188566904776743788261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32908125711269851162525507 49362188566904776743788261)
    ·
      refine ⟨9255410356294645639460299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49362188566904776743788261 9255410356294645639460299)
      ·
        refine ⟨13883115534441968459190449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9255410356294645639460299 13883115534441968459190449)
        ·
          refine ⟨10412336650831476344392837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13883115534441968459190449 10412336650831476344392837)
          ·
            refine ⟨1952313122030901814573657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10412336650831476344392837 1952313122030901814573657)
            ·
              refine ⟨1464234841523176360930243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1952313122030901814573657 1464234841523176360930243)
              ·
                refine ⟨2196352262284764541395365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1464234841523176360930243 2196352262284764541395365)
                ·
                  refine ⟨411816049178393351511631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2196352262284764541395365 411816049178393351511631)
                  ·
                    rfl

theorem cell21_1804520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 2, 1, 4].length) (baseStart_1804520 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1804520 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1804520 prefixEnd_1804520 := by exact prefixLift 1804520
  have htrace : WordTrace (prefixWord ++ tailWord_1804520) baseStart_1804520 baseEnd_1804520 := by
    simpa [prefixWord, tailWord_1804520, baseEnd_1804520] using wordTrace_append hprefix tailTrace_1804520
  have hstable : (prefixWord ++ tailWord_1804520).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1804520).length < 2 ^ (prefixWord ++ tailWord_1804520).sum := by decide
  have hdescent : baseEnd_1804520 < baseStart_1804520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1804520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1804565 : List Nat := [1, 3, 2, 1, 2, 1, 6, 2, 3]
def baseStart_1804565 : Nat := 118140960795 + 1804565 * 2 ^ 59
def prefixEnd_1804565 : Nat := 4983230072969 + 3 ^ 40 * 1804565 * 2
def baseEnd_1804565 : Nat := 411826318791483273261539

theorem tailTrace_1804565 : CollatzResearch.WordTrace tailWord_1804565 prefixEnd_1804565 411826318791483273261539 := by
  unfold tailWord_1804565
  simp only [CollatzResearch.WordTrace]
  refine ⟨65817892707376675010439149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43878595138251116673626099 65817892707376675010439149)
  ·
    refine ⟨24681709765266253128914681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65817892707376675010439149 24681709765266253128914681)
    ·
      refine ⟨18511282323949689846686011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24681709765266253128914681 18511282323949689846686011)
      ·
        refine ⟨27766923485924534770029017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18511282323949689846686011 27766923485924534770029017)
        ·
          refine ⟨20825192614443401077521763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27766923485924534770029017 20825192614443401077521763)
          ·
            refine ⟨31237788921665101616282645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20825192614443401077521763 31237788921665101616282645)
            ·
              refine ⟨1464271355703051638263249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 31237788921665101616282645 1464271355703051638263249)
              ·
                refine ⟨1098203516777288728697437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1464271355703051638263249 1098203516777288728697437)
                ·
                  refine ⟨411826318791483273261539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1098203516777288728697437 411826318791483273261539)
                  ·
                    rfl

theorem cell21_1804565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 6, 2, 3].length) (baseStart_1804565 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1804565 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1804565 prefixEnd_1804565 := by exact prefixLift 1804565
  have htrace : WordTrace (prefixWord ++ tailWord_1804565) baseStart_1804565 baseEnd_1804565 := by
    simpa [prefixWord, tailWord_1804565, baseEnd_1804565] using wordTrace_append hprefix tailTrace_1804565
  have hstable : (prefixWord ++ tailWord_1804565).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1804565).length < 2 ^ (prefixWord ++ tailWord_1804565).sum := by decide
  have hdescent : baseEnd_1804565 < baseStart_1804565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1804565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1804624 : List Nat := [2, 1, 1, 1, 1, 6, 2, 4, 3]
def baseStart_1804624 : Nat := 118140960795 + 1804624 * 2 ^ 59
def prefixEnd_1804624 : Nat := 4983230072969 + 3 ^ 40 * 1804624 * 2
def baseEnd_1804624 : Nat := 411839783395312281778085

theorem tailTrace_1804624 : CollatzResearch.WordTrace tailWord_1804624 prefixEnd_1804624 411839783395312281778085 := by
  unfold tailWord_1804624
  simp only [CollatzResearch.WordTrace]
  refine ⟨32910022307081464043418463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43880029742775285391224617 32910022307081464043418463)
  ·
    refine ⟨49365033460622196065127695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32910022307081464043418463 49365033460622196065127695)
    ·
      refine ⟨74047550190933294097691543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49365033460622196065127695 74047550190933294097691543)
      ·
        refine ⟨111071325286399941146537315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74047550190933294097691543 111071325286399941146537315)
        ·
          refine ⟨166606987929599911719805973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111071325286399941146537315 166606987929599911719805973)
          ·
            refine ⟨7809702559199995861865905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 166606987929599911719805973 7809702559199995861865905)
            ·
              refine ⟨5857276919399996896399429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7809702559199995861865905 5857276919399996896399429)
              ·
                refine ⟨1098239422387499418074893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5857276919399996896399429 1098239422387499418074893)
                ·
                  refine ⟨411839783395312281778085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1098239422387499418074893 411839783395312281778085)
                  ·
                    rfl

theorem cell21_1804624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 4, 3].length) (baseStart_1804624 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1804624 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1804624 prefixEnd_1804624 := by exact prefixLift 1804624
  have htrace : WordTrace (prefixWord ++ tailWord_1804624) baseStart_1804624 baseEnd_1804624 := by
    simpa [prefixWord, tailWord_1804624, baseEnd_1804624] using wordTrace_append hprefix tailTrace_1804624
  have hstable : (prefixWord ++ tailWord_1804624).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1804624).length < 2 ^ (prefixWord ++ tailWord_1804624).sum := by decide
  have hdescent : baseEnd_1804624 < baseStart_1804624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1804624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1804683 : List Nat := [1, 1, 1, 1, 4, 4, 3, 1, 5]
def baseStart_1804683 : Nat := 118140960795 + 1804683 * 2 ^ 59
def prefixEnd_1804683 : Nat := 4983230072969 + 3 ^ 40 * 1804683 * 2
def baseEnd_1804683 : Nat := 411853247999141290294631

theorem tailTrace_1804683 : CollatzResearch.WordTrace tailWord_1804683 prefixEnd_1804683 411853247999141290294631 := by
  unfold tailWord_1804683
  simp only [CollatzResearch.WordTrace]
  refine ⟨65822196520949181163234703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43881464347299454108823135 65822196520949181163234703)
  ·
    refine ⟨98733294781423771744852055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65822196520949181163234703 98733294781423771744852055)
    ·
      refine ⟨148099942172135657617278083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98733294781423771744852055 148099942172135657617278083)
      ·
        refine ⟨222149913258203486425917125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148099942172135657617278083 222149913258203486425917125)
        ·
          refine ⟨41653108735913153704859461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 222149913258203486425917125 41653108735913153704859461)
          ·
            refine ⟨7809957887983716319661149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41653108735913153704859461 7809957887983716319661149)
            ·
              refine ⟨2928734207993893619872931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7809957887983716319661149 2928734207993893619872931)
              ·
                refine ⟨4393101311990840429809397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2928734207993893619872931 4393101311990840429809397)
                ·
                  refine ⟨411853247999141290294631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4393101311990840429809397 411853247999141290294631)
                  ·
                    rfl

theorem cell21_1804683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 1, 5].length) (baseStart_1804683 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1804683 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1804683 prefixEnd_1804683 := by exact prefixLift 1804683
  have htrace : WordTrace (prefixWord ++ tailWord_1804683) baseStart_1804683 baseEnd_1804683 := by
    simpa [prefixWord, tailWord_1804683, baseEnd_1804683] using wordTrace_append hprefix tailTrace_1804683
  have hstable : (prefixWord ++ tailWord_1804683).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1804683).length < 2 ^ (prefixWord ++ tailWord_1804683).sum := by decide
  have hdescent : baseEnd_1804683 < baseStart_1804683 := by decide
  rcases family_descends (prefixWord ++ tailWord_1804683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1804776 : List Nat := [2, 1, 4, 1, 1, 3, 1, 5, 3]
def baseStart_1804776 : Nat := 118140960795 + 1804776 * 2 ^ 59
def prefixEnd_1804776 : Nat := 4983230072969 + 3 ^ 40 * 1804776 * 2
def baseEnd_1804776 : Nat := 411874471866193795244441

theorem tailTrace_1804776 : CollatzResearch.WordTrace tailWord_1804776 prefixEnd_1804776 411874471866193795244441 := by
  unfold tailWord_1804776
  simp only [CollatzResearch.WordTrace]
  refine ⟨32912794254806129023185091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43883725673074838697580121 32912794254806129023185091)
  ·
    refine ⟨49369191382209193534777637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32912794254806129023185091 49369191382209193534777637)
    ·
      refine ⟨9256723384164223787770807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49369191382209193534777637 9256723384164223787770807)
      ·
        refine ⟨13885085076246335681656211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9256723384164223787770807 13885085076246335681656211)
        ·
          refine ⟨20827627614369503522484317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13885085076246335681656211 20827627614369503522484317)
          ·
            refine ⟨7810360355388563820931619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20827627614369503522484317 7810360355388563820931619)
            ·
              refine ⟨11715540533082845731397429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7810360355388563820931619 11715540533082845731397429)
              ·
                refine ⟨1098331924976516787318509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11715540533082845731397429 1098331924976516787318509)
                ·
                  refine ⟨411874471866193795244441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1098331924976516787318509 411874471866193795244441)
                  ·
                    rfl

theorem cell21_1804776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 5, 3].length) (baseStart_1804776 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1804776 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1804776 prefixEnd_1804776 := by exact prefixLift 1804776
  have htrace : WordTrace (prefixWord ++ tailWord_1804776) baseStart_1804776 baseEnd_1804776 := by
    simpa [prefixWord, tailWord_1804776, baseEnd_1804776] using wordTrace_append hprefix tailTrace_1804776
  have hstable : (prefixWord ++ tailWord_1804776).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1804776).length < 2 ^ (prefixWord ++ tailWord_1804776).sum := by decide
  have hdescent : baseEnd_1804776 < baseStart_1804776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1804776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1804787 : List Nat := [1, 1, 1, 2, 2, 2, 12]
def baseStart_1804787 : Nat := 118140960795 + 1804787 * 2 ^ 59
def prefixEnd_1804787 : Nat := 4983230072969 + 3 ^ 40 * 1804787 * 2
def baseEnd_1804787 : Nat := 45764109135117802284565

theorem tailTrace_1804787 : CollatzResearch.WordTrace tailWord_1804787 prefixEnd_1804787 45764109135117802284565 := by
  unfold tailWord_1804787
  simp only [CollatzResearch.WordTrace]
  refine ⟨65825989712572406925020615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43883993141714937950013743 65825989712572406925020615)
  ·
    refine ⟨98738984568858610387530923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65825989712572406925020615 98738984568858610387530923)
    ·
      refine ⟨148108476853287915581296385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98738984568858610387530923 148108476853287915581296385)
      ·
        refine ⟨111081357639965936685972289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148108476853287915581296385 111081357639965936685972289)
        ·
          refine ⟨83311018229974452514479217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111081357639965936685972289 83311018229974452514479217)
          ·
            refine ⟨62483263672480839385859413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83311018229974452514479217 62483263672480839385859413)
            ·
              refine ⟨45764109135117802284565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 62483263672480839385859413 45764109135117802284565)
              ·
                rfl

theorem cell21_1804787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 12].length) (baseStart_1804787 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1804787 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1804787 prefixEnd_1804787 := by exact prefixLift 1804787
  have htrace : WordTrace (prefixWord ++ tailWord_1804787) baseStart_1804787 baseEnd_1804787 := by
    simpa [prefixWord, tailWord_1804787, baseEnd_1804787] using wordTrace_append hprefix tailTrace_1804787
  have hstable : (prefixWord ++ tailWord_1804787).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1804787).length < 2 ^ (prefixWord ++ tailWord_1804787).sum := by decide
  have hdescent : baseEnd_1804787 < baseStart_1804787 := by decide
  rcases family_descends (prefixWord ++ tailWord_1804787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1804790 : List Nat := [5, 1, 1, 1, 2, 1, 3, 1, 6]
def baseStart_1804790 : Nat := 118140960795 + 1804790 * 2 ^ 59
def prefixEnd_1804790 : Nat := 4983230072969 + 3 ^ 40 * 1804790 * 2
def baseEnd_1804790 : Nat := 411877666856932882011079

theorem tailTrace_1804790 : CollatzResearch.WordTrace tailWord_1804790 prefixEnd_1804790 411877666856932882011079 := by
  unfold tailWord_1804790
  simp only [CollatzResearch.WordTrace]
  refine ⟨4114131195722596152336239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43884066087707692291586549 4114131195722596152336239)
  ·
    refine ⟨6171196793583894228504359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4114131195722596152336239 6171196793583894228504359)
    ·
      refine ⟨9256795190375841342756539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6171196793583894228504359 9256795190375841342756539)
      ·
        refine ⟨13885192785563762014134809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9256795190375841342756539 13885192785563762014134809)
        ·
          refine ⟨10413894589172821510601107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13885192785563762014134809 10413894589172821510601107)
          ·
            refine ⟨15620841883759232265901661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10413894589172821510601107 15620841883759232265901661)
            ·
              refine ⟨5857815706409712099713123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15620841883759232265901661 5857815706409712099713123)
              ·
                refine ⟨8786723559614568149569685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5857815706409712099713123 8786723559614568149569685)
                ·
                  refine ⟨411877666856932882011079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8786723559614568149569685 411877666856932882011079)
                  ·
                    rfl

theorem cell21_1804790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_1804790 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1804790 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1804790 prefixEnd_1804790 := by exact prefixLift 1804790
  have htrace : WordTrace (prefixWord ++ tailWord_1804790) baseStart_1804790 baseEnd_1804790 := by
    simpa [prefixWord, tailWord_1804790, baseEnd_1804790] using wordTrace_append hprefix tailTrace_1804790
  have hstable : (prefixWord ++ tailWord_1804790).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1804790).length < 2 ^ (prefixWord ++ tailWord_1804790).sum := by decide
  have hdescent : baseEnd_1804790 < baseStart_1804790 := by decide
  rcases family_descends (prefixWord ++ tailWord_1804790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1804849 : List Nat := [1, 2, 2, 3, 1, 1, 4, 1, 6]
def baseStart_1804849 : Nat := 118140960795 + 1804849 * 2 ^ 59
def prefixEnd_1804849 : Nat := 4983230072969 + 3 ^ 40 * 1804849 * 2
def baseEnd_1804849 : Nat := 411891131460761890527625

theorem tailTrace_1804849 : CollatzResearch.WordTrace tailWord_1804849 prefixEnd_1804849 411891131460761890527625 := by
  unfold tailWord_1804849
  simp only [CollatzResearch.WordTrace]
  refine ⟨65828251038347791513777601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43885500692231861009185067 65828251038347791513777601)
  ·
    refine ⟨49371188278760843635333201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65828251038347791513777601 49371188278760843635333201)
    ·
      refine ⟨37028391209070632726499901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49371188278760843635333201 37028391209070632726499901)
      ·
        refine ⟨13885646703401487272437463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37028391209070632726499901 13885646703401487272437463)
        ·
          refine ⟨20828470055102230908656195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13885646703401487272437463 20828470055102230908656195)
          ·
            refine ⟨31242705082653346362984293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20828470055102230908656195 31242705082653346362984293)
            ·
              refine ⟨5858007202997502443059555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31242705082653346362984293 5858007202997502443059555)
              ·
                refine ⟨8787010804496253664589333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5858007202997502443059555 8787010804496253664589333)
                ·
                  refine ⟨411891131460761890527625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8787010804496253664589333 411891131460761890527625)
                  ·
                    rfl

theorem cell21_1804849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 1, 6].length) (baseStart_1804849 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1804849 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1804849 prefixEnd_1804849 := by exact prefixLift 1804849
  have htrace : WordTrace (prefixWord ++ tailWord_1804849) baseStart_1804849 baseEnd_1804849 := by
    simpa [prefixWord, tailWord_1804849, baseEnd_1804849] using wordTrace_append hprefix tailTrace_1804849
  have hstable : (prefixWord ++ tailWord_1804849).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1804849).length < 2 ^ (prefixWord ++ tailWord_1804849).sum := by decide
  have hdescent : baseEnd_1804849 < baseStart_1804849 := by decide
  rcases family_descends (prefixWord ++ tailWord_1804849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1804914 : List Nat := [3, 2, 1, 2, 5, 1, 1, 6]
def baseStart_1804914 : Nat := 118140960795 + 1804914 * 2 ^ 59
def prefixEnd_1804914 : Nat := 4983230072969 + 3 ^ 40 * 1804914 * 2
def baseEnd_1804914 : Nat := 137301988448778740648053

theorem tailTrace_1804914 : CollatzResearch.WordTrace tailWord_1804914 prefixEnd_1804914 137301988448778740648053 := by
  unfold tailWord_1804914
  simp only [CollatzResearch.WordTrace]
  refine ⟨16457655445778076903723449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43887081188741538409929197 16457655445778076903723449)
  ·
    refine ⟨12343241584333557677792587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16457655445778076903723449 12343241584333557677792587)
    ·
      refine ⟨18514862376500336516688881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12343241584333557677792587 18514862376500336516688881)
      ·
        refine ⟨13886146782375252387516661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18514862376500336516688881 13886146782375252387516661)
        ·
          refine ⟨1301826260847679911329687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13886146782375252387516661 1301826260847679911329687)
          ·
            refine ⟨1952739391271519866994531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1301826260847679911329687 1952739391271519866994531)
            ·
              refine ⟨2929109086907279800491797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1952739391271519866994531 2929109086907279800491797)
              ·
                refine ⟨137301988448778740648053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2929109086907279800491797 137301988448778740648053)
                ·
                  rfl

theorem cell21_1804914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 6].length) (baseStart_1804914 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1804914 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1804914 prefixEnd_1804914 := by exact prefixLift 1804914
  have htrace : WordTrace (prefixWord ++ tailWord_1804914) baseStart_1804914 baseEnd_1804914 := by
    simpa [prefixWord, tailWord_1804914, baseEnd_1804914] using wordTrace_append hprefix tailTrace_1804914
  have hstable : (prefixWord ++ tailWord_1804914).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1804914).length < 2 ^ (prefixWord ++ tailWord_1804914).sum := by decide
  have hdescent : baseEnd_1804914 < baseStart_1804914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1804914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1804956 : List Nat := [2, 2, 3, 2, 2, 2, 8]
def baseStart_1804956 : Nat := 118140960795 + 1804956 * 2 ^ 59
def prefixEnd_1804956 : Nat := 4983230072969 + 3 ^ 40 * 1804956 * 2
def baseEnd_1804956 : Nat := 45768394479839275804897

theorem tailTrace_1804956 : CollatzResearch.WordTrace tailWord_1804956 prefixEnd_1804956 45768394479839275804897 := by
  unfold tailWord_1804956
  simp only [CollatzResearch.WordTrace]
  refine ⟨32916076824480074393961361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43888102432640099191948481 32916076824480074393961361)
  ·
    refine ⟨24687057618360055795471021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32916076824480074393961361 24687057618360055795471021)
    ·
      refine ⟨9257646606885020923301633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24687057618360055795471021 9257646606885020923301633)
      ·
        refine ⟨6943234955163765692476225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9257646606885020923301633 6943234955163765692476225)
        ·
          refine ⟨5207426216372824269357169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6943234955163765692476225 5207426216372824269357169)
          ·
            refine ⟨3905569662279618202017877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5207426216372824269357169 3905569662279618202017877)
            ·
              refine ⟨45768394479839275804897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3905569662279618202017877 45768394479839275804897)
              ·
                rfl

theorem cell21_1804956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 8].length) (baseStart_1804956 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1804956 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1804956 prefixEnd_1804956 := by exact prefixLift 1804956
  have htrace : WordTrace (prefixWord ++ tailWord_1804956) baseStart_1804956 baseEnd_1804956 := by
    simpa [prefixWord, tailWord_1804956, baseEnd_1804956] using wordTrace_append hprefix tailTrace_1804956
  have hstable : (prefixWord ++ tailWord_1804956).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1804956).length < 2 ^ (prefixWord ++ tailWord_1804956).sum := by decide
  have hdescent : baseEnd_1804956 < baseStart_1804956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1804956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805015 : List Nat := [1, 1, 3, 2, 1, 4, 9]
def baseStart_1805015 : Nat := 118140960795 + 1805015 * 2 ^ 59
def prefixEnd_1805015 : Nat := 4983230072969 + 3 ^ 40 * 1805015 * 2
def baseEnd_1805015 : Nat := 45769890546931387862291

theorem tailTrace_1805015 : CollatzResearch.WordTrace tailWord_1805015 prefixEnd_1805015 45769890546931387862291 := by
  unfold tailWord_1805015
  simp only [CollatzResearch.WordTrace]
  refine ⟨65834305555746401864320499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43889537037164267909546999 65834305555746401864320499)
  ·
    refine ⟨98751458333619602796480749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65834305555746401864320499 98751458333619602796480749)
    ·
      refine ⟨37031796875107351048680281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98751458333619602796480749 37031796875107351048680281)
      ·
        refine ⟨27773847656330513286510211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37031796875107351048680281 27773847656330513286510211)
        ·
          refine ⟨41660771484495769929765317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27773847656330513286510211 41660771484495769929765317)
          ·
            refine ⟨7811394653342956861830997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41660771484495769929765317 7811394653342956861830997)
            ·
              refine ⟨45769890546931387862291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7811394653342956861830997 45769890546931387862291)
              ·
                rfl

theorem cell21_1805015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 9].length) (baseStart_1805015 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1805015 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1805015 prefixEnd_1805015 := by exact prefixLift 1805015
  have htrace : WordTrace (prefixWord ++ tailWord_1805015) baseStart_1805015 baseEnd_1805015 := by
    simpa [prefixWord, tailWord_1805015, baseEnd_1805015] using wordTrace_append hprefix tailTrace_1805015
  have hstable : (prefixWord ++ tailWord_1805015).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805015).length < 2 ^ (prefixWord ++ tailWord_1805015).sum := by decide
  have hdescent : baseEnd_1805015 < baseStart_1805015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805173 : List Nat := [1, 3, 4, 1, 1, 4, 1, 3, 3]
def baseStart_1805173 : Nat := 118140960795 + 1805173 * 2 ^ 59
def prefixEnd_1805173 : Nat := 4983230072969 + 3 ^ 40 * 1805173 * 2
def baseEnd_1805173 : Nat := 411965072675009327126963

theorem tailTrace_1805173 : CollatzResearch.WordTrace tailWord_1805173 prefixEnd_1805173 411965072675009327126963 := by
  unfold tailWord_1805173
  simp only [CollatzResearch.WordTrace]
  refine ⟨65840068289173994848572173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43893378859449329899048115 65840068289173994848572173)
  ·
    refine ⟨24690025608440248068214565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65840068289173994848572173 24690025608440248068214565)
    ·
      refine ⟨4629379801582546512790231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24690025608440248068214565 4629379801582546512790231)
      ·
        refine ⟨6944069702373819769185347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4629379801582546512790231 6944069702373819769185347)
        ·
          refine ⟨10416104553560729653778021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6944069702373819769185347 10416104553560729653778021)
          ·
            refine ⟨1953019603792636810083379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10416104553560729653778021 1953019603792636810083379)
            ·
              refine ⟨2929529405688955215125069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1953019603792636810083379 2929529405688955215125069)
              ·
                refine ⟨1098573527133358205671901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2929529405688955215125069 1098573527133358205671901)
                ·
                  refine ⟨411965072675009327126963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1098573527133358205671901 411965072675009327126963)
                  ·
                    rfl

theorem cell21_1805173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 3, 3].length) (baseStart_1805173 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1805173 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1805173 prefixEnd_1805173 := by exact prefixLift 1805173
  have htrace : WordTrace (prefixWord ++ tailWord_1805173) baseStart_1805173 baseEnd_1805173 := by
    simpa [prefixWord, tailWord_1805173, baseEnd_1805173] using wordTrace_append hprefix tailTrace_1805173
  have hstable : (prefixWord ++ tailWord_1805173).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805173).length < 2 ^ (prefixWord ++ tailWord_1805173).sum := by decide
  have hdescent : baseEnd_1805173 < baseStart_1805173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805246 : List Nat := [4, 2, 1, 1, 1, 2, 4, 2, 4]
def baseStart_1805246 : Nat := 118140960795 + 1805246 * 2 ^ 59
def prefixEnd_1805246 : Nat := 4983230072969 + 3 ^ 40 * 1805246 * 2
def baseEnd_1805246 : Nat := 411981732269577422410147

theorem tailTrace_1805246 : CollatzResearch.WordTrace tailWord_1805246 prefixEnd_1805246 411981732269577422410147 := by
  unfold tailWord_1805246
  simp only [CollatzResearch.WordTrace]
  refine ⟨8230341352238691039497449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43895153878606352210653061 8230341352238691039497449)
  ·
    refine ⟨6172756014179018279623087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8230341352238691039497449 6172756014179018279623087)
    ·
      refine ⟨9259134021268527419434631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6172756014179018279623087 9259134021268527419434631)
      ·
        refine ⟨13888701031902791129151947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9259134021268527419434631 13888701031902791129151947)
        ·
          refine ⟨20833051547854186693727921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13888701031902791129151947 20833051547854186693727921)
          ·
            refine ⟨15624788660890640020295941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20833051547854186693727921 15624788660890640020295941)
            ·
              refine ⟨2929647873916995003805489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15624788660890640020295941 2929647873916995003805489)
              ·
                refine ⟨2197235905437746252854117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2929647873916995003805489 2197235905437746252854117)
                ·
                  refine ⟨411981732269577422410147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2197235905437746252854117 411981732269577422410147)
                  ·
                    rfl

theorem cell21_1805246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 2, 4].length) (baseStart_1805246 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1805246 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1805246 prefixEnd_1805246 := by exact prefixLift 1805246
  have htrace : WordTrace (prefixWord ++ tailWord_1805246) baseStart_1805246 baseEnd_1805246 := by
    simpa [prefixWord, tailWord_1805246, baseEnd_1805246] using wordTrace_append hprefix tailTrace_1805246
  have hstable : (prefixWord ++ tailWord_1805246).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805246).length < 2 ^ (prefixWord ++ tailWord_1805246).sum := by decide
  have hdescent : baseEnd_1805246 < baseStart_1805246 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805274 : List Nat := [3, 1, 1, 2, 4, 1, 1, 1, 7]
def baseStart_1805274 : Nat := 118140960795 + 1805274 * 2 ^ 59
def prefixEnd_1805274 : Nat := 4983230072969 + 3 ^ 40 * 1805274 * 2
def baseEnd_1805274 : Nat := 411988122251055595943423

theorem tailTrace_1805274 : CollatzResearch.WordTrace tailWord_1805274 prefixEnd_1805274 411988122251055595943423 := by
  unfold tailWord_1805274
  simp only [CollatzResearch.WordTrace]
  refine ⟨16460938015452022274499719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43895834707872059398665917 16460938015452022274499719)
  ·
    refine ⟨24691407023178033411749579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16460938015452022274499719 24691407023178033411749579)
    ·
      refine ⟨37037110534767050117624369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24691407023178033411749579 37037110534767050117624369)
      ·
        refine ⟨27777832901075287588218277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37037110534767050117624369 27777832901075287588218277)
        ·
          refine ⟨5208343668951616422790927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27777832901075287588218277 5208343668951616422790927)
          ·
            refine ⟨7812515503427424634186391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5208343668951616422790927 7812515503427424634186391)
            ·
              refine ⟨11718773255141136951279587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7812515503427424634186391 11718773255141136951279587)
              ·
                refine ⟨17578159882711705426919381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11718773255141136951279587 17578159882711705426919381)
                ·
                  refine ⟨411988122251055595943423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17578159882711705426919381 411988122251055595943423)
                  ·
                    rfl

theorem cell21_1805274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 1, 7].length) (baseStart_1805274 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1805274 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1805274 prefixEnd_1805274 := by exact prefixLift 1805274
  have htrace : WordTrace (prefixWord ++ tailWord_1805274) baseStart_1805274 baseEnd_1805274 := by
    simpa [prefixWord, tailWord_1805274, baseEnd_1805274] using wordTrace_append hprefix tailTrace_1805274
  have hstable : (prefixWord ++ tailWord_1805274).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805274).length < 2 ^ (prefixWord ++ tailWord_1805274).sum := by decide
  have hdescent : baseEnd_1805274 < baseStart_1805274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805277 : List Nat := [1, 4, 3, 1, 2, 2, 3, 5]
def baseStart_1805277 : Nat := 118140960795 + 1805277 * 2 ^ 59
def prefixEnd_1805277 : Nat := 4983230072969 + 3 ^ 40 * 1805277 * 2
def baseEnd_1805277 : Nat := 137329602297309419131139

theorem tailTrace_1805277 : CollatzResearch.WordTrace tailWord_1805277 prefixEnd_1805277 137329602297309419131139 := by
  unfold tailWord_1805277
  simp only [CollatzResearch.WordTrace]
  refine ⟨65843861480797220610358085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43895907653864813740238723 65843861480797220610358085)
  ·
    refine ⟨12345724027649478864442141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65843861480797220610358085 12345724027649478864442141)
    ·
      refine ⟨4629646510368554574165803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12345724027649478864442141 4629646510368554574165803)
      ·
        refine ⟨6944469765552831861248705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4629646510368554574165803 6944469765552831861248705)
        ·
          refine ⟨5208352324164623895936529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6944469765552831861248705 5208352324164623895936529)
          ·
            refine ⟨3906264243123467921952397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5208352324164623895936529 3906264243123467921952397)
            ·
              refine ⟨1464849091171300470732149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3906264243123467921952397 1464849091171300470732149)
              ·
                refine ⟨137329602297309419131139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1464849091171300470732149 137329602297309419131139)
                ·
                  rfl

theorem cell21_1805277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 3, 5].length) (baseStart_1805277 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1805277 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1805277 prefixEnd_1805277 := by exact prefixLift 1805277
  have htrace : WordTrace (prefixWord ++ tailWord_1805277) baseStart_1805277 baseEnd_1805277 := by
    simpa [prefixWord, tailWord_1805277, baseEnd_1805277] using wordTrace_append hprefix tailTrace_1805277
  have hstable : (prefixWord ++ tailWord_1805277).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805277).length < 2 ^ (prefixWord ++ tailWord_1805277).sum := by decide
  have hdescent : baseEnd_1805277 < baseStart_1805277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805319 : List Nat := [1, 1, 4, 3, 1, 1, 2, 8]
def baseStart_1805319 : Nat := 118140960795 + 1805319 * 2 ^ 59
def prefixEnd_1805319 : Nat := 4983230072969 + 3 ^ 40 * 1805319 * 2
def baseEnd_1805319 : Nat := 137332797288048505897777

theorem tailTrace_1805319 : CollatzResearch.WordTrace tailWord_1805319 prefixEnd_1805319 137332797288048505897777 := by
  unfold tailWord_1805319
  simp only [CollatzResearch.WordTrace]
  refine ⟨65845393346645061783387011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43896928897763374522258007 65845393346645061783387011)
  ·
    refine ⟨98768090019967592675080517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65845393346645061783387011 98768090019967592675080517)
    ·
      refine ⟨18519016878743923626577597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98768090019967592675080517 18519016878743923626577597)
      ·
        refine ⟨6944631329528971359966599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18519016878743923626577597 6944631329528971359966599)
        ·
          refine ⟨10416946994293457039949899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6944631329528971359966599 10416946994293457039949899)
          ·
            refine ⟨15625420491440185559924849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10416946994293457039949899 15625420491440185559924849)
            ·
              refine ⟨11719065368580139169943637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15625420491440185559924849 11719065368580139169943637)
              ·
                refine ⟨137332797288048505897777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11719065368580139169943637 137332797288048505897777)
                ·
                  rfl

theorem cell21_1805319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 8].length) (baseStart_1805319 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1805319 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1805319 prefixEnd_1805319 := by exact prefixLift 1805319
  have htrace : WordTrace (prefixWord ++ tailWord_1805319) baseStart_1805319 baseEnd_1805319 := by
    simpa [prefixWord, tailWord_1805319, baseEnd_1805319] using wordTrace_append hprefix tailTrace_1805319
  have hstable : (prefixWord ++ tailWord_1805319).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805319).length < 2 ^ (prefixWord ++ tailWord_1805319).sum := by decide
  have hdescent : baseEnd_1805319 < baseStart_1805319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805336 : List Nat := [2, 1, 2, 3, 2, 2, 4, 5]
def baseStart_1805336 : Nat := 118140960795 + 1805336 * 2 ^ 59
def prefixEnd_1805336 : Nat := 4983230072969 + 3 ^ 40 * 1805336 * 2
def baseEnd_1805336 : Nat := 137334090498585755303321

theorem tailTrace_1805336 : CollatzResearch.WordTrace tailWord_1805336 prefixEnd_1805336 137334090498585755303321 := by
  unfold tailWord_1805336
  simp only [CollatzResearch.WordTrace]
  refine ⟨32923006693791736843377931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43897342258388982457837241 32923006693791736843377931)
  ·
    refine ⟨49384510040687605265066897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32923006693791736843377931 49384510040687605265066897)
    ·
      refine ⟨37038382530515703948800173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49384510040687605265066897 37038382530515703948800173)
      ·
        refine ⟨13889393448943388980800065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37038382530515703948800173 13889393448943388980800065)
        ·
          refine ⟨10417045086707541735600049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13889393448943388980800065 10417045086707541735600049)
          ·
            refine ⟨7812783815030656301700037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10417045086707541735600049 7812783815030656301700037)
            ·
              refine ⟨1464896965318248056568757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7812783815030656301700037 1464896965318248056568757)
              ·
                refine ⟨137334090498585755303321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1464896965318248056568757 137334090498585755303321)
                ·
                  rfl

theorem cell21_1805336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 4, 5].length) (baseStart_1805336 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1805336 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1805336 prefixEnd_1805336 := by exact prefixLift 1805336
  have htrace : WordTrace (prefixWord ++ tailWord_1805336) baseStart_1805336 baseEnd_1805336 := by
    simpa [prefixWord, tailWord_1805336, baseEnd_1805336] using wordTrace_append hprefix tailTrace_1805336
  have hstable : (prefixWord ++ tailWord_1805336).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805336).length < 2 ^ (prefixWord ++ tailWord_1805336).sum := by decide
  have hdescent : baseEnd_1805336 < baseStart_1805336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805426 : List Nat := [3, 2, 1, 2, 2, 1, 2, 3, 5]
def baseStart_1805426 : Nat := 118140960795 + 1805426 * 2 ^ 59
def prefixEnd_1805426 : Nat := 4983230072969 + 3 ^ 40 * 1805426 * 2
def baseEnd_1805426 : Nat := 412022810721937109409779

theorem tailTrace_1805426 : CollatzResearch.WordTrace tailWord_1805426 prefixEnd_1805426 412022810721937109409779 := by
  unfold tailWord_1805426
  simp only [CollatzResearch.WordTrace]
  refine ⟨16462323989314354764383033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43899530638171612705021421 16462323989314354764383033)
  ·
    refine ⟨12346742991985766073287275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16462323989314354764383033 12346742991985766073287275)
    ·
      refine ⟨18520114487978649109930913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12346742991985766073287275 18520114487978649109930913)
      ·
        refine ⟨13890085865983986832448185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18520114487978649109930913 13890085865983986832448185)
        ·
          refine ⟨10417564399487990124336139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13890085865983986832448185 10417564399487990124336139)
          ·
            refine ⟨15626346599231985186504209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10417564399487990124336139 15626346599231985186504209)
            ·
              refine ⟨11719759949423988889878157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15626346599231985186504209 11719759949423988889878157)
              ·
                refine ⟨4394909981033995833704309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11719759949423988889878157 4394909981033995833704309)
                ·
                  refine ⟨412022810721937109409779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4394909981033995833704309 412022810721937109409779)
                  ·
                    rfl

theorem cell21_1805426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 3, 5].length) (baseStart_1805426 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1805426 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1805426 prefixEnd_1805426 := by exact prefixLift 1805426
  have htrace : WordTrace (prefixWord ++ tailWord_1805426) baseStart_1805426 baseEnd_1805426 := by
    simpa [prefixWord, tailWord_1805426, baseEnd_1805426] using wordTrace_append hprefix tailTrace_1805426
  have hstable : (prefixWord ++ tailWord_1805426).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805426).length < 2 ^ (prefixWord ++ tailWord_1805426).sum := by decide
  have hdescent : baseEnd_1805426 < baseStart_1805426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805474 : List Nat := [3, 3, 1, 3, 2, 1, 1, 1, 6]
def baseStart_1805474 : Nat := 118140960795 + 1805474 * 2 ^ 59
def prefixEnd_1805474 : Nat := 4983230072969 + 3 ^ 40 * 1805474 * 2
def baseEnd_1805474 : Nat := 412033764975899692609681

theorem tailTrace_1805474 : CollatzResearch.WordTrace tailWord_1805474 prefixEnd_1805474 412033764975899692609681 := by
  unfold tailWord_1805474
  simp only [CollatzResearch.WordTrace]
  refine ⟨16462761665270880813819869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43900697774055682170186317 16462761665270880813819869)
  ·
    refine ⟨6173535624476580305182451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16462761665270880813819869 6173535624476580305182451)
    ·
      refine ⟨9260303436714870457773677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6173535624476580305182451 9260303436714870457773677)
      ·
        refine ⟨3472613788768076421665129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9260303436714870457773677 3472613788768076421665129)
        ·
          refine ⟨2604460341576057316248847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3472613788768076421665129 2604460341576057316248847)
          ·
            refine ⟨3906690512364085974373271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2604460341576057316248847 3906690512364085974373271)
            ·
              refine ⟨5860035768546128961559907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3906690512364085974373271 5860035768546128961559907)
              ·
                refine ⟨8790053652819193442339861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5860035768546128961559907 8790053652819193442339861)
                ·
                  refine ⟨412033764975899692609681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8790053652819193442339861 412033764975899692609681)
                  ·
                    rfl

theorem cell21_1805474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 1, 6].length) (baseStart_1805474 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1805474 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1805474 prefixEnd_1805474 := by exact prefixLift 1805474
  have htrace : WordTrace (prefixWord ++ tailWord_1805474) baseStart_1805474 baseEnd_1805474 := by
    simpa [prefixWord, tailWord_1805474, baseEnd_1805474] using wordTrace_append hprefix tailTrace_1805474
  have hstable : (prefixWord ++ tailWord_1805474).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805474).length < 2 ^ (prefixWord ++ tailWord_1805474).sum := by decide
  have hdescent : baseEnd_1805474 < baseStart_1805474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805505 : List Nat := [1, 2, 6, 1, 1, 1, 4, 5]
def baseStart_1805505 : Nat := 118140960795 + 1805505 * 2 ^ 59
def prefixEnd_1805505 : Nat := 4983230072969 + 3 ^ 40 * 1805505 * 2
def baseEnd_1805505 : Nat := 137346946532750175864317

theorem tailTrace_1805505 : CollatzResearch.WordTrace tailWord_1805505 prefixEnd_1805505 137346946532750175864317 := by
  unfold tailWord_1805505
  simp only [CollatzResearch.WordTrace]
  refine ⟨65852177323971215549657969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43901451549314143699771979 65852177323971215549657969)
  ·
    refine ⟨49389132992978411662243477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65852177323971215549657969 49389132992978411662243477)
    ·
      refine ⟨2315115609045863046667663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 49389132992978411662243477 2315115609045863046667663)
      ·
        refine ⟨3472673413568794570001495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2315115609045863046667663 3472673413568794570001495)
        ·
          refine ⟨5209010120353191855002243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3472673413568794570001495 5209010120353191855002243)
          ·
            refine ⟨7813515180529787782503365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5209010120353191855002243 7813515180529787782503365)
            ·
              refine ⟨1465034096349335209219381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7813515180529787782503365 1465034096349335209219381)
              ·
                refine ⟨137346946532750175864317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1465034096349335209219381 137346946532750175864317)
                ·
                  rfl

theorem cell21_1805505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 4, 5].length) (baseStart_1805505 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1805505 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1805505 prefixEnd_1805505 := by exact prefixLift 1805505
  have htrace : WordTrace (prefixWord ++ tailWord_1805505) baseStart_1805505 baseEnd_1805505 := by
    simpa [prefixWord, tailWord_1805505, baseEnd_1805505] using wordTrace_append hprefix tailTrace_1805505
  have hstable : (prefixWord ++ tailWord_1805505).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805505).length < 2 ^ (prefixWord ++ tailWord_1805505).sum := by decide
  have hdescent : baseEnd_1805505 < baseStart_1805505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805536 : List Nat := [2, 1, 1, 3, 1, 5, 3, 2, 3]
def baseStart_1805536 : Nat := 118140960795 + 1805536 * 2 ^ 59
def prefixEnd_1805536 : Nat := 4983230072969 + 3 ^ 40 * 1805536 * 2
def baseEnd_1805536 : Nat := 412047914220601362576221

theorem tailTrace_1805536 : CollatzResearch.WordTrace tailWord_1805536 prefixEnd_1805536 412047914220601362576221 := by
  unfold tailWord_1805536
  simp only [CollatzResearch.WordTrace]
  refine ⟨32926653993429453922018231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43902205324572605229357641 32926653993429453922018231)
  ·
    refine ⟨49389980990144180883027347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32926653993429453922018231 49389980990144180883027347)
    ·
      refine ⟨74084971485216271324541021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49389980990144180883027347 74084971485216271324541021)
      ·
        refine ⟨27781864306956101746702883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74084971485216271324541021 27781864306956101746702883)
        ·
          refine ⟨41672796460434152620054325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27781864306956101746702883 41672796460434152620054325)
          ·
            refine ⟨3906824668165701808130093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41672796460434152620054325 3906824668165701808130093)
            ·
              refine ⟨1465059250562138178048785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3906824668165701808130093 1465059250562138178048785)
              ·
                refine ⟨1098794437921603633536589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1465059250562138178048785 1098794437921603633536589)
                ·
                  refine ⟨412047914220601362576221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1098794437921603633536589 412047914220601362576221)
                  ·
                    rfl

theorem cell21_1805536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 3, 2, 3].length) (baseStart_1805536 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1805536 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1805536 prefixEnd_1805536 := by exact prefixLift 1805536
  have htrace : WordTrace (prefixWord ++ tailWord_1805536) baseStart_1805536 baseEnd_1805536 := by
    simpa [prefixWord, tailWord_1805536, baseEnd_1805536] using wordTrace_append hprefix tailTrace_1805536
  have hstable : (prefixWord ++ tailWord_1805536).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805536).length < 2 ^ (prefixWord ++ tailWord_1805536).sum := by decide
  have hdescent : baseEnd_1805536 < baseStart_1805536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805547 : List Nat := [1, 1, 1, 1, 2, 7, 2, 6]
def baseStart_1805547 : Nat := 118140960795 + 1805547 * 2 ^ 59
def prefixEnd_1805547 : Nat := 4983230072969 + 3 ^ 40 * 1805547 * 2
def baseEnd_1805547 : Nat := 137350141523489262630955

theorem tailTrace_1805547 : CollatzResearch.WordTrace tailWord_1805547 prefixEnd_1805547 137350141523489262630955 := by
  unfold tailWord_1805547
  simp only [CollatzResearch.WordTrace]
  refine ⟨65853709189819056722686895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43902472793212704481791263 65853709189819056722686895)
  ·
    refine ⟨98780563784728585084030343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65853709189819056722686895 98780563784728585084030343)
    ·
      refine ⟨148170845677092877626045515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98780563784728585084030343 148170845677092877626045515)
      ·
        refine ⟨222256268515639316439068273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148170845677092877626045515 222256268515639316439068273)
        ·
          refine ⟨166692201386729487329301205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222256268515639316439068273 166692201386729487329301205)
          ·
            refine ⟨3906848470001472359280497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 166692201386729487329301205 3906848470001472359280497)
            ·
              refine ⟨2930136352501104269460373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3906848470001472359280497 2930136352501104269460373)
              ·
                refine ⟨137350141523489262630955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2930136352501104269460373 137350141523489262630955)
                ·
                  rfl

theorem cell21_1805547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 6].length) (baseStart_1805547 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1805547 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1805547 prefixEnd_1805547 := by exact prefixLift 1805547
  have htrace : WordTrace (prefixWord ++ tailWord_1805547) baseStart_1805547 baseEnd_1805547 := by
    simpa [prefixWord, tailWord_1805547, baseEnd_1805547] using wordTrace_append hprefix tailTrace_1805547
  have hstable : (prefixWord ++ tailWord_1805547).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805547).length < 2 ^ (prefixWord ++ tailWord_1805547).sum := by decide
  have hdescent : baseEnd_1805547 < baseStart_1805547 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1805550 : List Nat := [4, 1, 2, 1, 1, 1, 6, 1, 4]
def baseStart_1805550 : Nat := 118140960795 + 1805550 * 2 ^ 59
def prefixEnd_1805550 : Nat := 4983230072969 + 3 ^ 40 * 1805550 * 2
def baseEnd_1805550 : Nat := 412051109211340449342859

theorem tailTrace_1805550 : CollatzResearch.WordTrace tailWord_1805550 prefixEnd_1805550 412051109211340449342859 := by
  unfold tailWord_1805550
  simp only [CollatzResearch.WordTrace]
  refine ⟨8231727326101023529380763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43902545739205458823364069 8231727326101023529380763)
  ·
    refine ⟨12347590989151535294071145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8231727326101023529380763 12347590989151535294071145)
    ·
      refine ⟨9260693241863651470553359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12347590989151535294071145 9260693241863651470553359)
      ·
        refine ⟨13891039862795477205830039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9260693241863651470553359 13891039862795477205830039)
        ·
          refine ⟨20836559794193215808745059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13891039862795477205830039 20836559794193215808745059)
          ·
            refine ⟨31254839691289823713117589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20836559794193215808745059 31254839691289823713117589)
            ·
              refine ⟨1465070610529210486552387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 31254839691289823713117589 1465070610529210486552387)
              ·
                refine ⟨2197605915793815729828581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1465070610529210486552387 2197605915793815729828581)
                ·
                  refine ⟨412051109211340449342859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2197605915793815729828581 412051109211340449342859)
                  ·
                    rfl

theorem cell21_1805550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 6, 1, 4].length) (baseStart_1805550 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1805550 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1805550 prefixEnd_1805550 := by exact prefixLift 1805550
  have htrace : WordTrace (prefixWord ++ tailWord_1805550) baseStart_1805550 baseEnd_1805550 := by
    simpa [prefixWord, tailWord_1805550, baseEnd_1805550] using wordTrace_append hprefix tailTrace_1805550
  have hstable : (prefixWord ++ tailWord_1805550).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1805550).length < 2 ^ (prefixWord ++ tailWord_1805550).sum := by decide
  have hdescent : baseEnd_1805550 < baseStart_1805550 := by decide
  rcases family_descends (prefixWord ++ tailWord_1805550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
