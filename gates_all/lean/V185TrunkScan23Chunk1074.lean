import V185TrunkScan23Chunk1073

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6358503 : List Nat := [1, 1, 5, 2, 1, 3, 1, 2, 2, 1, 4]
def baseStart_6358503 : Nat := 118140960795 + 6358503 * 2 ^ 59
def prefixEnd_6358503 : Nat := 4983230072969 + 3 ^ 40 * 6358503 * 2
def baseEnd_6358503 : Nat := 3264968282055441061470283

theorem tailTrace_6358503 : CollatzResearch.WordTrace tailWord_6358503 prefixEnd_6358503 3264968282055441061470283 := by
  unfold tailWord_6358503
  simp only [CollatzResearch.WordTrace]
  refine ⟨231913656883237051700944163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154609104588824701133962775 231913656883237051700944163)
  ·
    refine ⟨347870485324855577551416245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231913656883237051700944163 347870485324855577551416245)
    ·
      refine ⟨32612857999205210395445273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 347870485324855577551416245 32612857999205210395445273)
      ·
        refine ⟨24459643499403907796583955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32612857999205210395445273 24459643499403907796583955)
        ·
          refine ⟨36689465249105861694875933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24459643499403907796583955 36689465249105861694875933)
          ·
            refine ⟨13758549468414698135578475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36689465249105861694875933 13758549468414698135578475)
            ·
              refine ⟨20637824202622047203367713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13758549468414698135578475 20637824202622047203367713)
              ·
                refine ⟨15478368151966535402525785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20637824202622047203367713 15478368151966535402525785)
                ·
                  refine ⟨11608776113974901551894339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15478368151966535402525785 11608776113974901551894339)
                  ·
                    refine ⟨17413164170962352327841509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11608776113974901551894339 17413164170962352327841509)
                    ·
                      refine ⟨3264968282055441061470283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17413164170962352327841509 3264968282055441061470283)
                      ·
                        rfl

theorem cell23_6358503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_6358503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6358503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6358503 prefixEnd_6358503 := by exact prefixLift 6358503
  have htrace : WordTrace (prefixWord ++ tailWord_6358503) baseStart_6358503 baseEnd_6358503 := by
    simpa [prefixWord, tailWord_6358503, baseEnd_6358503] using wordTrace_append hprefix tailTrace_6358503
  have hstable : (prefixWord ++ tailWord_6358503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6358503).length < 2 ^ (prefixWord ++ tailWord_6358503).sum := by decide
  have hdescent : baseEnd_6358503 < baseStart_6358503 := by decide
  rcases family_descends (prefixWord ++ tailWord_6358503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6358513 : List Nat := [1, 2, 2, 2, 3, 2, 3, 1, 3, 4]
def baseStart_6358513 : Nat := 118140960795 + 6358513 * 2 ^ 59
def prefixEnd_6358513 : Nat := 4983230072969 + 3 ^ 40 * 6358513 * 2
def baseEnd_6358513 : Nat := 1088324472287328674115079

theorem tailTrace_6358513 : CollatzResearch.WordTrace tailWord_6358513 prefixEnd_6358513 1088324472287328674115079 := by
  unfold tailWord_6358513
  simp only [CollatzResearch.WordTrace]
  refine ⟨231914021613200823408808193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154609347742133882272538795 231914021613200823408808193)
  ·
    refine ⟨173935516209900617556606145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231914021613200823408808193 173935516209900617556606145)
    ·
      refine ⟨130451637157425463167454609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173935516209900617556606145 130451637157425463167454609)
      ·
        refine ⟨97838727868069097375590957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130451637157425463167454609 97838727868069097375590957)
        ·
          refine ⟨36689522950525911515846609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97838727868069097375590957 36689522950525911515846609)
          ·
            refine ⟨27517142212894433636884957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36689522950525911515846609 27517142212894433636884957)
            ·
              refine ⟨10318928329835412613831859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27517142212894433636884957 10318928329835412613831859)
              ·
                refine ⟨15478392494753118920747789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10318928329835412613831859 15478392494753118920747789)
                ·
                  refine ⟨5804397185532419595280421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15478392494753118920747789 5804397185532419595280421)
                  ·
                    refine ⟨1088324472287328674115079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5804397185532419595280421 1088324472287328674115079)
                    ·
                      rfl

theorem cell23_6358513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 1, 3, 4].length) (baseStart_6358513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6358513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6358513 prefixEnd_6358513 := by exact prefixLift 6358513
  have htrace : WordTrace (prefixWord ++ tailWord_6358513) baseStart_6358513 baseEnd_6358513 := by
    simpa [prefixWord, tailWord_6358513, baseEnd_6358513] using wordTrace_append hprefix tailTrace_6358513
  have hstable : (prefixWord ++ tailWord_6358513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6358513).length < 2 ^ (prefixWord ++ tailWord_6358513).sum := by decide
  have hdescent : baseEnd_6358513 < baseStart_6358513 := by decide
  rcases family_descends (prefixWord ++ tailWord_6358513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6358534 : List Nat := [6, 2, 1, 1, 2, 1, 2, 1, 2, 5]
def baseStart_6358534 : Nat := 118140960795 + 6358534 * 2 ^ 59
def prefixEnd_6358534 : Nat := 4983230072969 + 3 ^ 40 * 6358534 * 2
def baseEnd_6358534 : Nat := 1088328066651910146727547

theorem tailTrace_6358534 : CollatzResearch.WordTrace tailWord_6358534 prefixEnd_6358534 1088328066651910146727547 := by
  unfold tailWord_6358534
  simp only [CollatzResearch.WordTrace]
  refine ⟨7247337110816398249853833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 154609858364083162663548437 7247337110816398249853833)
  ·
    refine ⟨5435502833112298687390375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7247337110816398249853833 5435502833112298687390375)
    ·
      refine ⟨8153254249668448031085563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5435502833112298687390375 8153254249668448031085563)
      ·
        refine ⟨12229881374502672046628345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8153254249668448031085563 12229881374502672046628345)
        ·
          refine ⟨9172411030877004034971259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12229881374502672046628345 9172411030877004034971259)
          ·
            refine ⟨13758616546315506052456889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9172411030877004034971259 13758616546315506052456889)
            ·
              refine ⟨10318962409736629539342667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13758616546315506052456889 10318962409736629539342667)
              ·
                refine ⟨15478443614604944309014001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10318962409736629539342667 15478443614604944309014001)
                ·
                  refine ⟨11608832710953708231760501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15478443614604944309014001 11608832710953708231760501)
                  ·
                    refine ⟨1088328066651910146727547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11608832710953708231760501 1088328066651910146727547)
                    ·
                      rfl

theorem cell23_6358534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_6358534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6358534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6358534 prefixEnd_6358534 := by exact prefixLift 6358534
  have htrace : WordTrace (prefixWord ++ tailWord_6358534) baseStart_6358534 baseEnd_6358534 := by
    simpa [prefixWord, tailWord_6358534, baseEnd_6358534] using wordTrace_append hprefix tailTrace_6358534
  have hstable : (prefixWord ++ tailWord_6358534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6358534).length < 2 ^ (prefixWord ++ tailWord_6358534).sum := by decide
  have hdescent : baseEnd_6358534 < baseStart_6358534 := by decide
  rcases family_descends (prefixWord ++ tailWord_6358534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6358536 : List Nat := [2, 1, 3, 2, 1, 1, 2, 1, 2, 5, 3]
def baseStart_6358536 : Nat := 118140960795 + 6358536 * 2 ^ 59
def prefixEnd_6358536 : Nat := 4983230072969 + 3 ^ 40 * 6358536 * 2
def baseEnd_6358536 : Nat := 3264985226917039432357631

theorem tailTrace_6358536 : CollatzResearch.WordTrace tailWord_6358536 prefixEnd_6358536 3264985226917039432357631 := by
  unfold tailWord_6358536
  simp only [CollatzResearch.WordTrace]
  refine ⟨115957430246058749168447731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154609906994744998891263641 115957430246058749168447731)
  ·
    refine ⟨173936145369088123752671597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115957430246058749168447731 173936145369088123752671597)
    ·
      refine ⟨65226054513408046407251849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173936145369088123752671597 65226054513408046407251849)
      ·
        refine ⟨48919540885056034805438887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65226054513408046407251849 48919540885056034805438887)
        ·
          refine ⟨73379311327584052208158331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48919540885056034805438887 73379311327584052208158331)
          ·
            refine ⟨110068966991376078312237497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73379311327584052208158331 110068966991376078312237497)
            ·
              refine ⟨82551725243532058734178123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110068966991376078312237497 82551725243532058734178123)
              ·
                refine ⟨123827587865298088101267185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82551725243532058734178123 123827587865298088101267185)
                ·
                  refine ⟨92870690898973566075950389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 123827587865298088101267185 92870690898973566075950389)
                  ·
                    refine ⟨8706627271778771819620349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 92870690898973566075950389 8706627271778771819620349)
                    ·
                      refine ⟨3264985226917039432357631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8706627271778771819620349 3264985226917039432357631)
                      ·
                        rfl

theorem cell23_6358536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 2, 5, 3].length) (baseStart_6358536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6358536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6358536 prefixEnd_6358536 := by exact prefixLift 6358536
  have htrace : WordTrace (prefixWord ++ tailWord_6358536) baseStart_6358536 baseEnd_6358536 := by
    simpa [prefixWord, tailWord_6358536, baseEnd_6358536] using wordTrace_append hprefix tailTrace_6358536
  have hstable : (prefixWord ++ tailWord_6358536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6358536).length < 2 ^ (prefixWord ++ tailWord_6358536).sum := by decide
  have hdescent : baseEnd_6358536 < baseStart_6358536 := by decide
  rcases family_descends (prefixWord ++ tailWord_6358536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6358540 : List Nat := [2, 2, 1, 2, 5, 1, 2, 1, 2, 2, 3]
def baseStart_6358540 : Nat := 118140960795 + 6358540 * 2 ^ 59
def prefixEnd_6358540 : Nat := 4983230072969 + 3 ^ 40 * 6358540 * 2
def baseEnd_6358540 : Nat := 3264987280839657416707613

theorem tailTrace_6358540 : CollatzResearch.WordTrace tailWord_6358540 prefixEnd_6358540 3264987280839657416707613 := by
  unfold tailWord_6358540
  simp only [CollatzResearch.WordTrace]
  refine ⟨115957503192051503510020537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154610004256068671346694049 115957503192051503510020537)
  ·
    refine ⟨86968127394038627632515403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115957503192051503510020537 86968127394038627632515403)
    ·
      refine ⟨130452191091057941448773105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86968127394038627632515403 130452191091057941448773105)
      ·
        refine ⟨97839143318293456086579829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130452191091057941448773105 97839143318293456086579829)
        ·
          refine ⟨9172419686090011508116859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 97839143318293456086579829 9172419686090011508116859)
          ·
            refine ⟨13758629529135017262175289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9172419686090011508116859 13758629529135017262175289)
            ·
              refine ⟨10318972146851262946631467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13758629529135017262175289 10318972146851262946631467)
              ·
                refine ⟨15478458220276894419947201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10318972146851262946631467 15478458220276894419947201)
                ·
                  refine ⟨11608843665207670814960401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15478458220276894419947201 11608843665207670814960401)
                  ·
                    refine ⟨8706632748905753111220301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11608843665207670814960401 8706632748905753111220301)
                    ·
                      refine ⟨3264987280839657416707613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8706632748905753111220301 3264987280839657416707613)
                      ·
                        rfl

theorem cell23_6358540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 1, 2, 2, 3].length) (baseStart_6358540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6358540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6358540 prefixEnd_6358540 := by exact prefixLift 6358540
  have htrace : WordTrace (prefixWord ++ tailWord_6358540) baseStart_6358540 baseEnd_6358540 := by
    simpa [prefixWord, tailWord_6358540, baseEnd_6358540] using wordTrace_append hprefix tailTrace_6358540
  have hstable : (prefixWord ++ tailWord_6358540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6358540).length < 2 ^ (prefixWord ++ tailWord_6358540).sum := by decide
  have hdescent : baseEnd_6358540 < baseStart_6358540 := by decide
  rcases family_descends (prefixWord ++ tailWord_6358540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6358570 : List Nat := [3, 1, 4, 1, 1, 1, 2, 3, 3, 1, 3]
def baseStart_6358570 : Nat := 118140960795 + 6358570 * 2 ^ 59
def prefixEnd_6358570 : Nat := 4983230072969 + 3 ^ 40 * 6358570 * 2
def baseEnd_6358570 : Nat := 3265002685259292299332475

theorem tailTrace_6358570 : CollatzResearch.WordTrace tailWord_6358570 prefixEnd_6358570 3265002685259292299332475 := by
  unfold tailWord_6358570
  simp only [CollatzResearch.WordTrace]
  refine ⟨57979025143498580535908291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154610733715996214762422109 57979025143498580535908291)
  ·
    refine ⟨86968537715247870803862437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57979025143498580535908291 86968537715247870803862437)
    ·
      refine ⟨16306600821608975775724207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86968537715247870803862437 16306600821608975775724207)
      ·
        refine ⟨24459901232413463663586311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16306600821608975775724207 24459901232413463663586311)
        ·
          refine ⟨36689851848620195495379467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24459901232413463663586311 36689851848620195495379467)
          ·
            refine ⟨55034777772930293243069201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36689851848620195495379467 55034777772930293243069201)
            ·
              refine ⟨41276083329697719932301901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55034777772930293243069201 41276083329697719932301901)
              ·
                refine ⟨15478531248636644974613213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41276083329697719932301901 15478531248636644974613213)
                ·
                  refine ⟨5804449218238741865479955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15478531248636644974613213 5804449218238741865479955)
                  ·
                    refine ⟨8706673827358112798219933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5804449218238741865479955 8706673827358112798219933)
                    ·
                      refine ⟨3265002685259292299332475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8706673827358112798219933 3265002685259292299332475)
                      ·
                        rfl

theorem cell23_6358570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 3, 3, 1, 3].length) (baseStart_6358570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6358570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6358570 prefixEnd_6358570 := by exact prefixLift 6358570
  have htrace : WordTrace (prefixWord ++ tailWord_6358570) baseStart_6358570 baseEnd_6358570 := by
    simpa [prefixWord, tailWord_6358570, baseEnd_6358570] using wordTrace_append hprefix tailTrace_6358570
  have hstable : (prefixWord ++ tailWord_6358570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6358570).length < 2 ^ (prefixWord ++ tailWord_6358570).sum := by decide
  have hdescent : baseEnd_6358570 < baseStart_6358570 := by decide
  rcases family_descends (prefixWord ++ tailWord_6358570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6358593 : List Nat := [1, 2, 5, 1, 1, 1, 1, 3, 3, 1, 4]
def baseStart_6358593 : Nat := 118140960795 + 6358593 * 2 ^ 59
def prefixEnd_6358593 : Nat := 4983230072969 + 3 ^ 40 * 6358593 * 2
def baseEnd_6358593 : Nat := 3265014495314345709344869

theorem tailTrace_6358593 : CollatzResearch.WordTrace tailWord_6358593 prefixEnd_6358593 3265014495314345709344869 := by
  unfold tailWord_6358593
  simp only [CollatzResearch.WordTrace]
  refine ⟨231916939452910997071720433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154611292968607331381146955 231916939452910997071720433)
  ·
    refine ⟨173937704589683247803790325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231916939452910997071720433 173937704589683247803790325)
    ·
      refine ⟨16306659805282804481605343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 173937704589683247803790325 16306659805282804481605343)
      ·
        refine ⟨24459989707924206722408015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16306659805282804481605343 24459989707924206722408015)
        ·
          refine ⟨36689984561886310083612023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24459989707924206722408015 36689984561886310083612023)
          ·
            refine ⟨55034976842829465125418035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36689984561886310083612023 55034976842829465125418035)
            ·
              refine ⟨82552465264244197688127053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55034976842829465125418035 82552465264244197688127053)
              ·
                refine ⟨30957174474091574133047645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82552465264244197688127053 30957174474091574133047645)
                ·
                  refine ⟨11608940427784340299892867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30957174474091574133047645 11608940427784340299892867)
                  ·
                    refine ⟨17413410641676510449839301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11608940427784340299892867 17413410641676510449839301)
                    ·
                      refine ⟨3265014495314345709344869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17413410641676510449839301 3265014495314345709344869)
                      ·
                        rfl

theorem cell23_6358593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_6358593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6358593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6358593 prefixEnd_6358593 := by exact prefixLift 6358593
  have htrace : WordTrace (prefixWord ++ tailWord_6358593) baseStart_6358593 baseEnd_6358593 := by
    simpa [prefixWord, tailWord_6358593, baseEnd_6358593] using wordTrace_append hprefix tailTrace_6358593
  have hstable : (prefixWord ++ tailWord_6358593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6358593).length < 2 ^ (prefixWord ++ tailWord_6358593).sum := by decide
  have hdescent : baseEnd_6358593 < baseStart_6358593 := by decide
  rcases family_descends (prefixWord ++ tailWord_6358593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6358606 : List Nat := [4, 1, 1, 1, 1, 2, 1, 2, 3, 1, 6]
def baseStart_6358606 : Nat := 118140960795 + 6358606 * 2 ^ 59
def prefixEnd_6358606 : Nat := 4983230072969 + 3 ^ 40 * 6358606 * 2
def baseEnd_6358606 : Nat := 3265021170562854158482309

theorem tailTrace_6358606 : CollatzResearch.WordTrace tailWord_6358606 prefixEnd_6358606 3265021170562854158482309 := by
  unfold tailWord_6358606
  simp only [CollatzResearch.WordTrace]
  refine ⟨28989676700232987536492959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154611609067909266861295781 28989676700232987536492959)
  ·
    refine ⟨43484515050349481304739439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28989676700232987536492959 43484515050349481304739439)
    ·
      refine ⟨65226772575524221957109159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43484515050349481304739439 65226772575524221957109159)
      ·
        refine ⟨97840158863286332935663739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65226772575524221957109159 97840158863286332935663739)
        ·
          refine ⟨146760238294929499403495609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97840158863286332935663739 146760238294929499403495609)
          ·
            refine ⟨110070178721197124552621707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146760238294929499403495609 110070178721197124552621707)
            ·
              refine ⟨165105268081795686828932561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110070178721197124552621707 165105268081795686828932561)
              ·
                refine ⟨123828951061346765121699421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 165105268081795686828932561 123828951061346765121699421)
                ·
                  refine ⟨46435856648005036920637283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 123828951061346765121699421 46435856648005036920637283)
                  ·
                    refine ⟨69653784972007555380955925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46435856648005036920637283 69653784972007555380955925)
                    ·
                      refine ⟨3265021170562854158482309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69653784972007555380955925 3265021170562854158482309)
                      ·
                        rfl

theorem cell23_6358606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 3, 1, 6].length) (baseStart_6358606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6358606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6358606 prefixEnd_6358606 := by exact prefixLift 6358606
  have htrace : WordTrace (prefixWord ++ tailWord_6358606) baseStart_6358606 baseEnd_6358606 := by
    simpa [prefixWord, tailWord_6358606, baseEnd_6358606] using wordTrace_append hprefix tailTrace_6358606
  have hstable : (prefixWord ++ tailWord_6358606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6358606).length < 2 ^ (prefixWord ++ tailWord_6358606).sum := by decide
  have hdescent : baseEnd_6358606 < baseStart_6358606 := by decide
  rcases family_descends (prefixWord ++ tailWord_6358606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6358610 : List Nat := [3, 2, 2, 1, 2, 3, 1, 3, 1, 1, 4]
def baseStart_6358610 : Nat := 118140960795 + 6358610 * 2 ^ 59
def prefixEnd_6358610 : Nat := 4983230072969 + 3 ^ 40 * 6358610 * 2
def baseEnd_6358610 : Nat := 3265023224485472142832291

theorem tailTrace_6358610 : CollatzResearch.WordTrace tailWord_6358610 prefixEnd_6358610 3265023224485472142832291 := by
  unfold tailWord_6358610
  simp only [CollatzResearch.WordTrace]
  refine ⟨57979389873462352243772321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154611706329232939316726189 57979389873462352243772321)
  ·
    refine ⟨43484542405096764182829241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57979389873462352243772321 43484542405096764182829241)
    ·
      refine ⟨32613406803822573137121931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43484542405096764182829241 32613406803822573137121931)
      ·
        refine ⟨48920110205733859705682897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32613406803822573137121931 48920110205733859705682897)
        ·
          refine ⟨36690082654300394779262173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48920110205733859705682897 36690082654300394779262173)
          ·
            refine ⟨13758780995362648042223315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36690082654300394779262173 13758780995362648042223315)
            ·
              refine ⟨20638171493043972063334973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13758780995362648042223315 20638171493043972063334973)
              ·
                refine ⟨7739314309891489523750615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20638171493043972063334973 7739314309891489523750615)
                ·
                  refine ⟨11608971464837234285625923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7739314309891489523750615 11608971464837234285625923)
                  ·
                    refine ⟨17413457197255851428438885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11608971464837234285625923 17413457197255851428438885)
                    ·
                      refine ⟨3265023224485472142832291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17413457197255851428438885 3265023224485472142832291)
                      ·
                        rfl

theorem cell23_6358610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 3, 1, 1, 4].length) (baseStart_6358610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6358610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6358610 prefixEnd_6358610 := by exact prefixLift 6358610
  have htrace : WordTrace (prefixWord ++ tailWord_6358610) baseStart_6358610 baseEnd_6358610 := by
    simpa [prefixWord, tailWord_6358610, baseEnd_6358610] using wordTrace_append hprefix tailTrace_6358610
  have hstable : (prefixWord ++ tailWord_6358610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6358610).length < 2 ^ (prefixWord ++ tailWord_6358610).sum := by decide
  have hdescent : baseEnd_6358610 < baseStart_6358610 := by decide
  rcases family_descends (prefixWord ++ tailWord_6358610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6358620 : List Nat := [2, 2, 4, 1, 2, 2, 1, 1, 4, 4]
def baseStart_6358620 : Nat := 118140960795 + 6358620 * 2 ^ 59
def prefixEnd_6358620 : Nat := 4983230072969 + 3 ^ 40 * 6358620 * 2
def baseEnd_6358620 : Nat := 1088342786430672367902415

theorem tailTrace_6358620 : CollatzResearch.WordTrace tailWord_6358620 prefixEnd_6358620 1088342786430672367902415 := by
  unfold tailWord_6358620
  simp only [CollatzResearch.WordTrace]
  refine ⟨115958962111906590341476657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154611949482542120455302209 115958962111906590341476657)
  ·
    refine ⟨86969221583929942756107493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115958962111906590341476657 86969221583929942756107493)
    ·
      refine ⟨16306729046986864266770155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86969221583929942756107493 16306729046986864266770155)
      ·
        refine ⟨24460093570480296400155233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16306729046986864266770155 24460093570480296400155233)
        ·
          refine ⟨18345070177860222300116425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24460093570480296400155233 18345070177860222300116425)
          ·
            refine ⟨13758802633395166725087319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18345070177860222300116425 13758802633395166725087319)
            ·
              refine ⟨20638203950092750087630979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13758802633395166725087319 20638203950092750087630979)
              ·
                refine ⟨30957305925139125131446469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20638203950092750087630979 30957305925139125131446469)
                ·
                  refine ⟨5804494860963585962146213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30957305925139125131446469 5804494860963585962146213)
                  ·
                    refine ⟨1088342786430672367902415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5804494860963585962146213 1088342786430672367902415)
                    ·
                      rfl

theorem cell23_6358620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 1, 4, 4].length) (baseStart_6358620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6358620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6358620 prefixEnd_6358620 := by exact prefixLift 6358620
  have htrace : WordTrace (prefixWord ++ tailWord_6358620) baseStart_6358620 baseEnd_6358620 := by
    simpa [prefixWord, tailWord_6358620, baseEnd_6358620] using wordTrace_append hprefix tailTrace_6358620
  have hstable : (prefixWord ++ tailWord_6358620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6358620).length < 2 ^ (prefixWord ++ tailWord_6358620).sum := by decide
  have hdescent : baseEnd_6358620 < baseStart_6358620 := by decide
  rcases family_descends (prefixWord ++ tailWord_6358620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6358627 : List Nat := [1, 1, 1, 5, 1, 4, 2, 1, 3, 2, 2]
def baseStart_6358627 : Nat := 118140960795 + 6358627 * 2 ^ 59
def prefixEnd_6358627 : Nat := 4983230072969 + 3 ^ 40 * 6358627 * 2
def baseEnd_6358627 : Nat := 3265031953656598576319713

theorem tailTrace_6358627 : CollatzResearch.WordTrace tailWord_6358627 prefixEnd_6358627 3265031953656598576319713 := by
  unfold tailWord_6358627
  simp only [CollatzResearch.WordTrace]
  refine ⟨231918179534787820878458135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154612119689858547252305423 231918179534787820878458135)
  ·
    refine ⟨347877269302181731317687203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231918179534787820878458135 347877269302181731317687203)
    ·
      refine ⟨521815903953272596976530805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 347877269302181731317687203 521815903953272596976530805)
      ·
        refine ⟨48920240995619305966549763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 521815903953272596976530805 48920240995619305966549763)
        ·
          refine ⟨73380361493428958949824645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48920240995619305966549763 73380361493428958949824645)
          ·
            refine ⟨13758817780017929803092121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73380361493428958949824645 13758817780017929803092121)
            ·
              refine ⟨10319113335013447352319091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13758817780017929803092121 10319113335013447352319091)
              ·
                refine ⟨15478670002520171028478637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10319113335013447352319091 15478670002520171028478637)
                ·
                  refine ⟨5804501250945064135679489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15478670002520171028478637 5804501250945064135679489)
                  ·
                    refine ⟨4353375938208798101759617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5804501250945064135679489 4353375938208798101759617)
                    ·
                      refine ⟨3265031953656598576319713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4353375938208798101759617 3265031953656598576319713)
                      ·
                        rfl

theorem cell23_6358627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 1, 3, 2, 2].length) (baseStart_6358627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6358627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6358627 prefixEnd_6358627 := by exact prefixLift 6358627
  have htrace : WordTrace (prefixWord ++ tailWord_6358627) baseStart_6358627 baseEnd_6358627 := by
    simpa [prefixWord, tailWord_6358627, baseEnd_6358627] using wordTrace_append hprefix tailTrace_6358627
  have hstable : (prefixWord ++ tailWord_6358627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6358627).length < 2 ^ (prefixWord ++ tailWord_6358627).sum := by decide
  have hdescent : baseEnd_6358627 < baseStart_6358627 := by decide
  rcases family_descends (prefixWord ++ tailWord_6358627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6358637 : List Nat := [1, 5, 1, 1, 5, 1, 1, 1, 1, 6]
def baseStart_6358637 : Nat := 118140960795 + 6358637 * 2 ^ 59
def prefixEnd_6358637 : Nat := 4983230072969 + 3 ^ 40 * 6358637 * 2
def baseEnd_6358637 : Nat := 1088345696154381179064889

theorem tailTrace_6358637 : CollatzResearch.WordTrace tailWord_6358637 prefixEnd_6358637 1088345696154381179064889 := by
  unfold tailWord_6358637
  simp only [CollatzResearch.WordTrace]
  refine ⟨231918544264751592586322165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154612362843167728390881443 231918544264751592586322165)
  ·
    refine ⟨21742363524820461804967703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 231918544264751592586322165 21742363524820461804967703)
    ·
      refine ⟨32613545287230692707451555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21742363524820461804967703 32613545287230692707451555)
      ·
        refine ⟨48920317930846039061177333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32613545287230692707451555 48920317930846039061177333)
        ·
          refine ⟨4586279806016816161985375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48920317930846039061177333 4586279806016816161985375)
          ·
            refine ⟨6879419709025224242978063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4586279806016816161985375 6879419709025224242978063)
            ·
              refine ⟨10319129563537836364467095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6879419709025224242978063 10319129563537836364467095)
              ·
                refine ⟨15478694345306754546700643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10319129563537836364467095 15478694345306754546700643)
                ·
                  refine ⟨23218041517960131820050965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15478694345306754546700643 23218041517960131820050965)
                  ·
                    refine ⟨1088345696154381179064889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23218041517960131820050965 1088345696154381179064889)
                    ·
                      rfl

theorem cell23_6358637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 1, 1, 6].length) (baseStart_6358637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6358637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6358637 prefixEnd_6358637 := by exact prefixLift 6358637
  have htrace : WordTrace (prefixWord ++ tailWord_6358637) baseStart_6358637 baseEnd_6358637 := by
    simpa [prefixWord, tailWord_6358637, baseEnd_6358637] using wordTrace_append hprefix tailTrace_6358637
  have hstable : (prefixWord ++ tailWord_6358637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6358637).length < 2 ^ (prefixWord ++ tailWord_6358637).sum := by decide
  have hdescent : baseEnd_6358637 < baseStart_6358637 := by decide
  rcases family_descends (prefixWord ++ tailWord_6358637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6358640 : List Nat := [2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 4]
def baseStart_6358640 : Nat := 118140960795 + 6358640 * 2 ^ 59
def prefixEnd_6358640 : Nat := 4983230072969 + 3 ^ 40 * 6358640 * 2
def baseEnd_6358640 : Nat := 3265038628905107025457153

theorem tailTrace_6358640 : CollatzResearch.WordTrace tailWord_6358640 prefixEnd_6358640 3265038628905107025457153 := by
  unfold tailWord_6358640
  simp only [CollatzResearch.WordTrace]
  refine ⟨115959326841870362049340687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154612435789160482732454249 115959326841870362049340687)
  ·
    refine ⟨173938990262805543074011031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115959326841870362049340687 173938990262805543074011031)
    ·
      refine ⟨260908485394208314611016547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173938990262805543074011031 260908485394208314611016547)
      ·
        refine ⟨391362728091312471916524821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260908485394208314611016547 391362728091312471916524821)
        ·
          refine ⟨18345127879280272121087101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 391362728091312471916524821 18345127879280272121087101)
          ·
            refine ⟨6879422954730102045407663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18345127879280272121087101 6879422954730102045407663)
            ·
              refine ⟨10319134432095153068111495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6879422954730102045407663 10319134432095153068111495)
              ·
                refine ⟨15478701648142729602167243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10319134432095153068111495 15478701648142729602167243)
                ·
                  refine ⟨23218052472214094403250865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15478701648142729602167243 23218052472214094403250865)
                  ·
                    refine ⟨17413539354160570802438149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23218052472214094403250865 17413539354160570802438149)
                    ·
                      refine ⟨3265038628905107025457153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17413539354160570802438149 3265038628905107025457153)
                      ·
                        rfl

theorem cell23_6358640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 4].length) (baseStart_6358640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6358640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6358640 prefixEnd_6358640 := by exact prefixLift 6358640
  have htrace : WordTrace (prefixWord ++ tailWord_6358640) baseStart_6358640 baseEnd_6358640 := by
    simpa [prefixWord, tailWord_6358640, baseEnd_6358640] using wordTrace_append hprefix tailTrace_6358640
  have hstable : (prefixWord ++ tailWord_6358640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6358640).length < 2 ^ (prefixWord ++ tailWord_6358640).sum := by decide
  have hdescent : baseEnd_6358640 < baseStart_6358640 := by decide
  rcases family_descends (prefixWord ++ tailWord_6358640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6358656 : List Nat := [2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 5]
def baseStart_6358656 : Nat := 118140960795 + 6358656 * 2 ^ 59
def prefixEnd_6358656 : Nat := 4983230072969 + 3 ^ 40 * 6358656 * 2
def baseEnd_6358656 : Nat := 3265046844595578962857079

theorem tailTrace_6358656 : CollatzResearch.WordTrace tailWord_6358656 prefixEnd_6358656 3265046844595578962857079 := by
  unfold tailWord_6358656
  simp only [CollatzResearch.WordTrace]
  refine ⟨115959618625841379415631911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154612824834455172554175881 115959618625841379415631911)
  ·
    refine ⟨173939427938762069123447867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115959618625841379415631911 173939427938762069123447867)
    ·
      refine ⟨260909141908143103685171801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173939427938762069123447867 260909141908143103685171801)
      ·
        refine ⟨195681856431107327763878851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 260909141908143103685171801 195681856431107327763878851)
        ·
          refine ⟨293522784646660991645818277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195681856431107327763878851 293522784646660991645818277)
          ·
            refine ⟨55035522121248935933590927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 293522784646660991645818277 55035522121248935933590927)
            ·
              refine ⟨82553283181873403900386391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55035522121248935933590927 82553283181873403900386391)
              ·
                refine ⟨123829924772810105850579587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82553283181873403900386391 123829924772810105850579587)
                ·
                  refine ⟨185744887159215158775869381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 123829924772810105850579587 185744887159215158775869381)
                  ·
                    refine ⟨34827166342352842270475509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 185744887159215158775869381 34827166342352842270475509)
                    ·
                      refine ⟨3265046844595578962857079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34827166342352842270475509 3265046844595578962857079)
                      ·
                        rfl

theorem cell23_6358656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 5].length) (baseStart_6358656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6358656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6358656 prefixEnd_6358656 := by exact prefixLift 6358656
  have htrace : WordTrace (prefixWord ++ tailWord_6358656) baseStart_6358656 baseEnd_6358656 := by
    simpa [prefixWord, tailWord_6358656, baseEnd_6358656] using wordTrace_append hprefix tailTrace_6358656
  have hstable : (prefixWord ++ tailWord_6358656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6358656).length < 2 ^ (prefixWord ++ tailWord_6358656).sum := by decide
  have hdescent : baseEnd_6358656 < baseStart_6358656 := by decide
  rcases family_descends (prefixWord ++ tailWord_6358656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6358734 : List Nat := [4, 1, 1, 1, 3, 1, 4, 2, 2, 2, 2]
def baseStart_6358734 : Nat := 118140960795 + 6358734 * 2 ^ 59
def prefixEnd_6358734 : Nat := 4983230072969 + 3 ^ 40 * 6358734 * 2
def baseEnd_6358734 : Nat := 3265086896086629657681721

theorem tailTrace_6358734 : CollatzResearch.WordTrace tailWord_6358734 prefixEnd_6358734 3265086896086629657681721 := by
  unfold tailWord_6358734
  simp only [CollatzResearch.WordTrace]
  refine ⟨28990260268175022269075407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154614721430266785435068837 28990260268175022269075407)
  ·
    refine ⟨43485390402262533403613111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28990260268175022269075407 43485390402262533403613111)
    ·
      refine ⟨65228085603393800105419667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43485390402262533403613111 65228085603393800105419667)
      ·
        refine ⟨97842128405090700158129501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65228085603393800105419667 97842128405090700158129501)
        ·
          refine ⟨36690798151909012559298563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97842128405090700158129501 36690798151909012559298563)
          ·
            refine ⟨55036197227863518838947845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36690798151909012559298563 55036197227863518838947845)
            ·
              refine ⟨10319286980224409782302721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55036197227863518838947845 10319286980224409782302721)
              ·
                refine ⟨7739465235168307336727041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10319286980224409782302721 7739465235168307336727041)
                ·
                  refine ⟨5804598926376230502545281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7739465235168307336727041 5804598926376230502545281)
                  ·
                    refine ⟨4353449194782172876908961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5804598926376230502545281 4353449194782172876908961)
                    ·
                      refine ⟨3265086896086629657681721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4353449194782172876908961 3265086896086629657681721)
                      ·
                        rfl

theorem cell23_6358734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 2, 2, 2, 2].length) (baseStart_6358734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6358734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6358734 prefixEnd_6358734 := by exact prefixLift 6358734
  have htrace : WordTrace (prefixWord ++ tailWord_6358734) baseStart_6358734 baseEnd_6358734 := by
    simpa [prefixWord, tailWord_6358734, baseEnd_6358734] using wordTrace_append hprefix tailTrace_6358734
  have hstable : (prefixWord ++ tailWord_6358734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6358734).length < 2 ^ (prefixWord ++ tailWord_6358734).sum := by decide
  have hdescent : baseEnd_6358734 < baseStart_6358734 := by decide
  rcases family_descends (prefixWord ++ tailWord_6358734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6358807 : List Nat := [1, 1, 3, 4, 2, 1, 2, 1, 2, 4, 2]
def baseStart_6358807 : Nat := 118140960795 + 6358807 * 2 ^ 59
def prefixEnd_6358807 : Nat := 4983230072969 + 3 ^ 40 * 6358807 * 2
def baseEnd_6358807 : Nat := 3265124380174407872068885

theorem tailTrace_6358807 : CollatzResearch.WordTrace tailWord_6358807 prefixEnd_6358807 3265124380174407872068885 := by
  unfold tailWord_6358807
  simp only [CollatzResearch.WordTrace]
  refine ⟨231924744674135711620010675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154616496449423807746673783 231924744674135711620010675)
  ·
    refine ⟨347887117011203567430016013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231924744674135711620010675 347887117011203567430016013)
    ·
      refine ⟨130457668879201337786256005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 347887117011203567430016013 130457668879201337786256005)
      ·
        refine ⟨24460812914850250834923001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 130457668879201337786256005 24460812914850250834923001)
        ·
          refine ⟨18345609686137688126192251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24460812914850250834923001 18345609686137688126192251)
          ·
            refine ⟨27518414529206532189288377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18345609686137688126192251 27518414529206532189288377)
            ·
              refine ⟨20638810896904899141966283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27518414529206532189288377 20638810896904899141966283)
              ·
                refine ⟨30958216345357348712949425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20638810896904899141966283 30958216345357348712949425)
                ·
                  refine ⟨23218662259018011534712069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30958216345357348712949425 23218662259018011534712069)
                  ·
                    refine ⟨4353499173565877162758513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23218662259018011534712069 4353499173565877162758513)
                    ·
                      refine ⟨3265124380174407872068885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4353499173565877162758513 3265124380174407872068885)
                      ·
                        rfl

theorem cell23_6358807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 1, 2, 4, 2].length) (baseStart_6358807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6358807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6358807 prefixEnd_6358807 := by exact prefixLift 6358807
  have htrace : WordTrace (prefixWord ++ tailWord_6358807) baseStart_6358807 baseEnd_6358807 := by
    simpa [prefixWord, tailWord_6358807, baseEnd_6358807] using wordTrace_append hprefix tailTrace_6358807
  have hstable : (prefixWord ++ tailWord_6358807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6358807).length < 2 ^ (prefixWord ++ tailWord_6358807).sum := by decide
  have hdescent : baseEnd_6358807 < baseStart_6358807 := by decide
  rcases family_descends (prefixWord ++ tailWord_6358807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6358810 : List Nat := [3, 1, 1, 3, 2, 2, 1, 2, 1, 4, 3]
def baseStart_6358810 : Nat := 118140960795 + 6358810 * 2 ^ 59
def prefixEnd_6358810 : Nat := 4983230072969 + 3 ^ 40 * 6358810 * 2
def baseEnd_6358810 : Nat := 3265125920616371360331371

theorem tailTrace_6358810 : CollatzResearch.WordTrace tailWord_6358810 prefixEnd_6358810 3265125920616371360331371 := by
  unfold tailWord_6358810
  simp only [CollatzResearch.WordTrace]
  refine ⟨57981213523281210783092471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154616569395416562088246589 57981213523281210783092471)
  ·
    refine ⟨86971820284921816174638707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57981213523281210783092471 86971820284921816174638707)
    ·
      refine ⟨130457730427382724261958061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86971820284921816174638707 130457730427382724261958061)
      ·
        refine ⟨48921648910268521598234273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130457730427382724261958061 48921648910268521598234273)
        ·
          refine ⟨36691236682701391198675705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48921648910268521598234273 36691236682701391198675705)
          ·
            refine ⟨27518427512026043399006779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36691236682701391198675705 27518427512026043399006779)
            ·
              refine ⟨41277641268039065098510169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27518427512026043399006779 41277641268039065098510169)
              ·
                refine ⟨30958230951029298823882627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41277641268039065098510169 30958230951029298823882627)
                ·
                  refine ⟨46437346426543948235823941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30958230951029298823882627 46437346426543948235823941)
                  ·
                    refine ⟨8707002454976990294216989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46437346426543948235823941 8707002454976990294216989)
                    ·
                      refine ⟨3265125920616371360331371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8707002454976990294216989 3265125920616371360331371)
                      ·
                        rfl

theorem cell23_6358810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 2, 1, 4, 3].length) (baseStart_6358810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6358810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6358810 prefixEnd_6358810 := by exact prefixLift 6358810
  have htrace : WordTrace (prefixWord ++ tailWord_6358810) baseStart_6358810 baseEnd_6358810 := by
    simpa [prefixWord, tailWord_6358810, baseEnd_6358810] using wordTrace_append hprefix tailTrace_6358810
  have hstable : (prefixWord ++ tailWord_6358810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6358810).length < 2 ^ (prefixWord ++ tailWord_6358810).sum := by decide
  have hdescent : baseEnd_6358810 < baseStart_6358810 := by decide
  rcases family_descends (prefixWord ++ tailWord_6358810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6358834 : List Nat := [3, 2, 1, 1, 3, 2, 3, 3, 1, 4]
def baseStart_6358834 : Nat := 118140960795 + 6358834 * 2 ^ 59
def prefixEnd_6358834 : Nat := 4983230072969 + 3 ^ 40 * 6358834 * 2
def baseEnd_6358834 : Nat := 1088379414717359755477087

theorem tailTrace_6358834 : CollatzResearch.WordTrace tailWord_6358834 prefixEnd_6358834 1088379414717359755477087 := by
  unfold tailWord_6358834
  simp only [CollatzResearch.WordTrace]
  refine ⟨57981432361259473807810889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154617152963358596820829037 57981432361259473807810889)
  ·
    refine ⟨43486074270944605355858167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57981432361259473807810889 43486074270944605355858167)
    ·
      refine ⟨65229111406416908033787251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43486074270944605355858167 65229111406416908033787251)
      ·
        refine ⟨97843667109625362050680877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65229111406416908033787251 97843667109625362050680877)
        ·
          refine ⟨36691375166109510769005329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97843667109625362050680877 36691375166109510769005329)
          ·
            refine ⟨27518531374582133076753997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36691375166109510769005329 27518531374582133076753997)
            ·
              refine ⟨10319449265468299903782749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27518531374582133076753997 10319449265468299903782749)
              ·
                refine ⟨3869793474550612463918531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10319449265468299903782749 3869793474550612463918531)
                ·
                  refine ⟨5804690211825918695877797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3869793474550612463918531 5804690211825918695877797)
                  ·
                    refine ⟨1088379414717359755477087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5804690211825918695877797 1088379414717359755477087)
                    ·
                      rfl

theorem cell23_6358834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 3, 1, 4].length) (baseStart_6358834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6358834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6358834 prefixEnd_6358834 := by exact prefixLift 6358834
  have htrace : WordTrace (prefixWord ++ tailWord_6358834) baseStart_6358834 baseEnd_6358834 := by
    simpa [prefixWord, tailWord_6358834, baseEnd_6358834] using wordTrace_append hprefix tailTrace_6358834
  have hstable : (prefixWord ++ tailWord_6358834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6358834).length < 2 ^ (prefixWord ++ tailWord_6358834).sum := by decide
  have hdescent : baseEnd_6358834 < baseStart_6358834 := by decide
  rcases family_descends (prefixWord ++ tailWord_6358834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6358947 : List Nat := [1, 1, 1, 4, 1, 2, 1, 4, 4, 1, 3]
def baseStart_6358947 : Nat := 118140960795 + 6358947 * 2 ^ 59
def prefixEnd_6358947 : Nat := 4983230072969 + 3 ^ 40 * 6358947 * 2
def baseEnd_6358947 : Nat := 3265196267466037324318241

theorem tailTrace_6358947 : CollatzResearch.WordTrace tailWord_6358947 prefixEnd_6358947 3265196267466037324318241 := by
  unfold tailWord_6358947
  simp only [CollatzResearch.WordTrace]
  refine ⟨231929850893628515530107095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154619900595752343686738063 231929850893628515530107095)
  ·
    refine ⟨347894776340442773295160643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231929850893628515530107095 347894776340442773295160643)
    ·
      refine ⟨521842164510664159942740965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 347894776340442773295160643 521842164510664159942740965)
      ·
        refine ⟨97845405845749529989263931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 521842164510664159942740965 97845405845749529989263931)
        ·
          refine ⟨146768108768624294983895897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97845405845749529989263931 146768108768624294983895897)
          ·
            refine ⟨110076081576468221237921923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146768108768624294983895897 110076081576468221237921923)
            ·
              refine ⟨165114122364702331856882885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110076081576468221237921923 165114122364702331856882885)
              ·
                refine ⟨30958897943381687223165541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 165114122364702331856882885 30958897943381687223165541)
                ·
                  refine ⟨5804793364384066354343539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30958897943381687223165541 5804793364384066354343539)
                  ·
                    refine ⟨8707190046576099531515309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5804793364384066354343539 8707190046576099531515309)
                    ·
                      refine ⟨3265196267466037324318241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8707190046576099531515309 3265196267466037324318241)
                      ·
                        rfl

theorem cell23_6358947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 4, 4, 1, 3].length) (baseStart_6358947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6358947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6358947 prefixEnd_6358947 := by exact prefixLift 6358947
  have htrace : WordTrace (prefixWord ++ tailWord_6358947) baseStart_6358947 baseEnd_6358947 := by
    simpa [prefixWord, tailWord_6358947, baseEnd_6358947] using wordTrace_append hprefix tailTrace_6358947
  have hstable : (prefixWord ++ tailWord_6358947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6358947).length < 2 ^ (prefixWord ++ tailWord_6358947).sum := by decide
  have hdescent : baseEnd_6358947 < baseStart_6358947 := by decide
  rcases family_descends (prefixWord ++ tailWord_6358947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6358948 : List Nat := [2, 3, 1, 2, 1, 4, 2, 3, 1, 2, 2]
def baseStart_6358948 : Nat := 118140960795 + 6358948 * 2 ^ 59
def prefixEnd_6358948 : Nat := 4983230072969 + 3 ^ 40 * 6358948 * 2
def baseEnd_6358948 : Nat := 3265196780946691820405737

theorem tailTrace_6358948 : CollatzResearch.WordTrace tailWord_6358948 prefixEnd_6358948 3265196780946691820405737 := by
  unfold tailWord_6358948
  simp only [CollatzResearch.WordTrace]
  refine ⟨115964943683312446350446749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154619924911083261800595665 115964943683312446350446749)
  ·
    refine ⟨43486853881242167381417531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115964943683312446350446749 43486853881242167381417531)
    ·
      refine ⟨65230280821863251072126297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43486853881242167381417531 65230280821863251072126297)
      ·
        refine ⟨48922710616397438304094723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65230280821863251072126297 48922710616397438304094723)
        ·
          refine ⟨73384065924596157456142085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48922710616397438304094723 73384065924596157456142085)
          ·
            refine ⟨13759512360861779523026641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73384065924596157456142085 13759512360861779523026641)
            ·
              refine ⟨10319634270646334642269981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13759512360861779523026641 10319634270646334642269981)
              ·
                refine ⟨3869862851492375490851243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10319634270646334642269981 3869862851492375490851243)
                ·
                  refine ⟨5804794277238563236276865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3869862851492375490851243 5804794277238563236276865)
                  ·
                    refine ⟨4353595707928922427207649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5804794277238563236276865 4353595707928922427207649)
                    ·
                      refine ⟨3265196780946691820405737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4353595707928922427207649 3265196780946691820405737)
                      ·
                        rfl

theorem cell23_6358948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 3, 1, 2, 2].length) (baseStart_6358948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6358948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6358948 prefixEnd_6358948 := by exact prefixLift 6358948
  have htrace : WordTrace (prefixWord ++ tailWord_6358948) baseStart_6358948 baseEnd_6358948 := by
    simpa [prefixWord, tailWord_6358948, baseEnd_6358948] using wordTrace_append hprefix tailTrace_6358948
  have hstable : (prefixWord ++ tailWord_6358948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6358948).length < 2 ^ (prefixWord ++ tailWord_6358948).sum := by decide
  have hdescent : baseEnd_6358948 < baseStart_6358948 := by decide
  rcases family_descends (prefixWord ++ tailWord_6358948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6358951 : List Nat := [1, 1, 6, 1, 2, 1, 4, 1, 1, 2, 3]
def baseStart_6358951 : Nat := 118140960795 + 6358951 * 2 ^ 59
def prefixEnd_6358951 : Nat := 4983230072969 + 3 ^ 40 * 6358951 * 2
def baseEnd_6358951 : Nat := 3265198321388655308668223

theorem tailTrace_6358951 : CollatzResearch.WordTrace tailWord_6358951 prefixEnd_6358951 3265198321388655308668223 := by
  unfold tailWord_6358951
  simp only [CollatzResearch.WordTrace]
  refine ⟨231929996785614024213252707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154619997857076016142168471 231929996785614024213252707)
  ·
    refine ⟨347894995178421036319879061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231929996785614024213252707 347894995178421036319879061)
    ·
      refine ⟨16307577898988486077494331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 347894995178421036319879061 16307577898988486077494331)
      ·
        refine ⟨24461366848482729116241497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16307577898988486077494331 24461366848482729116241497)
        ·
          refine ⟨18346025136362046837181123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24461366848482729116241497 18346025136362046837181123)
          ·
            refine ⟨27519037704543070255771685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18346025136362046837181123 27519037704543070255771685)
            ·
              refine ⟨5159819569601825672957191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27519037704543070255771685 5159819569601825672957191)
              ·
                refine ⟨7739729354402738509435787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5159819569601825672957191 7739729354402738509435787)
                ·
                  refine ⟨11609594031604107764153681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7739729354402738509435787 11609594031604107764153681)
                  ·
                    refine ⟨8707195523703080823115261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11609594031604107764153681 8707195523703080823115261)
                    ·
                      refine ⟨3265198321388655308668223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8707195523703080823115261 3265198321388655308668223)
                      ·
                        rfl

theorem cell23_6358951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 4, 1, 1, 2, 3].length) (baseStart_6358951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6358951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6358951 prefixEnd_6358951 := by exact prefixLift 6358951
  have htrace : WordTrace (prefixWord ++ tailWord_6358951) baseStart_6358951 baseEnd_6358951 := by
    simpa [prefixWord, tailWord_6358951, baseEnd_6358951] using wordTrace_append hprefix tailTrace_6358951
  have hstable : (prefixWord ++ tailWord_6358951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6358951).length < 2 ^ (prefixWord ++ tailWord_6358951).sum := by decide
  have hdescent : baseEnd_6358951 < baseStart_6358951 := by decide
  rcases family_descends (prefixWord ++ tailWord_6358951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6358958 : List Nat := [4, 1, 5, 1, 1, 1, 1, 1, 4, 4]
def baseStart_6358958 : Nat := 118140960795 + 6358958 * 2 ^ 59
def prefixEnd_6358958 : Nat := 4983230072969 + 3 ^ 40 * 6358958 * 2
def baseEnd_6358958 : Nat := 1088400638584412260426897

theorem tailTrace_6358958 : CollatzResearch.WordTrace tailWord_6358958 prefixEnd_6358958 1088400638584412260426897 := by
  unfold tailWord_6358958
  simp only [CollatzResearch.WordTrace]
  refine ⟨28991281512073583051094691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154620168064392442939171685 28991281512073583051094691)
  ·
    refine ⟨43486922268110374576642037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28991281512073583051094691 43486922268110374576642037)
    ·
      refine ⟨4076898962635347616560191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43486922268110374576642037 4076898962635347616560191)
      ·
        refine ⟨6115348443953021424840287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4076898962635347616560191 6115348443953021424840287)
        ·
          refine ⟨9173022665929532137260431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6115348443953021424840287 9173022665929532137260431)
          ·
            refine ⟨13759533998894298205890647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9173022665929532137260431 13759533998894298205890647)
            ·
              refine ⟨20639300998341447308835971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13759533998894298205890647 20639300998341447308835971)
              ·
                refine ⟨30958951497512170963253957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20639300998341447308835971 30958951497512170963253957)
                ·
                  refine ⟨5804803405783532055610117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30958951497512170963253957 5804803405783532055610117)
                  ·
                    refine ⟨1088400638584412260426897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5804803405783532055610117 1088400638584412260426897)
                    ·
                      rfl

theorem cell23_6358958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_6358958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6358958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6358958 prefixEnd_6358958 := by exact prefixLift 6358958
  have htrace : WordTrace (prefixWord ++ tailWord_6358958) baseStart_6358958 baseEnd_6358958 := by
    simpa [prefixWord, tailWord_6358958, baseEnd_6358958] using wordTrace_append hprefix tailTrace_6358958
  have hstable : (prefixWord ++ tailWord_6358958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6358958).length < 2 ^ (prefixWord ++ tailWord_6358958).sum := by decide
  have hdescent : baseEnd_6358958 < baseStart_6358958 := by decide
  rcases family_descends (prefixWord ++ tailWord_6358958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6358970 : List Nat := [3, 1, 1, 1, 2, 1, 2, 3, 2, 3, 4]
def baseStart_6358970 : Nat := 118140960795 + 6358970 * 2 ^ 59
def prefixEnd_6358970 : Nat := 4983230072969 + 3 ^ 40 * 6358970 * 2
def baseEnd_6358970 : Nat := 3265208077521090734330635

theorem tailTrace_6358970 : CollatzResearch.WordTrace tailWord_6358970 prefixEnd_6358970 3265208077521090734330635 := by
  unfold tailWord_6358970
  simp only [CollatzResearch.WordTrace]
  refine ⟨57982672443136297614548591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154620459848363460305462909 57982672443136297614548591)
  ·
    refine ⟨86974008664704446421822887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57982672443136297614548591 86974008664704446421822887)
    ·
      refine ⟨130461012997056669632734331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86974008664704446421822887 130461012997056669632734331)
      ·
        refine ⟨195691519495585004449101497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130461012997056669632734331 195691519495585004449101497)
        ·
          refine ⟨146768639621688753336826123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 195691519495585004449101497 146768639621688753336826123)
          ·
            refine ⟨220152959432533130005239185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146768639621688753336826123 220152959432533130005239185)
            ·
              refine ⟨165114719574399847503929389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 220152959432533130005239185 165114719574399847503929389)
              ·
                refine ⟨61918019840399942813973521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 165114719574399847503929389 61918019840399942813973521)
                ·
                  refine ⟨46438514880299957110480141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61918019840399942813973521 46438514880299957110480141)
                  ·
                    refine ⟨17414443080112483916430053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46438514880299957110480141 17414443080112483916430053)
                    ·
                      refine ⟨3265208077521090734330635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17414443080112483916430053 3265208077521090734330635)
                      ·
                        rfl

theorem cell23_6358970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 3, 2, 3, 4].length) (baseStart_6358970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6358970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6358970 prefixEnd_6358970 := by exact prefixLift 6358970
  have htrace : WordTrace (prefixWord ++ tailWord_6358970) baseStart_6358970 baseEnd_6358970 := by
    simpa [prefixWord, tailWord_6358970, baseEnd_6358970] using wordTrace_append hprefix tailTrace_6358970
  have hstable : (prefixWord ++ tailWord_6358970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6358970).length < 2 ^ (prefixWord ++ tailWord_6358970).sum := by decide
  have hdescent : baseEnd_6358970 < baseStart_6358970 := by decide
  rcases family_descends (prefixWord ++ tailWord_6358970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6359007 : List Nat := [1, 1, 2, 3, 4, 2, 1, 1, 2, 1, 5]
def baseStart_6359007 : Nat := 118140960795 + 6359007 * 2 ^ 59
def prefixEnd_6359007 : Nat := 4983230072969 + 3 ^ 40 * 6359007 * 2
def baseEnd_6359007 : Nat := 3265227076305307089567965

theorem tailTrace_6359007 : CollatzResearch.WordTrace tailWord_6359007 prefixEnd_6359007 3265227076305307089567965 := by
  unfold tailWord_6359007
  simp only [CollatzResearch.WordTrace]
  refine ⟨231932039273411145777291275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154621359515607430518194183 231932039273411145777291275)
  ·
    refine ⟨347898058910116718665936913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231932039273411145777291275 347898058910116718665936913)
    ·
      refine ⟨260923544182587538999452685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 347898058910116718665936913 260923544182587538999452685)
      ·
        refine ⟨97846329068470327124794757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 260923544182587538999452685 97846329068470327124794757)
        ·
          refine ⟨18346186700338186335899017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97846329068470327124794757 18346186700338186335899017)
          ·
            refine ⟨13759640025253639751924263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18346186700338186335899017 13759640025253639751924263)
            ·
              refine ⟨20639460037880459627886395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13759640025253639751924263 20639460037880459627886395)
              ·
                refine ⟨30959190056820689441829593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20639460037880459627886395 30959190056820689441829593)
                ·
                  refine ⟨23219392542615517081372195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30959190056820689441829593 23219392542615517081372195)
                  ·
                    refine ⟨34829088813923275622058293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23219392542615517081372195 34829088813923275622058293)
                    ·
                      refine ⟨3265227076305307089567965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34829088813923275622058293 3265227076305307089567965)
                      ·
                        rfl

theorem cell23_6359007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 1, 2, 1, 5].length) (baseStart_6359007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6359007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6359007 prefixEnd_6359007 := by exact prefixLift 6359007
  have htrace : WordTrace (prefixWord ++ tailWord_6359007) baseStart_6359007 baseEnd_6359007 := by
    simpa [prefixWord, tailWord_6359007, baseEnd_6359007] using wordTrace_append hprefix tailTrace_6359007
  have hstable : (prefixWord ++ tailWord_6359007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6359007).length < 2 ^ (prefixWord ++ tailWord_6359007).sum := by decide
  have hdescent : baseEnd_6359007 < baseStart_6359007 := by decide
  rcases family_descends (prefixWord ++ tailWord_6359007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6359027 : List Nat := [1, 1, 1, 2, 2, 2, 1, 8, 5]
def baseStart_6359027 : Nat := 118140960795 + 6359027 * 2 ^ 59
def prefixEnd_6359027 : Nat := 4983230072969 + 3 ^ 40 * 6359027 * 2
def baseEnd_6359027 : Nat := 362804149546488556813097

theorem tailTrace_6359027 : CollatzResearch.WordTrace tailWord_6359027 prefixEnd_6359027 362804149546488556813097 := by
  unfold tailWord_6359027
  simp only [CollatzResearch.WordTrace]
  refine ⟨231932768733338689193019335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154621845822225792795346223 231932768733338689193019335)
  ·
    refine ⟨347899153100008033789529003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231932768733338689193019335 347899153100008033789529003)
    ·
      refine ⟨521848729650012050684293505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 347899153100008033789529003 521848729650012050684293505)
      ·
        refine ⟨391386547237509038013220129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 521848729650012050684293505 391386547237509038013220129)
        ·
          refine ⟨293539910428131778509915097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 391386547237509038013220129 293539910428131778509915097)
          ·
            refine ⟨220154932821098833882436323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 293539910428131778509915097 220154932821098833882436323)
            ·
              refine ⟨330232399231648250823654485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 220154932821098833882436323 330232399231648250823654485)
              ·
                refine ⟨3869910928495877939339701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 330232399231648250823654485 3869910928495877939339701)
                ·
                  refine ⟨362804149546488556813097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3869910928495877939339701 362804149546488556813097)
                  ·
                    rfl

theorem cell23_6359027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 8, 5].length) (baseStart_6359027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6359027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6359027 prefixEnd_6359027 := by exact prefixLift 6359027
  have htrace : WordTrace (prefixWord ++ tailWord_6359027) baseStart_6359027 baseEnd_6359027 := by
    simpa [prefixWord, tailWord_6359027, baseEnd_6359027] using wordTrace_append hprefix tailTrace_6359027
  have hstable : (prefixWord ++ tailWord_6359027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6359027).length < 2 ^ (prefixWord ++ tailWord_6359027).sum := by decide
  have hdescent : baseEnd_6359027 < baseStart_6359027 := by decide
  rcases family_descends (prefixWord ++ tailWord_6359027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6359037 : List Nat := [1, 4, 1, 1, 1, 2, 2, 3, 2, 3, 3]
def baseStart_6359037 : Nat := 118140960795 + 6359037 * 2 ^ 59
def prefixEnd_6359037 : Nat := 4983230072969 + 3 ^ 40 * 6359037 * 2
def baseEnd_6359037 : Nat := 3265242480724941972192827

theorem tailTrace_6359037 : CollatzResearch.WordTrace tailWord_6359037 prefixEnd_6359037 3265242480724941972192827 := by
  unfold tailWord_6359037
  simp only [CollatzResearch.WordTrace]
  refine ⟨231933133463302460900883365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154622088975534973933922243 231933133463302460900883365)
  ·
    refine ⟨43487462524369211418915631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 231933133463302460900883365 43487462524369211418915631)
    ·
      refine ⟨65231193786553817128373447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43487462524369211418915631 65231193786553817128373447)
      ·
        refine ⟨97846790679830725692560171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65231193786553817128373447 97846790679830725692560171)
        ·
          refine ⟨146770186019746088538840257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97846790679830725692560171 146770186019746088538840257)
          ·
            refine ⟨110077639514809566404130193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146770186019746088538840257 110077639514809566404130193)
            ·
              refine ⟨82558229636107174803097645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110077639514809566404130193 82558229636107174803097645)
              ·
                refine ⟨30959336113540190551161617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82558229636107174803097645 30959336113540190551161617)
                ·
                  refine ⟨23219502085155142913371213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30959336113540190551161617 23219502085155142913371213)
                  ·
                    refine ⟨8707313281933178592514205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23219502085155142913371213 8707313281933178592514205)
                    ·
                      refine ⟨3265242480724941972192827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8707313281933178592514205 3265242480724941972192827)
                      ·
                        rfl

theorem cell23_6359037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 3, 2, 3, 3].length) (baseStart_6359037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6359037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6359037 prefixEnd_6359037 := by exact prefixLift 6359037
  have htrace : WordTrace (prefixWord ++ tailWord_6359037) baseStart_6359037 baseEnd_6359037 := by
    simpa [prefixWord, tailWord_6359037, baseEnd_6359037] using wordTrace_append hprefix tailTrace_6359037
  have hstable : (prefixWord ++ tailWord_6359037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6359037).length < 2 ^ (prefixWord ++ tailWord_6359037).sum := by decide
  have hdescent : baseEnd_6359037 < baseStart_6359037 := by decide
  rcases family_descends (prefixWord ++ tailWord_6359037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6359040 : List Nat := [2, 1, 1, 2, 1, 1, 1, 6, 1, 7]
def baseStart_6359040 : Nat := 118140960795 + 6359040 * 2 ^ 59
def prefixEnd_6359040 : Nat := 4983230072969 + 3 ^ 40 * 6359040 * 2
def baseEnd_6359040 : Nat := 1088414673722301820151771

theorem tailTrace_6359040 : CollatzResearch.WordTrace tailWord_6359040 prefixEnd_6359040 1088414673722301820151771 := by
  unfold tailWord_6359040
  simp only [CollatzResearch.WordTrace]
  refine ⟨115966621441145796206621287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154622161921527728275495049 115966621441145796206621287)
  ·
    refine ⟨173949932161718694309931931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115966621441145796206621287 173949932161718694309931931)
    ·
      refine ⟨260924898242578041464897897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173949932161718694309931931 260924898242578041464897897)
      ·
        refine ⟨195693673681933531098673423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 260924898242578041464897897 195693673681933531098673423)
        ·
          refine ⟨293540510522900296648010135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195693673681933531098673423 293540510522900296648010135)
          ·
            refine ⟨440310765784350444972015203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 293540510522900296648010135 440310765784350444972015203)
            ·
              refine ⟨660466148676525667458022805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 440310765784350444972015203 660466148676525667458022805)
              ·
                refine ⟨30959350719212140662094819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 660466148676525667458022805 30959350719212140662094819)
                ·
                  refine ⟨46439026078818210993142229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30959350719212140662094819 46439026078818210993142229)
                  ·
                    refine ⟨1088414673722301820151771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46439026078818210993142229 1088414673722301820151771)
                    ·
                      rfl

theorem cell23_6359040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 6, 1, 7].length) (baseStart_6359040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6359040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6359040 prefixEnd_6359040 := by exact prefixLift 6359040
  have htrace : WordTrace (prefixWord ++ tailWord_6359040) baseStart_6359040 baseEnd_6359040 := by
    simpa [prefixWord, tailWord_6359040, baseEnd_6359040] using wordTrace_append hprefix tailTrace_6359040
  have hstable : (prefixWord ++ tailWord_6359040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6359040).length < 2 ^ (prefixWord ++ tailWord_6359040).sum := by decide
  have hdescent : baseEnd_6359040 < baseStart_6359040 := by decide
  rcases family_descends (prefixWord ++ tailWord_6359040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6359094 : List Nat := [5, 1, 2, 1, 1, 1, 2, 2, 1, 3, 4]
def baseStart_6359094 : Nat := 118140960795 + 6359094 * 2 ^ 59
def prefixEnd_6359094 : Nat := 4983230072969 + 3 ^ 40 * 6359094 * 2
def baseEnd_6359094 : Nat := 3265271749122248249180065

theorem tailTrace_6359094 : CollatzResearch.WordTrace tailWord_6359094 prefixEnd_6359094 3265271749122248249180065 := by
  unfold tailWord_6359094
  simp only [CollatzResearch.WordTrace]
  refine ⟨14495950776505997477231771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 154623474949397306423805557 14495950776505997477231771)
  ·
    refine ⟨21743926164758996215847657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14495950776505997477231771 21743926164758996215847657)
    ·
      refine ⟨16307944623569247161885743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21743926164758996215847657 16307944623569247161885743)
      ·
        refine ⟨24461916935353870742828615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16307944623569247161885743 24461916935353870742828615)
        ·
          refine ⟨36692875403030806114242923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24461916935353870742828615 36692875403030806114242923)
          ·
            refine ⟨55039313104546209171364385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36692875403030806114242923 55039313104546209171364385)
            ·
              refine ⟨41279484828409656878523289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55039313104546209171364385 41279484828409656878523289)
              ·
                refine ⟨30959613621307242658892467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41279484828409656878523289 30959613621307242658892467)
                ·
                  refine ⟨46439420431960863988338701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30959613621307242658892467 46439420431960863988338701)
                  ·
                    refine ⟨17414782661985323995627013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46439420431960863988338701 17414782661985323995627013)
                    ·
                      refine ⟨3265271749122248249180065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17414782661985323995627013 3265271749122248249180065)
                      ·
                        rfl

theorem cell23_6359094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_6359094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6359094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6359094 prefixEnd_6359094 := by exact prefixLift 6359094
  have htrace : WordTrace (prefixWord ++ tailWord_6359094) baseStart_6359094 baseEnd_6359094 := by
    simpa [prefixWord, tailWord_6359094, baseEnd_6359094] using wordTrace_append hprefix tailTrace_6359094
  have hstable : (prefixWord ++ tailWord_6359094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6359094).length < 2 ^ (prefixWord ++ tailWord_6359094).sum := by decide
  have hdescent : baseEnd_6359094 < baseStart_6359094 := by decide
  rcases family_descends (prefixWord ++ tailWord_6359094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6359104 : List Nat := [2, 1, 1, 2, 2, 5, 1, 2, 3, 4]
def baseStart_6359104 : Nat := 118140960795 + 6359104 * 2 ^ 59
def prefixEnd_6359104 : Nat := 4983230072969 + 3 ^ 40 * 6359104 * 2
def baseEnd_6359104 : Nat := 1088425627976264403351673

theorem tailTrace_6359104 : CollatzResearch.WordTrace tailWord_6359104 prefixEnd_6359104 1088425627976264403351673 := by
  unfold tailWord_6359104
  simp only [CollatzResearch.WordTrace]
  refine ⟨115967788577029865671786183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154623718102706487562381577 115967788577029865671786183)
  ·
    refine ⟨173951682865544798507679275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115967788577029865671786183 173951682865544798507679275)
    ·
      refine ⟨260927524298317197761518913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173951682865544798507679275 260927524298317197761518913)
      ·
        refine ⟨195695643223737898321139185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 260927524298317197761518913 195695643223737898321139185)
        ·
          refine ⟨146771732417803423740854389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 195695643223737898321139185 146771732417803423740854389)
          ·
            refine ⟨13759849914169070975705099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 146771732417803423740854389 13759849914169070975705099)
            ·
              refine ⟨20639774871253606463557649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13759849914169070975705099 20639774871253606463557649)
              ·
                refine ⟨15479831153440204847668237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20639774871253606463557649 15479831153440204847668237)
                ·
                  refine ⟨5804936682540076817875589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15479831153440204847668237 5804936682540076817875589)
                  ·
                    refine ⟨1088425627976264403351673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5804936682540076817875589 1088425627976264403351673)
                    ·
                      rfl

theorem cell23_6359104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 2, 3, 4].length) (baseStart_6359104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6359104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6359104 prefixEnd_6359104 := by exact prefixLift 6359104
  have htrace : WordTrace (prefixWord ++ tailWord_6359104) baseStart_6359104 baseEnd_6359104 := by
    simpa [prefixWord, tailWord_6359104, baseEnd_6359104] using wordTrace_append hprefix tailTrace_6359104
  have hstable : (prefixWord ++ tailWord_6359104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6359104).length < 2 ^ (prefixWord ++ tailWord_6359104).sum := by decide
  have hdescent : baseEnd_6359104 < baseStart_6359104 := by decide
  rcases family_descends (prefixWord ++ tailWord_6359104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6359138 : List Nat := [3, 3, 2, 2, 2, 1, 2, 1, 3, 4]
def baseStart_6359138 : Nat := 118140960795 + 6359138 * 2 ^ 59
def prefixEnd_6359138 : Nat := 4983230072969 + 3 ^ 40 * 6359138 * 2
def baseEnd_6359138 : Nat := 1088431447423682025676621

theorem tailTrace_6359138 : CollatzResearch.WordTrace tailWord_6359138 prefixEnd_6359138 1088431447423682025676621 := by
  unfold tailWord_6359138
  simp only [CollatzResearch.WordTrace]
  refine ⟨57984204308984138787577517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154624544823957703433540045 57984204308984138787577517)
  ·
    refine ⟨21744076615869052045341569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57984204308984138787577517 21744076615869052045341569)
    ·
      refine ⟨16308057461901789034006177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21744076615869052045341569 16308057461901789034006177)
      ·
        refine ⟨12231043096426341775504633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16308057461901789034006177 12231043096426341775504633)
        ·
          refine ⟨9173282322319756331628475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12231043096426341775504633 9173282322319756331628475)
          ·
            refine ⟨13759923483479634497442713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9173282322319756331628475 13759923483479634497442713)
            ·
              refine ⟨10319942612609725873082035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13759923483479634497442713 10319942612609725873082035)
              ·
                refine ⟨15479913918914588809623053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10319942612609725873082035 15479913918914588809623053)
                ·
                  refine ⟨5804967719592970803608645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15479913918914588809623053 5804967719592970803608645)
                  ·
                    refine ⟨1088431447423682025676621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5804967719592970803608645 1088431447423682025676621)
                    ·
                      rfl

theorem cell23_6359138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 1, 3, 4].length) (baseStart_6359138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6359138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6359138 prefixEnd_6359138 := by exact prefixLift 6359138
  have htrace : WordTrace (prefixWord ++ tailWord_6359138) baseStart_6359138 baseEnd_6359138 := by
    simpa [prefixWord, tailWord_6359138, baseEnd_6359138] using wordTrace_append hprefix tailTrace_6359138
  have hstable : (prefixWord ++ tailWord_6359138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6359138).length < 2 ^ (prefixWord ++ tailWord_6359138).sum := by decide
  have hdescent : baseEnd_6359138 < baseStart_6359138 := by decide
  rcases family_descends (prefixWord ++ tailWord_6359138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6359161 : List Nat := [1, 2, 1, 3, 4, 1, 2, 2, 3, 1, 3]
def baseStart_6359161 : Nat := 118140960795 + 6359161 * 2 ^ 59
def prefixEnd_6359161 : Nat := 4983230072969 + 3 ^ 40 * 6359161 * 2
def baseEnd_6359161 : Nat := 3265306152326099487042257

theorem tailTrace_6359161 : CollatzResearch.WordTrace tailWord_6359161 prefixEnd_6359161 3265306152326099487042257 := by
  unfold tailWord_6359161
  simp only [CollatzResearch.WordTrace]
  refine ⟨231937656114853230078397337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154625104076568820052264891 231937656114853230078397337)
  ·
    refine ⟨173953242086139922558798003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231937656114853230078397337 173953242086139922558798003)
    ·
      refine ⟨260929863129209883838197005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173953242086139922558798003 260929863129209883838197005)
      ·
        refine ⟨97848698673453706439323877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 260929863129209883838197005 97848698673453706439323877)
        ·
          refine ⟨18346631001272569957373227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97848698673453706439323877 18346631001272569957373227)
          ·
            refine ⟨27519946501908854936059841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18346631001272569957373227 27519946501908854936059841)
            ·
              refine ⟨20639959876431641202044881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27519946501908854936059841 20639959876431641202044881)
              ·
                refine ⟨15479969907323730901533661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20639959876431641202044881 15479969907323730901533661)
                ·
                  refine ⟨5804988715246399088075123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15479969907323730901533661 5804988715246399088075123)
                  ·
                    refine ⟨8707483072869598632112685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5804988715246399088075123 8707483072869598632112685)
                    ·
                      refine ⟨3265306152326099487042257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8707483072869598632112685 3265306152326099487042257)
                      ·
                        rfl

theorem cell23_6359161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 2, 3, 1, 3].length) (baseStart_6359161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6359161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6359161 prefixEnd_6359161 := by exact prefixLift 6359161
  have htrace : WordTrace (prefixWord ++ tailWord_6359161) baseStart_6359161 baseEnd_6359161 := by
    simpa [prefixWord, tailWord_6359161, baseEnd_6359161] using wordTrace_append hprefix tailTrace_6359161
  have hstable : (prefixWord ++ tailWord_6359161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6359161).length < 2 ^ (prefixWord ++ tailWord_6359161).sum := by decide
  have hdescent : baseEnd_6359161 < baseStart_6359161 := by decide
  rcases family_descends (prefixWord ++ tailWord_6359161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6359164 : List Nat := [2, 2, 2, 1, 1, 4, 1, 4, 1, 5]
def baseStart_6359164 : Nat := 118140960795 + 6359164 * 2 ^ 59
def prefixEnd_6359164 : Nat := 4983230072969 + 3 ^ 40 * 6359164 * 2
def baseEnd_6359164 : Nat := 1088435897589354325101581

theorem tailTrace_6359164 : CollatzResearch.WordTrace tailWord_6359164 prefixEnd_6359164 1088435897589354325101581 := by
  unfold tailWord_6359164
  simp only [CollatzResearch.WordTrace]
  refine ⟨115968882766921180795378273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154625177022561574393837697 115968882766921180795378273)
  ·
    refine ⟨86976662075190885596533705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115968882766921180795378273 86976662075190885596533705)
    ·
      refine ⟨65232496556393164197400279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86976662075190885596533705 65232496556393164197400279)
      ·
        refine ⟨97848744834589746296100419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65232496556393164197400279 97848744834589746296100419)
        ·
          refine ⟨146773117251884619444150629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97848744834589746296100419 146773117251884619444150629)
          ·
            refine ⟨27519959484728366145778243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 146773117251884619444150629 27519959484728366145778243)
            ·
              refine ⟨41279939227092549218667365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27519959484728366145778243 41279939227092549218667365)
              ·
                refine ⟨7739988605079852978500131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41279939227092549218667365 7739988605079852978500131)
                ·
                  refine ⟨11609982907619779467750197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7739988605079852978500131 11609982907619779467750197)
                  ·
                    refine ⟨1088435897589354325101581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11609982907619779467750197 1088435897589354325101581)
                    ·
                      rfl

theorem cell23_6359164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 4, 1, 5].length) (baseStart_6359164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6359164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6359164 prefixEnd_6359164 := by exact prefixLift 6359164
  have htrace : WordTrace (prefixWord ++ tailWord_6359164) baseStart_6359164 baseEnd_6359164 := by
    simpa [prefixWord, tailWord_6359164, baseEnd_6359164] using wordTrace_append hprefix tailTrace_6359164
  have hstable : (prefixWord ++ tailWord_6359164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6359164).length < 2 ^ (prefixWord ++ tailWord_6359164).sum := by decide
  have hdescent : baseEnd_6359164 < baseStart_6359164 := by decide
  rcases family_descends (prefixWord ++ tailWord_6359164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6359177 : List Nat := [1, 2, 1, 1, 4, 2, 2, 1, 3, 6]
def baseStart_6359177 : Nat := 118140960795 + 6359177 * 2 ^ 59
def prefixEnd_6359177 : Nat := 4983230072969 + 3 ^ 40 * 6359177 * 2
def baseEnd_6359177 : Nat := 1088438122672190474814061

theorem tailTrace_6359177 : CollatzResearch.WordTrace tailWord_6359177 prefixEnd_6359177 1088438122672190474814061 := by
  unfold tailWord_6359177
  simp only [CollatzResearch.WordTrace]
  refine ⟨231938239682795264810979785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154625493121863509873986523 231938239682795264810979785)
  ·
    refine ⟨173953679762096448608234839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231938239682795264810979785 173953679762096448608234839)
    ·
      refine ⟨260930519643144672912352259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173953679762096448608234839 260930519643144672912352259)
      ·
        refine ⟨391395779464717009368528389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260930519643144672912352259 391395779464717009368528389)
        ·
          refine ⟨73386708649634439256599073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 391395779464717009368528389 73386708649634439256599073)
          ·
            refine ⟨55040031487225829442449305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73386708649634439256599073 55040031487225829442449305)
            ·
              refine ⟨41280023615419372081836979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55040031487225829442449305 41280023615419372081836979)
              ·
                refine ⟨61920035423129058122755469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41280023615419372081836979 61920035423129058122755469)
                ·
                  refine ⟨23220013283673396796033301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61920035423129058122755469 23220013283673396796033301)
                  ·
                    refine ⟨1088438122672190474814061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23220013283673396796033301 1088438122672190474814061)
                    ·
                      rfl

theorem cell23_6359177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 1, 3, 6].length) (baseStart_6359177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6359177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6359177 prefixEnd_6359177 := by exact prefixLift 6359177
  have htrace : WordTrace (prefixWord ++ tailWord_6359177) baseStart_6359177 baseEnd_6359177 := by
    simpa [prefixWord, tailWord_6359177, baseEnd_6359177] using wordTrace_append hprefix tailTrace_6359177
  have hstable : (prefixWord ++ tailWord_6359177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6359177).length < 2 ^ (prefixWord ++ tailWord_6359177).sum := by decide
  have hdescent : baseEnd_6359177 < baseStart_6359177 := by decide
  rcases family_descends (prefixWord ++ tailWord_6359177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6359184 : List Nat := [2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 4]
def baseStart_6359184 : Nat := 118140960795 + 6359184 * 2 ^ 59
def prefixEnd_6359184 : Nat := 4983230072969 + 3 ^ 40 * 6359184 * 2
def baseEnd_6359184 : Nat := 3265317962381152897054651

theorem tailTrace_6359184 : CollatzResearch.WordTrace tailWord_6359184 prefixEnd_6359184 3265317962381152897054651 := by
  unfold tailWord_6359184
  simp only [CollatzResearch.WordTrace]
  refine ⟨115969247496884952503242303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154625663329179936670989737 115969247496884952503242303)
  ·
    refine ⟨173953871245327428754863455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115969247496884952503242303 173953871245327428754863455)
    ·
      refine ⟨260930806867991143132295183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173953871245327428754863455 260930806867991143132295183)
      ·
        refine ⟨391396210301986714698442775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260930806867991143132295183 391396210301986714698442775)
        ·
          refine ⟨587094315452980072047664163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 391396210301986714698442775 587094315452980072047664163)
          ·
            refine ⟨880641473179470108071496245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 587094315452980072047664163 880641473179470108071496245)
            ·
              refine ⟨82560138110575322631702773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 880641473179470108071496245 82560138110575322631702773)
              ·
                refine ⟨7740012947866436496722135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 82560138110575322631702773 7740012947866436496722135)
                ·
                  refine ⟨11610019421799654745083203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7740012947866436496722135 11610019421799654745083203)
                  ·
                    refine ⟨17415029132699482117624805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11610019421799654745083203 17415029132699482117624805)
                    ·
                      refine ⟨3265317962381152897054651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17415029132699482117624805 3265317962381152897054651)
                      ·
                        rfl

theorem cell23_6359184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 4].length) (baseStart_6359184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6359184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6359184 prefixEnd_6359184 := by exact prefixLift 6359184
  have htrace : WordTrace (prefixWord ++ tailWord_6359184) baseStart_6359184 baseEnd_6359184 := by
    simpa [prefixWord, tailWord_6359184, baseEnd_6359184] using wordTrace_append hprefix tailTrace_6359184
  have hstable : (prefixWord ++ tailWord_6359184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6359184).length < 2 ^ (prefixWord ++ tailWord_6359184).sum := by decide
  have hdescent : baseEnd_6359184 < baseStart_6359184 := by decide
  rcases family_descends (prefixWord ++ tailWord_6359184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6359274 : List Nat := [3, 1, 3, 1, 1, 2, 1, 2, 2, 3, 4]
def baseStart_6359274 : Nat := 118140960795 + 6359274 * 2 ^ 59
def prefixEnd_6359274 : Nat := 4983230072969 + 3 ^ 40 * 6359274 * 2
def baseEnd_6359274 : Nat := 3265364175640057544929237

theorem tailTrace_6359274 : CollatzResearch.WordTrace tailWord_6359274 prefixEnd_6359274 3265364175640057544929237 := by
  unfold tailWord_6359274
  simp only [CollatzResearch.WordTrace]
  refine ⟨57985444390860962594315219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154627851708962566918173917 57985444390860962594315219)
  ·
    refine ⟨86978166586291443891472829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57985444390860962594315219 86978166586291443891472829)
    ·
      refine ⟨32616812469859291459302311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86978166586291443891472829 32616812469859291459302311)
      ·
        refine ⟨48925218704788937188953467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32616812469859291459302311 48925218704788937188953467)
        ·
          refine ⟨73387828057183405783430201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48925218704788937188953467 73387828057183405783430201)
          ·
            refine ⟨55040871042887554337572651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73387828057183405783430201 55040871042887554337572651)
            ·
              refine ⟨82561306564331331506358977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55040871042887554337572651 82561306564331331506358977)
              ·
                refine ⟨61920979923248498629769233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82561306564331331506358977 61920979923248498629769233)
                ·
                  refine ⟨46440734942436373972326925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61920979923248498629769233 46440734942436373972326925)
                  ·
                    refine ⟨17415275603413640239622597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46440734942436373972326925 17415275603413640239622597)
                    ·
                      refine ⟨3265364175640057544929237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17415275603413640239622597 3265364175640057544929237)
                      ·
                        rfl

theorem cell23_6359274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 2, 2, 3, 4].length) (baseStart_6359274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6359274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6359274 prefixEnd_6359274 := by exact prefixLift 6359274
  have htrace : WordTrace (prefixWord ++ tailWord_6359274) baseStart_6359274 baseEnd_6359274 := by
    simpa [prefixWord, tailWord_6359274, baseEnd_6359274] using wordTrace_append hprefix tailTrace_6359274
  have hstable : (prefixWord ++ tailWord_6359274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6359274).length < 2 ^ (prefixWord ++ tailWord_6359274).sum := by decide
  have hdescent : baseEnd_6359274 < baseStart_6359274 := by decide
  rcases family_descends (prefixWord ++ tailWord_6359274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6359278 : List Nat := [4, 1, 2, 1, 1, 1, 1, 6, 1, 3, 2]
def baseStart_6359278 : Nat := 118140960795 + 6359278 * 2 ^ 59
def prefixEnd_6359278 : Nat := 4983230072969 + 3 ^ 40 * 6359278 * 2
def baseEnd_6359278 : Nat := 3265366229562675529279219

theorem tailTrace_6359278 : CollatzResearch.WordTrace tailWord_6359278 prefixEnd_6359278 3265366229562675529279219 := by
  unfold tailWord_6359278
  simp only [CollatzResearch.WordTrace]
  refine ⟨28992740431928669882550811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154627948970286239373604325 28992740431928669882550811)
  ·
    refine ⟨43489110647893004823826217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28992740431928669882550811 43489110647893004823826217)
    ·
      refine ⟨32616832985919753617869663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43489110647893004823826217 32616832985919753617869663)
      ·
        refine ⟨48925249478879630426804495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32616832985919753617869663 48925249478879630426804495)
        ·
          refine ⟨73387874218319445640206743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48925249478879630426804495 73387874218319445640206743)
          ·
            refine ⟨110081811327479168460310115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73387874218319445640206743 110081811327479168460310115)
            ·
              refine ⟨165122716991218752690465173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110081811327479168460310115 165122716991218752690465173)
              ·
                refine ⟨7740127358963379032365555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 165122716991218752690465173 7740127358963379032365555)
                ·
                  refine ⟨11610191038445068548548333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7740127358963379032365555 11610191038445068548548333)
                  ·
                    refine ⟨4353821639416900705705625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11610191038445068548548333 4353821639416900705705625)
                    ·
                      refine ⟨3265366229562675529279219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4353821639416900705705625 3265366229562675529279219)
                      ·
                        rfl

theorem cell23_6359278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 6, 1, 3, 2].length) (baseStart_6359278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6359278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6359278 prefixEnd_6359278 := by exact prefixLift 6359278
  have htrace : WordTrace (prefixWord ++ tailWord_6359278) baseStart_6359278 baseEnd_6359278 := by
    simpa [prefixWord, tailWord_6359278, baseEnd_6359278] using wordTrace_append hprefix tailTrace_6359278
  have hstable : (prefixWord ++ tailWord_6359278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6359278).length < 2 ^ (prefixWord ++ tailWord_6359278).sum := by decide
  have hdescent : baseEnd_6359278 < baseStart_6359278 := by decide
  rcases family_descends (prefixWord ++ tailWord_6359278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6359308 : List Nat := [2, 2, 1, 2, 2, 2, 3, 1, 4, 2, 2]
def baseStart_6359308 : Nat := 118140960795 + 6359308 * 2 ^ 59
def prefixEnd_6359308 : Nat := 4983230072969 + 3 ^ 40 * 6359308 * 2
def baseEnd_6359308 : Nat := 3265381633982310411904081

theorem tailTrace_6359308 : CollatzResearch.WordTrace tailWord_6359308 prefixEnd_6359308 3265381633982310411904081 := by
  unfold tailWord_6359308
  simp only [CollatzResearch.WordTrace]
  refine ⟨115971508822660337091999289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154628678430213782789332385 115971508822660337091999289)
  ·
    refine ⟨86978631616995252818999467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115971508822660337091999289 86978631616995252818999467)
    ·
      refine ⟨130467947425492879228499201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86978631616995252818999467 130467947425492879228499201)
      ·
        refine ⟨97850960569119659421374401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130467947425492879228499201 97850960569119659421374401)
        ·
          refine ⟨73388220426839744566030801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97850960569119659421374401 73388220426839744566030801)
          ·
            refine ⟨55041165320129808424523101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73388220426839744566030801 55041165320129808424523101)
            ·
              refine ⟨20640436995048678159196163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55041165320129808424523101 20640436995048678159196163)
              ·
                refine ⟨30960655492573017238794245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20640436995048678159196163 30960655492573017238794245)
                ·
                  refine ⟨5805122904857440732273921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30960655492573017238794245 5805122904857440732273921)
                  ·
                    refine ⟨4353842178643080549205441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5805122904857440732273921 4353842178643080549205441)
                    ·
                      refine ⟨3265381633982310411904081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4353842178643080549205441 3265381633982310411904081)
                      ·
                        rfl

theorem cell23_6359308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 1, 4, 2, 2].length) (baseStart_6359308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6359308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6359308 prefixEnd_6359308 := by exact prefixLift 6359308
  have htrace : WordTrace (prefixWord ++ tailWord_6359308) baseStart_6359308 baseEnd_6359308 := by
    simpa [prefixWord, tailWord_6359308, baseEnd_6359308] using wordTrace_append hprefix tailTrace_6359308
  have hstable : (prefixWord ++ tailWord_6359308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6359308).length < 2 ^ (prefixWord ++ tailWord_6359308).sum := by decide
  have hdescent : baseEnd_6359308 < baseStart_6359308 := by decide
  rcases family_descends (prefixWord ++ tailWord_6359308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6359374 : List Nat := [4, 1, 1, 1, 1, 1, 2, 2, 2, 8]
def baseStart_6359374 : Nat := 118140960795 + 6359374 * 2 ^ 59
def prefixEnd_6359374 : Nat := 4983230072969 + 3 ^ 40 * 6359374 * 2
def baseEnd_6359374 : Nat := 1088471841235169051226259

theorem tailTrace_6359374 : CollatzResearch.WordTrace tailWord_6359374 prefixEnd_6359374 1088471841235169051226259 := by
  unfold tailWord_6359374
  simp only [CollatzResearch.WordTrace]
  refine ⟨28993178107885195931987647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154630283242054378303934117 28993178107885195931987647)
  ·
    refine ⟨43489767161827793897981471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28993178107885195931987647 43489767161827793897981471)
    ·
      refine ⟨65234650742741690846972207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43489767161827793897981471 65234650742741690846972207)
      ·
        refine ⟨97851976114112536270458311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65234650742741690846972207 97851976114112536270458311)
        ·
          refine ⟨146777964171168804405687467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97851976114112536270458311 146777964171168804405687467)
          ·
            refine ⟨220166946256753206608531201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146777964171168804405687467 220166946256753206608531201)
            ·
              refine ⟨165125209692564904956398401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 220166946256753206608531201 165125209692564904956398401)
              ·
                refine ⟨123843907269423678717298801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 165125209692564904956398401 123843907269423678717298801)
                ·
                  refine ⟨92882930452067759037974101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 123843907269423678717298801 92882930452067759037974101)
                  ·
                    refine ⟨1088471841235169051226259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 92882930452067759037974101 1088471841235169051226259)
                    ·
                      rfl

theorem cell23_6359374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 2, 8].length) (baseStart_6359374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6359374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6359374 prefixEnd_6359374 := by exact prefixLift 6359374
  have htrace : WordTrace (prefixWord ++ tailWord_6359374) baseStart_6359374 baseEnd_6359374 := by
    simpa [prefixWord, tailWord_6359374, baseEnd_6359374] using wordTrace_append hprefix tailTrace_6359374
  have hstable : (prefixWord ++ tailWord_6359374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6359374).length < 2 ^ (prefixWord ++ tailWord_6359374).sum := by decide
  have hdescent : baseEnd_6359374 < baseStart_6359374 := by decide
  rcases family_descends (prefixWord ++ tailWord_6359374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6359391 : List Nat := [1, 1, 2, 3, 1, 2, 2, 4, 3, 4]
def baseStart_6359391 : Nat := 118140960795 + 6359391 * 2 ^ 59
def prefixEnd_6359391 : Nat := 4983230072969 + 3 ^ 40 * 6359391 * 2
def baseEnd_6359391 : Nat := 1088474750958877862388733

theorem tailTrace_6359391 : CollatzResearch.WordTrace tailWord_6359391 prefixEnd_6359391 1088474750958877862388733 := by
  unfold tailWord_6359391
  simp only [CollatzResearch.WordTrace]
  refine ⟨231946044904019979359270027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154630696602679986239513351 231946044904019979359270027)
  ·
    refine ⟨347919067356029969038905041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231946044904019979359270027 347919067356029969038905041)
    ·
      refine ⟨260939300517022476779178781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 347919067356029969038905041 260939300517022476779178781)
      ·
        refine ⟨97852237693883428792192043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 260939300517022476779178781 97852237693883428792192043)
        ·
          refine ⟨146778356540825143188288065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97852237693883428792192043 146778356540825143188288065)
          ·
            refine ⟨110083767405618857391216049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146778356540825143188288065 110083767405618857391216049)
            ·
              refine ⟨82562825554214143043412037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110083767405618857391216049 82562825554214143043412037)
              ·
                refine ⟨15480529791415151820639757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82562825554214143043412037 15480529791415151820639757)
                ·
                  refine ⟨5805198671780681932739909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15480529791415151820639757 5805198671780681932739909)
                  ·
                    refine ⟨1088474750958877862388733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5805198671780681932739909 1088474750958877862388733)
                    ·
                      rfl

theorem cell23_6359391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 4, 3, 4].length) (baseStart_6359391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6359391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6359391 prefixEnd_6359391 := by exact prefixLift 6359391
  have htrace : WordTrace (prefixWord ++ tailWord_6359391) baseStart_6359391 baseEnd_6359391 := by
    simpa [prefixWord, tailWord_6359391, baseEnd_6359391] using wordTrace_append hprefix tailTrace_6359391
  have hstable : (prefixWord ++ tailWord_6359391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6359391).length < 2 ^ (prefixWord ++ tailWord_6359391).sum := by decide
  have hdescent : baseEnd_6359391 < baseStart_6359391 := by decide
  rcases family_descends (prefixWord ++ tailWord_6359391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6359421 : List Nat := [1, 4, 1, 1, 2, 3, 1, 4, 6]
def baseStart_6359421 : Nat := 118140960795 + 6359421 * 2 ^ 59
def prefixEnd_6359421 : Nat := 4983230072969 + 3 ^ 40 * 6359421 * 2
def baseEnd_6359421 : Nat := 362826628588474274421229

theorem tailTrace_6359421 : CollatzResearch.WordTrace tailWord_6359421 prefixEnd_6359421 362826628588474274421229 := by
  unfold tailWord_6359421
  simp only [CollatzResearch.WordTrace]
  refine ⟨231947139093911294482862117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154631426062607529655241411 231947139093911294482862117)
  ·
    refine ⟨43490088580108367715536647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 231947139093911294482862117 43490088580108367715536647)
    ·
      refine ⟨65235132870162551573304971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43490088580108367715536647 65235132870162551573304971)
      ·
        refine ⟨97852699305243827359957457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65235132870162551573304971 97852699305243827359957457)
        ·
          refine ⟨73389524478932870519968093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97852699305243827359957457 73389524478932870519968093)
          ·
            refine ⟨27521071679599826444988035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73389524478932870519968093 27521071679599826444988035)
            ·
              refine ⟨41281607519399739667482053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27521071679599826444988035 41281607519399739667482053)
              ·
                refine ⟨7740301409887451187652885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41281607519399739667482053 7740301409887451187652885)
                ·
                  refine ⟨362826628588474274421229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7740301409887451187652885 362826628588474274421229)
                  ·
                    rfl

theorem cell23_6359421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 4, 6].length) (baseStart_6359421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6359421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6359421 prefixEnd_6359421 := by exact prefixLift 6359421
  have htrace : WordTrace (prefixWord ++ tailWord_6359421) baseStart_6359421 baseEnd_6359421 := by
    simpa [prefixWord, tailWord_6359421, baseEnd_6359421] using wordTrace_append hprefix tailTrace_6359421
  have hstable : (prefixWord ++ tailWord_6359421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6359421).length < 2 ^ (prefixWord ++ tailWord_6359421).sum := by decide
  have hdescent : baseEnd_6359421 < baseStart_6359421 := by decide
  rcases family_descends (prefixWord ++ tailWord_6359421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6359438 : List Nat := [4, 1, 1, 4, 1, 1, 2, 3, 6]
def baseStart_6359438 : Nat := 118140960795 + 6359438 * 2 ^ 59
def prefixEnd_6359438 : Nat := 4983230072969 + 3 ^ 40 * 6359438 * 2
def baseEnd_6359438 : Nat := 362827598496377211475387

theorem tailTrace_6359438 : CollatzResearch.WordTrace tailWord_6359438 prefixEnd_6359438 362827598496377211475387 := by
  unfold tailWord_6359438
  simp only [CollatzResearch.WordTrace]
  refine ⟨28993469891856213298278871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154631839423233137590820645 28993469891856213298278871)
  ·
    refine ⟨43490204837784319947418307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28993469891856213298278871 43490204837784319947418307)
    ·
      refine ⟨65235307256676479921127461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43490204837784319947418307 65235307256676479921127461)
      ·
        refine ⟨12231620110626839985211399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65235307256676479921127461 12231620110626839985211399)
        ·
          refine ⟨18347430165940259977817099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12231620110626839985211399 18347430165940259977817099)
          ·
            refine ⟨27521145248910389966725649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18347430165940259977817099 27521145248910389966725649)
            ·
              refine ⟨20640858936682792475044237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27521145248910389966725649 20640858936682792475044237)
              ·
                refine ⟨7740322101256047178141589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20640858936682792475044237 7740322101256047178141589)
                ·
                  refine ⟨362827598496377211475387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7740322101256047178141589 362827598496377211475387)
                  ·
                    rfl

theorem cell23_6359438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 3, 6].length) (baseStart_6359438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6359438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6359438 prefixEnd_6359438 := by exact prefixLift 6359438
  have htrace : WordTrace (prefixWord ++ tailWord_6359438) baseStart_6359438 baseEnd_6359438 := by
    simpa [prefixWord, tailWord_6359438, baseEnd_6359438] using wordTrace_append hprefix tailTrace_6359438
  have hstable : (prefixWord ++ tailWord_6359438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6359438).length < 2 ^ (prefixWord ++ tailWord_6359438).sum := by decide
  have hdescent : baseEnd_6359438 < baseStart_6359438 := by decide
  rcases family_descends (prefixWord ++ tailWord_6359438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6359446 : List Nat := [5, 3, 1, 2, 2, 1, 1, 1, 2, 5]
def baseStart_6359446 : Nat := 118140960795 + 6359446 * 2 ^ 59
def prefixEnd_6359446 : Nat := 4983230072969 + 3 ^ 40 * 6359446 * 2
def baseEnd_6359446 : Nat := 1088484164770876957326149

theorem tailTrace_6359446 : CollatzResearch.WordTrace tailWord_6359446 prefixEnd_6359446 1088484164770876957326149 := by
  unfold tailWord_6359446
  simp only [CollatzResearch.WordTrace]
  refine ⟨14496753182426295234532637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 154632033945880482501681461 14496753182426295234532637)
  ·
    refine ⟨5436282443409860712949739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14496753182426295234532637 5436282443409860712949739)
    ·
      refine ⟨8154423665114791069424609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5436282443409860712949739 8154423665114791069424609)
      ·
        refine ⟨6115817748836093302068457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8154423665114791069424609 6115817748836093302068457)
        ·
          refine ⟨4586863311627069976551343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6115817748836093302068457 4586863311627069976551343)
          ·
            refine ⟨6880294967440604964827015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4586863311627069976551343 6880294967440604964827015)
            ·
              refine ⟨10320442451160907447240523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6880294967440604964827015 10320442451160907447240523)
              ·
                refine ⟨15480663676741361170860785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10320442451160907447240523 15480663676741361170860785)
                ·
                  refine ⟨11610497757556020878145589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15480663676741361170860785 11610497757556020878145589)
                  ·
                    refine ⟨1088484164770876957326149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11610497757556020878145589 1088484164770876957326149)
                    ·
                      rfl

theorem cell23_6359446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_6359446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6359446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6359446 prefixEnd_6359446 := by exact prefixLift 6359446
  have htrace : WordTrace (prefixWord ++ tailWord_6359446) baseStart_6359446 baseEnd_6359446 := by
    simpa [prefixWord, tailWord_6359446, baseEnd_6359446] using wordTrace_append hprefix tailTrace_6359446
  have hstable : (prefixWord ++ tailWord_6359446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6359446).length < 2 ^ (prefixWord ++ tailWord_6359446).sum := by decide
  have hdescent : baseEnd_6359446 < baseStart_6359446 := by decide
  rcases family_descends (prefixWord ++ tailWord_6359446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6359489 : List Nat := [1, 2, 7, 1, 1, 1, 3, 1, 6]
def baseStart_6359489 : Nat := 118140960795 + 6359489 * 2 ^ 59
def prefixEnd_6359489 : Nat := 4983230072969 + 3 ^ 40 * 6359489 * 2
def baseEnd_6359489 : Nat := 362830508220086022637861

theorem tailTrace_6359489 : CollatzResearch.WordTrace tailWord_6359489 prefixEnd_6359489 362830508220086022637861 := by
  unfold tailWord_6359489
  simp only [CollatzResearch.WordTrace]
  refine ⟨231949619257664942096337521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154633079505109961397558347 231949619257664942096337521)
  ·
    refine ⟨173962214443248706572253141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231949619257664942096337521 173962214443248706572253141)
    ·
      refine ⟨4077239401013641560287183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 173962214443248706572253141 4077239401013641560287183)
      ·
        refine ⟨6115859101520462340430775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4077239401013641560287183 6115859101520462340430775)
        ·
          refine ⟨9173788652280693510646163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6115859101520462340430775 9173788652280693510646163)
          ·
            refine ⟨13760682978421040265969245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9173788652280693510646163 13760682978421040265969245)
            ·
              refine ⟨5160256116907890099738467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13760682978421040265969245 5160256116907890099738467)
              ·
                refine ⟨7740384175361835149607701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5160256116907890099738467 7740384175361835149607701)
                ·
                  refine ⟨362830508220086022637861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7740384175361835149607701 362830508220086022637861)
                  ·
                    rfl

theorem cell23_6359489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 3, 1, 6].length) (baseStart_6359489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6359489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6359489 prefixEnd_6359489 := by exact prefixLift 6359489
  have htrace : WordTrace (prefixWord ++ tailWord_6359489) baseStart_6359489 baseEnd_6359489 := by
    simpa [prefixWord, tailWord_6359489, baseEnd_6359489] using wordTrace_append hprefix tailTrace_6359489
  have hstable : (prefixWord ++ tailWord_6359489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6359489).length < 2 ^ (prefixWord ++ tailWord_6359489).sum := by decide
  have hdescent : baseEnd_6359489 < baseStart_6359489 := by decide
  rcases family_descends (prefixWord ++ tailWord_6359489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6359525 : List Nat := [1, 3, 1, 5, 2, 1, 2, 1, 1, 1, 5]
def baseStart_6359525 : Nat := 118140960795 + 6359525 * 2 ^ 59
def prefixEnd_6359525 : Nat := 4983230072969 + 3 ^ 40 * 6359525 * 2
def baseEnd_6359525 : Nat := 3265493059284336062890583

theorem tailTrace_6359525 : CollatzResearch.WordTrace tailWord_6359525 prefixEnd_6359525 3265493059284336062890583 := by
  unfold tailWord_6359525
  simp only [CollatzResearch.WordTrace]
  refine ⟨231950932285534520244648029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154633954857023013496432019 231950932285534520244648029)
  ·
    refine ⟨86981599607075445091743011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 231950932285534520244648029 86981599607075445091743011)
    ·
      refine ⟨130472399410613167637614517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86981599607075445091743011 130472399410613167637614517)
      ·
        refine ⟨12231787444744984466026361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 130472399410613167637614517 12231787444744984466026361)
        ·
          refine ⟨9173840583558738349519771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12231787444744984466026361 9173840583558738349519771)
          ·
            refine ⟨13760760875338107524279657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9173840583558738349519771 13760760875338107524279657)
            ·
              refine ⟨10320570656503580643209743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13760760875338107524279657 10320570656503580643209743)
              ·
                refine ⟨15480855984755370964814615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10320570656503580643209743 15480855984755370964814615)
                ·
                  refine ⟨23221283977133056447221923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15480855984755370964814615 23221283977133056447221923)
                  ·
                    refine ⟨34831925965699584670832885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23221283977133056447221923 34831925965699584670832885)
                    ·
                      refine ⟨3265493059284336062890583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34831925965699584670832885 3265493059284336062890583)
                      ·
                        rfl

theorem cell23_6359525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_6359525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6359525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6359525 prefixEnd_6359525 := by exact prefixLift 6359525
  have htrace : WordTrace (prefixWord ++ tailWord_6359525) baseStart_6359525 baseEnd_6359525 := by
    simpa [prefixWord, tailWord_6359525, baseEnd_6359525] using wordTrace_append hprefix tailTrace_6359525
  have hstable : (prefixWord ++ tailWord_6359525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6359525).length < 2 ^ (prefixWord ++ tailWord_6359525).sum := by decide
  have hdescent : baseEnd_6359525 < baseStart_6359525 := by decide
  rcases family_descends (prefixWord ++ tailWord_6359525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6359539 : List Nat := [1, 1, 1, 2, 2, 2, 7, 2, 1, 2, 2]
def baseStart_6359539 : Nat := 118140960795 + 6359539 * 2 ^ 59
def prefixEnd_6359539 : Nat := 4983230072969 + 3 ^ 40 * 6359539 * 2
def baseEnd_6359539 : Nat := 3265500248013499008115519

theorem tailTrace_6359539 : CollatzResearch.WordTrace tailWord_6359539 prefixEnd_6359539 3265500248013499008115519 := by
  unfold tailWord_6359539
  simp only [CollatzResearch.WordTrace]
  refine ⟨231951442907483800635657671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154634295271655867090438447 231951442907483800635657671)
  ·
    refine ⟨347927164361225700953486507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231951442907483800635657671 347927164361225700953486507)
    ·
      refine ⟨521890746541838551430229761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 347927164361225700953486507 521890746541838551430229761)
      ·
        refine ⟨391418059906378913572672321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 521890746541838551430229761 391418059906378913572672321)
        ·
          refine ⟨293563544929784185179504241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 391418059906378913572672321 293563544929784185179504241)
          ·
            refine ⟨220172658697338138884628181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 293563544929784185179504241 220172658697338138884628181)
            ·
              refine ⟨5160296688218862630108473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 220172658697338138884628181 5160296688218862630108473)
              ·
                refine ⟨3870222516164146972581355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5160296688218862630108473 3870222516164146972581355)
                ·
                  refine ⟨5805333774246220458872033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3870222516164146972581355 5805333774246220458872033)
                  ·
                    refine ⟨4354000330684665344154025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5805333774246220458872033 4354000330684665344154025)
                    ·
                      refine ⟨3265500248013499008115519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4354000330684665344154025 3265500248013499008115519)
                      ·
                        rfl

theorem cell23_6359539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 7, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 7, 2, 1, 2, 2].length) (baseStart_6359539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6359539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6359539 prefixEnd_6359539 := by exact prefixLift 6359539
  have htrace : WordTrace (prefixWord ++ tailWord_6359539) baseStart_6359539 baseEnd_6359539 := by
    simpa [prefixWord, tailWord_6359539, baseEnd_6359539] using wordTrace_append hprefix tailTrace_6359539
  have hstable : (prefixWord ++ tailWord_6359539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6359539).length < 2 ^ (prefixWord ++ tailWord_6359539).sum := by decide
  have hdescent : baseEnd_6359539 < baseStart_6359539 := by decide
  rcases family_descends (prefixWord ++ tailWord_6359539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6359548 : List Nat := [2, 2, 2, 1, 2, 1, 1, 1, 2, 7, 2]
def baseStart_6359548 : Nat := 118140960795 + 6359548 * 2 ^ 59
def prefixEnd_6359548 : Nat := 4983230072969 + 3 ^ 40 * 6359548 * 2
def baseEnd_6359548 : Nat := 3265504869339389472902977

theorem tailTrace_6359548 : CollatzResearch.WordTrace tailWord_6359548 prefixEnd_6359548 3265504869339389472902977 := by
  unfold tailWord_6359548
  simp only [CollatzResearch.WordTrace]
  refine ⟨115975885582225597586367649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154634514109634130115156865 115975885582225597586367649)
  ·
    refine ⟨86981914186669198189775737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115975885582225597586367649 86981914186669198189775737)
    ·
      refine ⟨65236435640001898642331803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86981914186669198189775737 65236435640001898642331803)
      ·
        refine ⟨97854653460002847963497705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65236435640001898642331803 97854653460002847963497705)
        ·
          refine ⟨73390990095002135972623279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97854653460002847963497705 73390990095002135972623279)
          ·
            refine ⟨110086485142503203958934919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73390990095002135972623279 110086485142503203958934919)
            ·
              refine ⟨165129727713754805938402379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110086485142503203958934919 165129727713754805938402379)
              ·
                refine ⟨247694591570632208907603569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 165129727713754805938402379 247694591570632208907603569)
                ·
                  refine ⟨185770943677974156680702677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 247694591570632208907603569 185770943677974156680702677)
                  ·
                    refine ⟨4354006492452519297203969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 185770943677974156680702677 4354006492452519297203969)
                    ·
                      refine ⟨3265504869339389472902977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4354006492452519297203969 3265504869339389472902977)
                      ·
                        rfl

theorem cell23_6359548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 2, 7, 2].length) (baseStart_6359548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6359548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6359548 prefixEnd_6359548 := by exact prefixLift 6359548
  have htrace : WordTrace (prefixWord ++ tailWord_6359548) baseStart_6359548 baseEnd_6359548 := by
    simpa [prefixWord, tailWord_6359548, baseEnd_6359548] using wordTrace_append hprefix tailTrace_6359548
  have hstable : (prefixWord ++ tailWord_6359548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6359548).length < 2 ^ (prefixWord ++ tailWord_6359548).sum := by decide
  have hdescent : baseEnd_6359548 < baseStart_6359548 := by decide
  rcases family_descends (prefixWord ++ tailWord_6359548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6359555 : List Nat := [1, 1, 1, 3, 2, 1, 5, 3, 2, 1, 3]
def baseStart_6359555 : Nat := 118140960795 + 6359555 * 2 ^ 59
def prefixEnd_6359555 : Nat := 4983230072969 + 3 ^ 40 * 6359555 * 2
def baseEnd_6359555 : Nat := 3265508463703970945515445

theorem tailTrace_6359555 : CollatzResearch.WordTrace tailWord_6359555 prefixEnd_6359555 3265508463703970945515445 := by
  unfold tailWord_6359555
  simp only [CollatzResearch.WordTrace]
  refine ⟨231952026475425835368240119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154634684316950556912160079 231952026475425835368240119)
  ·
    refine ⟨347928039713138753052360179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231952026475425835368240119 347928039713138753052360179)
    ·
      refine ⟨521892059569708129578540269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 347928039713138753052360179 521892059569708129578540269)
      ·
        refine ⟨195709522338640548591952601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 521892059569708129578540269 195709522338640548591952601)
        ·
          refine ⟨146782141753980411443964451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 195709522338640548591952601 146782141753980411443964451)
          ·
            refine ⟨220173212630970617165946677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146782141753980411443964451 220173212630970617165946677)
            ·
              refine ⟨20641238684153495359307501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 220173212630970617165946677 20641238684153495359307501)
              ·
                refine ⟨7740464506557560759740313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20641238684153495359307501 7740464506557560759740313)
                ·
                  refine ⟨5805348379918170569805235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7740464506557560759740313 5805348379918170569805235)
                  ·
                    refine ⟨8708022569877255854707853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5805348379918170569805235 8708022569877255854707853)
                    ·
                      refine ⟨3265508463703970945515445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8708022569877255854707853 3265508463703970945515445)
                      ·
                        rfl

theorem cell23_6359555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 3, 2, 1, 3].length) (baseStart_6359555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6359555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6359555 prefixEnd_6359555 := by exact prefixLift 6359555
  have htrace : WordTrace (prefixWord ++ tailWord_6359555) baseStart_6359555 baseEnd_6359555 := by
    simpa [prefixWord, tailWord_6359555, baseEnd_6359555] using wordTrace_append hprefix tailTrace_6359555
  have hstable : (prefixWord ++ tailWord_6359555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6359555).length < 2 ^ (prefixWord ++ tailWord_6359555).sum := by decide
  have hdescent : baseEnd_6359555 < baseStart_6359555 := by decide
  rcases family_descends (prefixWord ++ tailWord_6359555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6359559 : List Nat := [1, 1, 4, 3, 4, 1, 1, 2, 1, 2, 3]
def baseStart_6359559 : Nat := 118140960795 + 6359559 * 2 ^ 59
def prefixEnd_6359559 : Nat := 4983230072969 + 3 ^ 40 * 6359559 * 2
def baseEnd_6359559 : Nat := 3265510517626588929865427

theorem tailTrace_6359559 : CollatzResearch.WordTrace tailWord_6359559 prefixEnd_6359559 3265510517626588929865427 := by
  unfold tailWord_6359559
  simp only [CollatzResearch.WordTrace]
  refine ⟨231952172367411344051385731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154634781578274229367590487 231952172367411344051385731)
  ·
    refine ⟨347928258551117016077078597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231952172367411344051385731 347928258551117016077078597)
    ·
      refine ⟨65236548478334440514452237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 347928258551117016077078597 65236548478334440514452237)
      ·
        refine ⟨24463705679375415192919589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65236548478334440514452237 24463705679375415192919589)
        ·
          refine ⟨4586944814882890348672423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24463705679375415192919589 4586944814882890348672423)
          ·
            refine ⟨6880417222324335523008635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4586944814882890348672423 6880417222324335523008635)
            ·
              refine ⟨10320625833486503284512953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6880417222324335523008635 10320625833486503284512953)
              ·
                refine ⟨7740469375114877463384715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10320625833486503284512953 7740469375114877463384715)
                ·
                  refine ⟨11610704062672316195077073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7740469375114877463384715 11610704062672316195077073)
                  ·
                    refine ⟨8708028047004237146307805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11610704062672316195077073 8708028047004237146307805)
                    ·
                      refine ⟨3265510517626588929865427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8708028047004237146307805 3265510517626588929865427)
                      ·
                        rfl

theorem cell23_6359559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 2, 1, 2, 3].length) (baseStart_6359559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6359559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6359559 prefixEnd_6359559 := by exact prefixLift 6359559
  have htrace : WordTrace (prefixWord ++ tailWord_6359559) baseStart_6359559 baseEnd_6359559 := by
    simpa [prefixWord, tailWord_6359559, baseEnd_6359559] using wordTrace_append hprefix tailTrace_6359559
  have hstable : (prefixWord ++ tailWord_6359559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6359559).length < 2 ^ (prefixWord ++ tailWord_6359559).sum := by decide
  have hdescent : baseEnd_6359559 < baseStart_6359559 := by decide
  rcases family_descends (prefixWord ++ tailWord_6359559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6359561 : List Nat := [1, 2, 1, 1, 3, 1, 2, 1, 4, 3, 4]
def baseStart_6359561 : Nat := 118140960795 + 6359561 * 2 ^ 59
def prefixEnd_6359561 : Nat := 4983230072969 + 3 ^ 40 * 6359561 * 2
def baseEnd_6359561 : Nat := 3265511544587897922040417

theorem tailTrace_6359561 : CollatzResearch.WordTrace tailWord_6359561 prefixEnd_6359561 3265511544587897922040417 := by
  unfold tailWord_6359561
  simp only [CollatzResearch.WordTrace]
  refine ⟨231952245313404098392958537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154634830208936065595305691 231952245313404098392958537)
  ·
    refine ⟨173964183985053073794718903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231952245313404098392958537 173964183985053073794718903)
    ·
      refine ⟨260946275977579610692078355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173964183985053073794718903 260946275977579610692078355)
      ·
        refine ⟨391419413966369416038117533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260946275977579610692078355 391419413966369416038117533)
        ·
          refine ⟨146782280237388531014294075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 391419413966369416038117533 146782280237388531014294075)
          ·
            refine ⟨220173420356082796521441113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146782280237388531014294075 220173420356082796521441113)
            ·
              refine ⟨165130065267062097391080835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 220173420356082796521441113 165130065267062097391080835)
              ·
                refine ⟨247695097900593146086621253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 165130065267062097391080835 247695097900593146086621253)
                ·
                  refine ⟨46442830856361214891241485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 247695097900593146086621253 46442830856361214891241485)
                  ·
                    refine ⟨17416061571135455584215557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46442830856361214891241485 17416061571135455584215557)
                    ·
                      refine ⟨3265511544587897922040417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17416061571135455584215557 3265511544587897922040417)
                      ·
                        rfl

theorem cell23_6359561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 4, 3, 4].length) (baseStart_6359561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6359561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6359561 prefixEnd_6359561 := by exact prefixLift 6359561
  have htrace : WordTrace (prefixWord ++ tailWord_6359561) baseStart_6359561 baseEnd_6359561 := by
    simpa [prefixWord, tailWord_6359561, baseEnd_6359561] using wordTrace_append hprefix tailTrace_6359561
  have hstable : (prefixWord ++ tailWord_6359561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6359561).length < 2 ^ (prefixWord ++ tailWord_6359561).sum := by decide
  have hdescent : baseEnd_6359561 < baseStart_6359561 := by decide
  rcases family_descends (prefixWord ++ tailWord_6359561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6359572 : List Nat := [2, 4, 3, 1, 1, 2, 1, 2, 1, 3, 3]
def baseStart_6359572 : Nat := 118140960795 + 6359572 * 2 ^ 59
def prefixEnd_6359572 : Nat := 4983230072969 + 3 ^ 40 * 6359572 * 2
def baseEnd_6359572 : Nat := 3265517192875097379002867

theorem tailTrace_6359572 : CollatzResearch.WordTrace tailWord_6359572 prefixEnd_6359572 3265517192875097379002867 := by
  unfold tailWord_6359572
  simp only [CollatzResearch.WordTrace]
  refine ⟨115976323258182123635804485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154635097677576164847739313 115976323258182123635804485)
  ·
    refine ⟨21745560610909148181713341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115976323258182123635804485 21745560610909148181713341)
    ·
      refine ⟨8154585229090930568142503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21745560610909148181713341 8154585229090930568142503)
      ·
        refine ⟨12231877843636395852213755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8154585229090930568142503 12231877843636395852213755)
        ·
          refine ⟨18347816765454593778320633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12231877843636395852213755 18347816765454593778320633)
          ·
            refine ⟨13760862574090945333740475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18347816765454593778320633 13760862574090945333740475)
            ·
              refine ⟨20641293861136418000610713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13760862574090945333740475 20641293861136418000610713)
              ·
                refine ⟨15480970395852313500458035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20641293861136418000610713 15480970395852313500458035)
                ·
                  refine ⟨23221455593778470250687053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15480970395852313500458035 23221455593778470250687053)
                  ·
                    refine ⟨8708045847666926344007645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23221455593778470250687053 8708045847666926344007645)
                    ·
                      refine ⟨3265517192875097379002867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8708045847666926344007645 3265517192875097379002867)
                      ·
                        rfl

theorem cell23_6359572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_6359572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6359572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6359572 prefixEnd_6359572 := by exact prefixLift 6359572
  have htrace : WordTrace (prefixWord ++ tailWord_6359572) baseStart_6359572 baseEnd_6359572 := by
    simpa [prefixWord, tailWord_6359572, baseEnd_6359572] using wordTrace_append hprefix tailTrace_6359572
  have hstable : (prefixWord ++ tailWord_6359572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6359572).length < 2 ^ (prefixWord ++ tailWord_6359572).sum := by decide
  have hdescent : baseEnd_6359572 < baseStart_6359572 := by decide
  rcases family_descends (prefixWord ++ tailWord_6359572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6359595 : List Nat := [1, 1, 1, 1, 2, 1, 3, 5, 4, 2, 2]
def baseStart_6359595 : Nat := 118140960795 + 6359595 * 2 ^ 59
def prefixEnd_6359595 : Nat := 4983230072969 + 3 ^ 40 * 6359595 * 2
def baseEnd_6359595 : Nat := 3265529002930150789015261

theorem tailTrace_6359595 : CollatzResearch.WordTrace tailWord_6359595 prefixEnd_6359595 3265529002930150789015261 := by
  unfold tailWord_6359595
  simp only [CollatzResearch.WordTrace]
  refine ⟨231953485395280922199696239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154635656930187281466464159 231953485395280922199696239)
  ·
    refine ⟨347930228092921383299544359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231953485395280922199696239 347930228092921383299544359)
    ·
      refine ⟨521895342139382074949316539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 347930228092921383299544359 521895342139382074949316539)
      ·
        refine ⟨782843013209073112423974809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 521895342139382074949316539 782843013209073112423974809)
        ·
          refine ⟨587132259906804834317981107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 782843013209073112423974809 587132259906804834317981107)
          ·
            refine ⟨880698389860207251476971661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 587132259906804834317981107 880698389860207251476971661)
            ·
              refine ⟨330261896197577719303864373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 880698389860207251476971661 330261896197577719303864373)
              ·
                refine ⟨30962052768522911184737285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 330261896197577719303864373 30962052768522911184737285)
                ·
                  refine ⟨5805384894098045847138241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30962052768522911184737285 5805384894098045847138241)
                  ·
                    refine ⟨4354038670573534385353681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5805384894098045847138241 4354038670573534385353681)
                    ·
                      refine ⟨3265529002930150789015261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4354038670573534385353681 3265529002930150789015261)
                      ·
                        rfl

theorem cell23_6359595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 5, 4, 2, 2].length) (baseStart_6359595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6359595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6359595 prefixEnd_6359595 := by exact prefixLift 6359595
  have htrace : WordTrace (prefixWord ++ tailWord_6359595) baseStart_6359595 baseEnd_6359595 := by
    simpa [prefixWord, tailWord_6359595, baseEnd_6359595] using wordTrace_append hprefix tailTrace_6359595
  have hstable : (prefixWord ++ tailWord_6359595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6359595).length < 2 ^ (prefixWord ++ tailWord_6359595).sum := by decide
  have hdescent : baseEnd_6359595 < baseStart_6359595 := by decide
  rcases family_descends (prefixWord ++ tailWord_6359595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6359608 : List Nat := [2, 1, 2, 1, 4, 1, 3, 1, 2, 2, 4]
def baseStart_6359608 : Nat := 118140960795 + 6359608 * 2 ^ 59
def prefixEnd_6359608 : Nat := 4983230072969 + 3 ^ 40 * 6359608 * 2
def baseEnd_6359608 : Nat := 3265535678178659238152701

theorem tailTrace_6359608 : CollatzResearch.WordTrace tailWord_6359608 prefixEnd_6359608 3265535678178659238152701 := by
  unfold tailWord_6359608
  simp only [CollatzResearch.WordTrace]
  refine ⟨115976979772116912709959739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154635973029489216946612985 115976979772116912709959739)
  ·
    refine ⟨173965469658175369064939609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115976979772116912709959739 173965469658175369064939609)
    ·
      refine ⟨130474102243631526798704707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173965469658175369064939609 130474102243631526798704707)
      ·
        refine ⟨195711153365447290198057061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130474102243631526798704707 195711153365447290198057061)
        ·
          refine ⟨36695841256021366912135699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 195711153365447290198057061 36695841256021366912135699)
          ·
            refine ⟨55043761884032050368203549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36695841256021366912135699 55043761884032050368203549)
            ·
              refine ⟨20641410706512018888076331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55043761884032050368203549 20641410706512018888076331)
              ·
                refine ⟨30962116059768028332114497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20641410706512018888076331 30962116059768028332114497)
                ·
                  refine ⟨23221587044826021249085873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30962116059768028332114497 23221587044826021249085873)
                  ·
                    refine ⟨17416190283619515936814405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23221587044826021249085873 17416190283619515936814405)
                    ·
                      refine ⟨3265535678178659238152701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17416190283619515936814405 3265535678178659238152701)
                      ·
                        rfl

theorem cell23_6359608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 1, 2, 2, 4].length) (baseStart_6359608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6359608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6359608 prefixEnd_6359608 := by exact prefixLift 6359608
  have htrace : WordTrace (prefixWord ++ tailWord_6359608) baseStart_6359608 baseEnd_6359608 := by
    simpa [prefixWord, tailWord_6359608, baseEnd_6359608] using wordTrace_append hprefix tailTrace_6359608
  have hstable : (prefixWord ++ tailWord_6359608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6359608).length < 2 ^ (prefixWord ++ tailWord_6359608).sum := by decide
  have hdescent : baseEnd_6359608 < baseStart_6359608 := by decide
  rcases family_descends (prefixWord ++ tailWord_6359608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6359612 : List Nat := [2, 2, 2, 2, 3, 2, 2, 1, 1, 4, 2]
def baseStart_6359612 : Nat := 118140960795 + 6359612 * 2 ^ 59
def prefixEnd_6359612 : Nat := 4983230072969 + 3 ^ 40 * 6359612 * 2
def baseEnd_6359612 : Nat := 3265537732101277222502683

theorem tailTrace_6359612 : CollatzResearch.WordTrace tailWord_6359612 prefixEnd_6359612 3265537732101277222502683 := by
  unfold tailWord_6359612
  simp only [CollatzResearch.WordTrace]
  refine ⟨115977052718109667051532545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154636070290812889402043393 115977052718109667051532545)
  ·
    refine ⟨86982789538582250288649409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115977052718109667051532545 86982789538582250288649409)
    ·
      refine ⟨65237092153936687716487057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86982789538582250288649409 65237092153936687716487057)
      ·
        refine ⟨48927819115452515787365293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65237092153936687716487057 48927819115452515787365293)
        ·
          refine ⟨18347932168294693420261985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48927819115452515787365293 18347932168294693420261985)
          ·
            refine ⟨13760949126221020065196489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18347932168294693420261985 13760949126221020065196489)
            ·
              refine ⟨10320711844665765048897367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13760949126221020065196489 10320711844665765048897367)
              ·
                refine ⟨15481067766998647573346051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10320711844665765048897367 15481067766998647573346051)
                ·
                  refine ⟨23221601650497971360019077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15481067766998647573346051 23221601650497971360019077)
                  ·
                    refine ⟨4354050309468369630003577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23221601650497971360019077 4354050309468369630003577)
                    ·
                      refine ⟨3265537732101277222502683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4354050309468369630003577 3265537732101277222502683)
                      ·
                        rfl

theorem cell23_6359612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 1, 1, 4, 2].length) (baseStart_6359612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6359612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6359612 prefixEnd_6359612 := by exact prefixLift 6359612
  have htrace : WordTrace (prefixWord ++ tailWord_6359612) baseStart_6359612 baseEnd_6359612 := by
    simpa [prefixWord, tailWord_6359612, baseEnd_6359612] using wordTrace_append hprefix tailTrace_6359612
  have hstable : (prefixWord ++ tailWord_6359612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6359612).length < 2 ^ (prefixWord ++ tailWord_6359612).sum := by decide
  have hdescent : baseEnd_6359612 < baseStart_6359612 := by decide
  rcases family_descends (prefixWord ++ tailWord_6359612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6359628 : List Nat := [2, 2, 1, 3, 1, 2, 1, 2, 1, 5, 3]
def baseStart_6359628 : Nat := 118140960795 + 6359628 * 2 ^ 59
def prefixEnd_6359628 : Nat := 4983230072969 + 3 ^ 40 * 6359628 * 2
def baseEnd_6359628 : Nat := 3265545947791749159902609

theorem tailTrace_6359628 : CollatzResearch.WordTrace tailWord_6359628 prefixEnd_6359628 3265545947791749159902609 := by
  unfold tailWord_6359628
  simp only [CollatzResearch.WordTrace]
  refine ⟨115977344502080684417823769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154636459336107579223765025 115977344502080684417823769)
  ·
    refine ⟨86983008376560513313367827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115977344502080684417823769 86983008376560513313367827)
    ·
      refine ⟨130474512564840769970051741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86983008376560513313367827 130474512564840769970051741)
      ·
        refine ⟨48927942211815288738769403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130474512564840769970051741 48927942211815288738769403)
        ·
          refine ⟨73391913317722933108154105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48927942211815288738769403 73391913317722933108154105)
          ·
            refine ⟨55043934988292199831115579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73391913317722933108154105 55043934988292199831115579)
            ·
              refine ⟨82565902482438299746673369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55043934988292199831115579 82565902482438299746673369)
              ·
                refine ⟨61924426861828724810005027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82565902482438299746673369 61924426861828724810005027)
                ·
                  refine ⟨92886640292743087215007541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61924426861828724810005027 92886640292743087215007541)
                  ·
                    refine ⟨8708122527444664426406957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 92886640292743087215007541 8708122527444664426406957)
                    ·
                      refine ⟨3265545947791749159902609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8708122527444664426406957 3265545947791749159902609)
                      ·
                        rfl

theorem cell23_6359628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 2, 1, 5, 3].length) (baseStart_6359628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6359628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6359628 prefixEnd_6359628 := by exact prefixLift 6359628
  have htrace : WordTrace (prefixWord ++ tailWord_6359628) baseStart_6359628 baseEnd_6359628 := by
    simpa [prefixWord, tailWord_6359628, baseEnd_6359628] using wordTrace_append hprefix tailTrace_6359628
  have hstable : (prefixWord ++ tailWord_6359628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6359628).length < 2 ^ (prefixWord ++ tailWord_6359628).sum := by decide
  have hdescent : baseEnd_6359628 < baseStart_6359628 := by decide
  rcases family_descends (prefixWord ++ tailWord_6359628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6359648 : List Nat := [2, 1, 1, 3, 2, 1, 2, 4, 2, 5]
def baseStart_6359648 : Nat := 118140960795 + 6359648 * 2 ^ 59
def prefixEnd_6359648 : Nat := 4983230072969 + 3 ^ 40 * 6359648 * 2
def baseEnd_6359648 : Nat := 1088518739134946360550839

theorem tailTrace_6359648 : CollatzResearch.WordTrace tailWord_6359648 prefixEnd_6359648 1088518739134946360550839 := by
  unfold tailWord_6359648
  simp only [CollatzResearch.WordTrace]
  refine ⟨115977709232044456125687799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154636945642725941500917065 115977709232044456125687799)
  ·
    refine ⟨173966563848066684188531699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115977709232044456125687799 173966563848066684188531699)
    ·
      refine ⟨260949845772100026282797549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173966563848066684188531699 260949845772100026282797549)
      ·
        refine ⟨97856192164537509856049081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 260949845772100026282797549 97856192164537509856049081)
        ·
          refine ⟨73392144123403132392036811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97856192164537509856049081 73392144123403132392036811)
          ·
            refine ⟨110088216185104698588055217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73392144123403132392036811 110088216185104698588055217)
            ·
              refine ⟨82566162138828523941041413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110088216185104698588055217 82566162138828523941041413)
              ·
                refine ⟨15481155401030348238945265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82566162138828523941041413 15481155401030348238945265)
                ·
                  refine ⟨11610866550772761179208949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15481155401030348238945265 11610866550772761179208949)
                  ·
                    refine ⟨1088518739134946360550839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11610866550772761179208949 1088518739134946360550839)
                    ·
                      rfl

theorem cell23_6359648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 4, 2, 5].length) (baseStart_6359648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6359648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6359648 prefixEnd_6359648 := by exact prefixLift 6359648
  have htrace : WordTrace (prefixWord ++ tailWord_6359648) baseStart_6359648 baseEnd_6359648 := by
    simpa [prefixWord, tailWord_6359648, baseEnd_6359648] using wordTrace_append hprefix tailTrace_6359648
  have hstable : (prefixWord ++ tailWord_6359648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6359648).length < 2 ^ (prefixWord ++ tailWord_6359648).sum := by decide
  have hdescent : baseEnd_6359648 < baseStart_6359648 := by decide
  rcases family_descends (prefixWord ++ tailWord_6359648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6359658 : List Nat := [3, 1, 3, 2, 1, 1, 2, 1, 1, 1, 7]
def baseStart_6359658 : Nat := 118140960795 + 6359658 * 2 ^ 59
def prefixEnd_6359658 : Nat := 4983230072969 + 3 ^ 40 * 6359658 * 2
def baseEnd_6359658 : Nat := 3265561352211384042527471

theorem tailTrace_6359658 : CollatzResearch.WordTrace tailWord_6359658 prefixEnd_6359658 3265561352211384042527471 := by
  unfold tailWord_6359658
  simp only [CollatzResearch.WordTrace]
  refine ⟨57988945798513170989809907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154637188796035122639493085 57988945798513170989809907)
  ·
    refine ⟨86983418697769756484714861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57988945798513170989809907 86983418697769756484714861)
    ·
      refine ⟨32618782011663658681768073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86983418697769756484714861 32618782011663658681768073)
      ·
        refine ⟨24464086508747744011326055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32618782011663658681768073 24464086508747744011326055)
        ·
          refine ⟨36696129763121616016989083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24464086508747744011326055 36696129763121616016989083)
          ·
            refine ⟨55044194644682424025483625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36696129763121616016989083 55044194644682424025483625)
            ·
              refine ⟨41283145983511818019112719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55044194644682424025483625 41283145983511818019112719)
              ·
                refine ⟨61924718975267727028669079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41283145983511818019112719 61924718975267727028669079)
                ·
                  refine ⟨92887078462901590543003619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61924718975267727028669079 92887078462901590543003619)
                  ·
                    refine ⟨139330617694352385814505429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 92887078462901590543003619 139330617694352385814505429)
                    ·
                      refine ⟨3265561352211384042527471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 139330617694352385814505429 3265561352211384042527471)
                      ·
                        rfl

theorem cell23_6359658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_6359658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6359658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6359658 prefixEnd_6359658 := by exact prefixLift 6359658
  have htrace : WordTrace (prefixWord ++ tailWord_6359658) baseStart_6359658 baseEnd_6359658 := by
    simpa [prefixWord, tailWord_6359658, baseEnd_6359658] using wordTrace_append hprefix tailTrace_6359658
  have hstable : (prefixWord ++ tailWord_6359658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6359658).length < 2 ^ (prefixWord ++ tailWord_6359658).sum := by decide
  have hdescent : baseEnd_6359658 < baseStart_6359658 := by decide
  rcases family_descends (prefixWord ++ tailWord_6359658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6359705 : List Nat := [1, 2, 1, 2, 1, 2, 5, 2, 2, 2, 3]
def baseStart_6359705 : Nat := 118140960795 + 6359705 * 2 ^ 59
def prefixEnd_6359705 : Nat := 4983230072969 + 3 ^ 40 * 6359705 * 2
def baseEnd_6359705 : Nat := 3265585485802145358639755

theorem tailTrace_6359705 : CollatzResearch.WordTrace tailWord_6359705 prefixEnd_6359705 3265585485802145358639755 := by
  unfold tailWord_6359705
  simp only [CollatzResearch.WordTrace]
  refine ⟨231957497424882410986200569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154638331616588273990800379 231957497424882410986200569)
  ·
    refine ⟨173968123068661808239650427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231957497424882410986200569 173968123068661808239650427)
    ·
      refine ⟨260952184602992712359475641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173968123068661808239650427 260952184602992712359475641)
      ·
        refine ⟨195714138452244534269606731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 260952184602992712359475641 195714138452244534269606731)
        ·
          refine ⟨293571207678366801404410097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195714138452244534269606731 293571207678366801404410097)
          ·
            refine ⟨220178405758775101053307573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 293571207678366801404410097 220178405758775101053307573)
            ·
              refine ⟨20641725539885165723747585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 220178405758775101053307573 20641725539885165723747585)
              ·
                refine ⟨15481294154913874292810689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20641725539885165723747585 15481294154913874292810689)
                ·
                  refine ⟨11610970616185405719608017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15481294154913874292810689 11610970616185405719608017)
                  ·
                    refine ⟨8708227962139054289706013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11610970616185405719608017 8708227962139054289706013)
                    ·
                      refine ⟨3265585485802145358639755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8708227962139054289706013 3265585485802145358639755)
                      ·
                        rfl

theorem cell23_6359705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 2, 2, 2, 3].length) (baseStart_6359705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6359705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6359705 prefixEnd_6359705 := by exact prefixLift 6359705
  have htrace : WordTrace (prefixWord ++ tailWord_6359705) baseStart_6359705 baseEnd_6359705 := by
    simpa [prefixWord, tailWord_6359705, baseEnd_6359705] using wordTrace_append hprefix tailTrace_6359705
  have hstable : (prefixWord ++ tailWord_6359705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6359705).length < 2 ^ (prefixWord ++ tailWord_6359705).sum := by decide
  have hdescent : baseEnd_6359705 < baseStart_6359705 := by decide
  rcases family_descends (prefixWord ++ tailWord_6359705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6359769 : List Nat := [1, 2, 1, 2, 3, 2, 3, 4, 1, 1, 3]
def baseStart_6359769 : Nat := 118140960795 + 6359769 * 2 ^ 59
def prefixEnd_6359769 : Nat := 4983230072969 + 3 ^ 40 * 6359769 * 2
def baseEnd_6359769 : Nat := 3265618348564033108239461

theorem tailTrace_6359769 : CollatzResearch.WordTrace tailWord_6359769 prefixEnd_6359769 3265618348564033108239461 := by
  unfold tailWord_6359769
  simp only [CollatzResearch.WordTrace]
  refine ⟨231959831696650549916530361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154639887797767033277686907 231959831696650549916530361)
  ·
    refine ⟨173969873772487912437397771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231959831696650549916530361 173969873772487912437397771)
    ·
      refine ⟨260954810658731868656096657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173969873772487912437397771 260954810658731868656096657)
      ·
        refine ⟨195716107994048901492072493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 260954810658731868656096657 195716107994048901492072493)
        ·
          refine ⟨73393540497768338059527185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 195716107994048901492072493 73393540497768338059527185)
          ·
            refine ⟨55045155373326253544645389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73393540497768338059527185 55045155373326253544645389)
            ·
              refine ⟨20641933264997345079242021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55045155373326253544645389 20641933264997345079242021)
              ·
                refine ⟨3870362487187002202357879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20641933264997345079242021 3870362487187002202357879)
                ·
                  refine ⟨5805543730780503303536819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3870362487187002202357879 5805543730780503303536819)
                  ·
                    refine ⟨8708315596170754955305229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5805543730780503303536819 8708315596170754955305229)
                    ·
                      refine ⟨3265618348564033108239461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8708315596170754955305229 3265618348564033108239461)
                      ·
                        rfl

theorem cell23_6359769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 4, 1, 1, 3].length) (baseStart_6359769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6359769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6359769 prefixEnd_6359769 := by exact prefixLift 6359769
  have htrace : WordTrace (prefixWord ++ tailWord_6359769) baseStart_6359769 baseEnd_6359769 := by
    simpa [prefixWord, tailWord_6359769, baseEnd_6359769] using wordTrace_append hprefix tailTrace_6359769
  have hstable : (prefixWord ++ tailWord_6359769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6359769).length < 2 ^ (prefixWord ++ tailWord_6359769).sum := by decide
  have hdescent : baseEnd_6359769 < baseStart_6359769 := by decide
  rcases family_descends (prefixWord ++ tailWord_6359769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6359772 : List Nat := [2, 2, 5, 1, 1, 1, 1, 2, 3, 5]
def baseStart_6359772 : Nat := 118140960795 + 6359772 * 2 ^ 59
def prefixEnd_6359772 : Nat := 4983230072969 + 3 ^ 40 * 6359772 * 2
def baseEnd_6359772 : Nat := 1088539963001998865500649

theorem tailTrace_6359772 : CollatzResearch.WordTrace tailWord_6359772 prefixEnd_6359772 1088539963001998865500649 := by
  unfold tailWord_6359772
  simp only [CollatzResearch.WordTrace]
  refine ⟨115979970557819840714444785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154639960743759787619259713 115979970557819840714444785)
  ·
    refine ⟨86984977918364880535833589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115979970557819840714444785 86984977918364880535833589)
    ·
      refine ⟨8154841679846707550234399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 86984977918364880535833589 8154841679846707550234399)
      ·
        refine ⟨12232262519770061325351599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8154841679846707550234399 12232262519770061325351599)
        ·
          refine ⟨18348393779655091988027399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12232262519770061325351599 18348393779655091988027399)
          ·
            refine ⟨27522590669482637982041099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18348393779655091988027399 27522590669482637982041099)
            ·
              refine ⟨41283886004223956973061649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27522590669482637982041099 41283886004223956973061649)
              ·
                refine ⟨30962914503167967729796237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41283886004223956973061649 30962914503167967729796237)
                ·
                  refine ⟨11611092938687987898673589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30962914503167967729796237 11611092938687987898673589)
                  ·
                    refine ⟨1088539963001998865500649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11611092938687987898673589 1088539963001998865500649)
                    ·
                      rfl

theorem cell23_6359772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_6359772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6359772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6359772 prefixEnd_6359772 := by exact prefixLift 6359772
  have htrace : WordTrace (prefixWord ++ tailWord_6359772) baseStart_6359772 baseEnd_6359772 := by
    simpa [prefixWord, tailWord_6359772, baseEnd_6359772] using wordTrace_append hprefix tailTrace_6359772
  have hstable : (prefixWord ++ tailWord_6359772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6359772).length < 2 ^ (prefixWord ++ tailWord_6359772).sum := by decide
  have hdescent : baseEnd_6359772 < baseStart_6359772 := by decide
  rcases family_descends (prefixWord ++ tailWord_6359772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6359775 : List Nat := [1, 1, 2, 3, 2, 3, 1, 2, 3, 1, 4]
def baseStart_6359775 : Nat := 118140960795 + 6359775 * 2 ^ 59
def prefixEnd_6359775 : Nat := 4983230072969 + 3 ^ 40 * 6359775 * 2
def baseEnd_6359775 : Nat := 3265621429447960084764433

theorem tailTrace_6359775 : CollatzResearch.WordTrace tailWord_6359775 prefixEnd_6359775 3265621429447960084764433 := by
  unfold tailWord_6359775
  simp only [CollatzResearch.WordTrace]
  refine ⟨231960050534628812941248779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154640033689752541960832519 231960050534628812941248779)
  ·
    refine ⟨347940075801943219411873169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231960050534628812941248779 347940075801943219411873169)
    ·
      refine ⟨260955056851457414558904877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 347940075801943219411873169 260955056851457414558904877)
      ·
        refine ⟨97858146319296530459589329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 260955056851457414558904877 97858146319296530459589329)
        ·
          refine ⟨73393609739472397844691997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97858146319296530459589329 73393609739472397844691997)
          ·
            refine ⟨27522603652302149191759499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73393609739472397844691997 27522603652302149191759499)
            ·
              refine ⟨41283905478453223787639249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27522603652302149191759499 41283905478453223787639249)
              ·
                refine ⟨30962929108839917840729437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41283905478453223787639249 30962929108839917840729437)
                ·
                  refine ⟨11611098415814969190273539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30962929108839917840729437 11611098415814969190273539)
                  ·
                    refine ⟨17416647623722453785410309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11611098415814969190273539 17416647623722453785410309)
                    ·
                      refine ⟨3265621429447960084764433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17416647623722453785410309 3265621429447960084764433)
                      ·
                        rfl

theorem cell23_6359775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 2, 3, 1, 4].length) (baseStart_6359775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6359775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6359775 prefixEnd_6359775 := by exact prefixLift 6359775
  have htrace : WordTrace (prefixWord ++ tailWord_6359775) baseStart_6359775 baseEnd_6359775 := by
    simpa [prefixWord, tailWord_6359775, baseEnd_6359775] using wordTrace_append hprefix tailTrace_6359775
  have hstable : (prefixWord ++ tailWord_6359775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6359775).length < 2 ^ (prefixWord ++ tailWord_6359775).sum := by decide
  have hdescent : baseEnd_6359775 < baseStart_6359775 := by decide
  rcases family_descends (prefixWord ++ tailWord_6359775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6359805 : List Nat := [1, 4, 1, 1, 1, 1, 3, 4, 1, 2, 4]
def baseStart_6359805 : Nat := 118140960795 + 6359805 * 2 ^ 59
def prefixEnd_6359805 : Nat := 4983230072969 + 3 ^ 40 * 6359805 * 2
def baseEnd_6359805 : Nat := 3265636833867594967389295

theorem tailTrace_6359805 : CollatzResearch.WordTrace tailWord_6359805 prefixEnd_6359805 3265636833867594967389295 := by
  unfold tailWord_6359805
  simp only [CollatzResearch.WordTrace]
  refine ⟨231961144724520128064840869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154640763149680085376560579 231961144724520128064840869)
  ·
    refine ⟨43492714635847524012157663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 231961144724520128064840869 43492714635847524012157663)
    ·
      refine ⟨65239071953771286018236495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43492714635847524012157663 65239071953771286018236495)
      ·
        refine ⟨97858607930656929027354743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65239071953771286018236495 97858607930656929027354743)
        ·
          refine ⟨146787911895985393541032115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97858607930656929027354743 146787911895985393541032115)
          ·
            refine ⟨220181867843978090311548173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146787911895985393541032115 220181867843978090311548173)
            ·
              refine ⟨82568200441491783866830565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 220181867843978090311548173 82568200441491783866830565)
              ·
                refine ⟨15481537582779709475030731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82568200441491783866830565 15481537582779709475030731)
                ·
                  refine ⟨23222306374169564212546097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15481537582779709475030731 23222306374169564212546097)
                  ·
                    refine ⟨17416729780627173159409573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23222306374169564212546097 17416729780627173159409573)
                    ·
                      refine ⟨3265636833867594967389295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17416729780627173159409573 3265636833867594967389295)
                      ·
                        rfl

theorem cell23_6359805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 4, 1, 2, 4].length) (baseStart_6359805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6359805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6359805 prefixEnd_6359805 := by exact prefixLift 6359805
  have htrace : WordTrace (prefixWord ++ tailWord_6359805) baseStart_6359805 baseEnd_6359805 := by
    simpa [prefixWord, tailWord_6359805, baseEnd_6359805] using wordTrace_append hprefix tailTrace_6359805
  have hstable : (prefixWord ++ tailWord_6359805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6359805).length < 2 ^ (prefixWord ++ tailWord_6359805).sum := by decide
  have hdescent : baseEnd_6359805 < baseStart_6359805 := by decide
  rcases family_descends (prefixWord ++ tailWord_6359805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6359806 : List Nat := [4, 2, 2, 1, 2, 3, 2, 1, 1, 5]
def baseStart_6359806 : Nat := 118140960795 + 6359806 * 2 ^ 59
def prefixEnd_6359806 : Nat := 4983230072969 + 3 ^ 40 * 6359806 * 2
def baseEnd_6359806 : Nat := 1088545782449416487825597

theorem tailTrace_6359806 : CollatzResearch.WordTrace tailWord_6359806 prefixEnd_6359806 1088545782449416487825597 := by
  unfold tailWord_6359806
  simp only [CollatzResearch.WordTrace]
  refine ⟨28995147649689563154453409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154640787465011003490418181 28995147649689563154453409)
  ·
    refine ⟨21746360737267172365840057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28995147649689563154453409 21746360737267172365840057)
    ·
      refine ⟨16309770552950379274380043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21746360737267172365840057 16309770552950379274380043)
      ·
        refine ⟨24464655829425568911570065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16309770552950379274380043 24464655829425568911570065)
        ·
          refine ⟨18348491872069176683677549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24464655829425568911570065 18348491872069176683677549)
          ·
            refine ⟨6880684452025941256379081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18348491872069176683677549 6880684452025941256379081)
            ·
              refine ⟨5160513339019455942284311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6880684452025941256379081 5160513339019455942284311)
              ·
                refine ⟨7740770008529183913426467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5160513339019455942284311 7740770008529183913426467)
                ·
                  refine ⟨11611155012793775870139701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7740770008529183913426467 11611155012793775870139701)
                  ·
                    refine ⟨1088545782449416487825597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11611155012793775870139701 1088545782449416487825597)
                    ·
                      rfl

theorem cell23_6359806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 2, 1, 1, 5].length) (baseStart_6359806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6359806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6359806 prefixEnd_6359806 := by exact prefixLift 6359806
  have htrace : WordTrace (prefixWord ++ tailWord_6359806) baseStart_6359806 baseEnd_6359806 := by
    simpa [prefixWord, tailWord_6359806, baseEnd_6359806] using wordTrace_append hprefix tailTrace_6359806
  have hstable : (prefixWord ++ tailWord_6359806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6359806).length < 2 ^ (prefixWord ++ tailWord_6359806).sum := by decide
  have hdescent : baseEnd_6359806 < baseStart_6359806 := by decide
  rcases family_descends (prefixWord ++ tailWord_6359806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6359815 : List Nat := [1, 1, 4, 4, 1, 2, 10]
def baseStart_6359815 : Nat := 118140960795 + 6359815 * 2 ^ 59
def prefixEnd_6359815 : Nat := 4983230072969 + 3 ^ 40 * 6359815 * 2
def baseEnd_6359815 : Nat := 40316567514495554669929

theorem tailTrace_6359815 : CollatzResearch.WordTrace tailWord_6359815 prefixEnd_6359815 40316567514495554669929 := by
  unfold tailWord_6359815
  simp only [CollatzResearch.WordTrace]
  refine ⟨231961509454483899772704899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154641006302989266515136599 231961509454483899772704899)
  ·
    refine ⟨347942264181725849659057349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231961509454483899772704899 347942264181725849659057349)
    ·
      refine ⟨65239174534073596811073253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 347942264181725849659057349 65239174534073596811073253)
      ·
        refine ⟨12232345225138799402076235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65239174534073596811073253 12232345225138799402076235)
        ·
          refine ⟨18348517837708199103114353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12232345225138799402076235 18348517837708199103114353)
          ·
            refine ⟨13761388378281149327335765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18348517837708199103114353 13761388378281149327335765)
            ·
              refine ⟨40316567514495554669929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 13761388378281149327335765 40316567514495554669929)
              ·
                rfl

theorem cell23_6359815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 10].length) (baseStart_6359815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6359815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6359815 prefixEnd_6359815 := by exact prefixLift 6359815
  have htrace : WordTrace (prefixWord ++ tailWord_6359815) baseStart_6359815 baseEnd_6359815 := by
    simpa [prefixWord, tailWord_6359815, baseEnd_6359815] using wordTrace_append hprefix tailTrace_6359815
  have hstable : (prefixWord ++ tailWord_6359815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6359815).length < 2 ^ (prefixWord ++ tailWord_6359815).sum := by decide
  have hdescent : baseEnd_6359815 < baseStart_6359815 := by decide
  rcases family_descends (prefixWord ++ tailWord_6359815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6359825 : List Nat := [1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 3]
def baseStart_6359825 : Nat := 118140960795 + 6359825 * 2 ^ 59
def prefixEnd_6359825 : Nat := 4983230072969 + 3 ^ 40 * 6359825 * 2
def baseEnd_6359825 : Nat := 3265647103480684889139203

theorem tailTrace_6359825 : CollatzResearch.WordTrace tailWord_6359825 prefixEnd_6359825 3265647103480684889139203 := by
  unfold tailWord_6359825
  simp only [CollatzResearch.WordTrace]
  refine ⟨231961874184447671480568929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154641249456298447653712619 231961874184447671480568929)
  ·
    refine ⟨173971405638335753610426697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231961874184447671480568929 173971405638335753610426697)
    ·
      refine ⟨130478554228751815207820023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173971405638335753610426697 130478554228751815207820023)
      ·
        refine ⟨195717831343127722811730035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130478554228751815207820023 195717831343127722811730035)
        ·
          refine ⟨293576747014691584217595053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195717831343127722811730035 293576747014691584217595053)
          ·
            refine ⟨110091280130509344081598145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 293576747014691584217595053 110091280130509344081598145)
            ·
              refine ⟨82568460097882008061198609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110091280130509344081598145 82568460097882008061198609)
              ·
                refine ⟨61926345073411506045898957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82568460097882008061198609 61926345073411506045898957)
                ·
                  refine ⟨23222379402529314767212109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61926345073411506045898957 23222379402529314767212109)
                  ·
                    refine ⟨8708392275948493037704541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23222379402529314767212109 8708392275948493037704541)
                    ·
                      refine ⟨3265647103480684889139203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8708392275948493037704541 3265647103480684889139203)
                      ·
                        rfl

theorem cell23_6359825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 3].length) (baseStart_6359825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6359825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6359825 prefixEnd_6359825 := by exact prefixLift 6359825
  have htrace : WordTrace (prefixWord ++ tailWord_6359825) baseStart_6359825 baseEnd_6359825 := by
    simpa [prefixWord, tailWord_6359825, baseEnd_6359825] using wordTrace_append hprefix tailTrace_6359825
  have hstable : (prefixWord ++ tailWord_6359825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6359825).length < 2 ^ (prefixWord ++ tailWord_6359825).sum := by decide
  have hdescent : baseEnd_6359825 < baseStart_6359825 := by decide
  rcases family_descends (prefixWord ++ tailWord_6359825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6359882 : List Nat := [3, 1, 2, 1, 1, 1, 2, 1, 5, 4, 2]
def baseStart_6359882 : Nat := 118140960795 + 6359882 * 2 ^ 59
def prefixEnd_6359882 : Nat := 4983230072969 + 3 ^ 40 * 6359882 * 2
def baseEnd_6359882 : Nat := 3265676371877991166126441

theorem tailTrace_6359882 : CollatzResearch.WordTrace tailWord_6359882 prefixEnd_6359882 3265676371877991166126441 := by
  unfold tailWord_6359882
  simp only [CollatzResearch.WordTrace]
  refine ⟨57990988286310292553848475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154642635430160780143595933 57990988286310292553848475)
  ·
    refine ⟨86986482429465438830772713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57990988286310292553848475 86986482429465438830772713)
    ·
      refine ⟨65239861822099079123079535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86986482429465438830772713 65239861822099079123079535)
      ·
        refine ⟨97859792733148618684619303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65239861822099079123079535 97859792733148618684619303)
        ·
          refine ⟨146789689099722928026928955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97859792733148618684619303 146789689099722928026928955)
          ·
            refine ⟨220184533649584392040393433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146789689099722928026928955 220184533649584392040393433)
            ·
              refine ⟨165138400237188294030295075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 220184533649584392040393433 165138400237188294030295075)
              ·
                refine ⟨247707600355782441045442613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 165138400237188294030295075 247707600355782441045442613)
                ·
                  refine ⟨23222587533354603848010245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 247707600355782441045442613 23222587533354603848010245)
                  ·
                    refine ⟨4354235162503988221501921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23222587533354603848010245 4354235162503988221501921)
                    ·
                      refine ⟨3265676371877991166126441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4354235162503988221501921 3265676371877991166126441)
                      ·
                        rfl

theorem cell23_6359882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 5, 4, 2].length) (baseStart_6359882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6359882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6359882 prefixEnd_6359882 := by exact prefixLift 6359882
  have htrace : WordTrace (prefixWord ++ tailWord_6359882) baseStart_6359882 baseEnd_6359882 := by
    simpa [prefixWord, tailWord_6359882, baseEnd_6359882] using wordTrace_append hprefix tailTrace_6359882
  have hstable : (prefixWord ++ tailWord_6359882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6359882).length < 2 ^ (prefixWord ++ tailWord_6359882).sum := by decide
  have hdescent : baseEnd_6359882 < baseStart_6359882 := by decide
  rcases family_descends (prefixWord ++ tailWord_6359882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6359969 : List Nat := [1, 2, 3, 4, 1, 1, 3, 1, 2, 5]
def baseStart_6359969 : Nat := 118140960795 + 6359969 * 2 ^ 59
def prefixEnd_6359969 : Nat := 4983230072969 + 3 ^ 40 * 6359969 * 2
def baseEnd_6359969 : Nat := 1088573681564977441912847

theorem tailTrace_6359969 : CollatzResearch.WordTrace tailWord_6359969 prefixEnd_6359969 1088573681564977441912847 := by
  unfold tailWord_6359969
  simp only [CollatzResearch.WordTrace]
  refine ⟨231967126295925984073810961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154644750863950656049207307 231967126295925984073810961)
  ·
    refine ⟨173975344721944488055358221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231967126295925984073810961 173975344721944488055358221)
    ·
      refine ⟨65240754270729183020759333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173975344721944488055358221 65240754270729183020759333)
      ·
        refine ⟨12232641425761721816392375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65240754270729183020759333 12232641425761721816392375)
        ·
          refine ⟨18348962138642582724588563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12232641425761721816392375 18348962138642582724588563)
          ·
            refine ⟨27523443207963874086882845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18348962138642582724588563 27523443207963874086882845)
            ·
              refine ⟨10321291202986452782581067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27523443207963874086882845 10321291202986452782581067)
              ·
                refine ⟨15481936804479679173871601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10321291202986452782581067 15481936804479679173871601)
                ·
                  refine ⟨11611452603359759380403701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15481936804479679173871601 11611452603359759380403701)
                  ·
                    refine ⟨1088573681564977441912847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11611452603359759380403701 1088573681564977441912847)
                    ·
                      rfl

theorem cell23_6359969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 1, 2, 5].length) (baseStart_6359969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6359969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6359969 prefixEnd_6359969 := by exact prefixLift 6359969
  have htrace : WordTrace (prefixWord ++ tailWord_6359969) baseStart_6359969 baseEnd_6359969 := by
    simpa [prefixWord, tailWord_6359969, baseEnd_6359969] using wordTrace_append hprefix tailTrace_6359969
  have hstable : (prefixWord ++ tailWord_6359969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6359969).length < 2 ^ (prefixWord ++ tailWord_6359969).sum := by decide
  have hdescent : baseEnd_6359969 < baseStart_6359969 := by decide
  rcases family_descends (prefixWord ++ tailWord_6359969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6359972 : List Nat := [2, 3, 1, 2, 1, 2, 3, 1, 1, 3, 4]
def baseStart_6359972 : Nat := 118140960795 + 6359972 * 2 ^ 59
def prefixEnd_6359972 : Nat := 4983230072969 + 3 ^ 40 * 6359972 * 2
def baseEnd_6359972 : Nat := 3265722585136895814001027

theorem tailTrace_6359972 : CollatzResearch.WordTrace tailWord_6359972 prefixEnd_6359972 3265722585136895814001027 := by
  unfold tailWord_6359972
  simp only [CollatzResearch.WordTrace]
  refine ⟨115983617857457557793085085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154644823809943410390780113 115983617857457557793085085)
  ·
    refine ⟨43493856696546584172406907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115983617857457557793085085 43493856696546584172406907)
    ·
      refine ⟨65240785044819876258610361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43493856696546584172406907 65240785044819876258610361)
      ·
        refine ⟨48930588783614907193957771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65240785044819876258610361 48930588783614907193957771)
        ·
          refine ⟨73395883175422360790936657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48930588783614907193957771 73395883175422360790936657)
          ·
            refine ⟨55046912381566770593202493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73395883175422360790936657 55046912381566770593202493)
            ·
              refine ⟨20642592143087538972450935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55046912381566770593202493 20642592143087538972450935)
              ·
                refine ⟨30963888214631308458676403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20642592143087538972450935 30963888214631308458676403)
                ·
                  refine ⟨46445832321946962688014605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30963888214631308458676403 46445832321946962688014605)
                  ·
                    refine ⟨17417187120730111008005477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46445832321946962688014605 17417187120730111008005477)
                    ·
                      refine ⟨3265722585136895814001027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17417187120730111008005477 3265722585136895814001027)
                      ·
                        rfl

theorem cell23_6359972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 1, 1, 3, 4].length) (baseStart_6359972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6359972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6359972 prefixEnd_6359972 := by exact prefixLift 6359972
  have htrace : WordTrace (prefixWord ++ tailWord_6359972) baseStart_6359972 baseEnd_6359972 := by
    simpa [prefixWord, tailWord_6359972, baseEnd_6359972] using wordTrace_append hprefix tailTrace_6359972
  have hstable : (prefixWord ++ tailWord_6359972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6359972).length < 2 ^ (prefixWord ++ tailWord_6359972).sum := by decide
  have hdescent : baseEnd_6359972 < baseStart_6359972 := by decide
  rcases family_descends (prefixWord ++ tailWord_6359972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6359989 : List Nat := [1, 3, 3, 2, 1, 1, 1, 1, 4, 4, 2]
def baseStart_6359989 : Nat := 118140960795 + 6359989 * 2 ^ 59
def prefixEnd_6359989 : Nat := 4983230072969 + 3 ^ 40 * 6359989 * 2
def baseEnd_6359989 : Nat := 3265731314308022247488449

theorem tailTrace_6359989 : CollatzResearch.WordTrace tailWord_6359989 prefixEnd_6359989 3265731314308022247488449 := by
  unfold tailWord_6359989
  simp only [CollatzResearch.WordTrace]
  refine ⟨231967855755853527489539021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154645237170569018326359347 231967855755853527489539021)
  ·
    refine ⟨86987945908445072808577133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 231967855755853527489539021 86987945908445072808577133)
    ·
      refine ⟨32620479715666902303216425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86987945908445072808577133 32620479715666902303216425)
      ·
        refine ⟨24465359786750176727412319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32620479715666902303216425 24465359786750176727412319)
        ·
          refine ⟨36698039680125265091118479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24465359786750176727412319 36698039680125265091118479)
          ·
            refine ⟨55047059520187897636677719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36698039680125265091118479 55047059520187897636677719)
            ·
              refine ⟨82570589280281846455016579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55047059520187897636677719 82570589280281846455016579)
              ·
                refine ⟨123855883920422769682524869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82570589280281846455016579 123855883920422769682524869)
                ·
                  refine ⟨23222978235079269315473413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 123855883920422769682524869 23222978235079269315473413)
                  ·
                    refine ⟨4354308419077362996651265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23222978235079269315473413 4354308419077362996651265)
                    ·
                      refine ⟨3265731314308022247488449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4354308419077362996651265 3265731314308022247488449)
                      ·
                        rfl

theorem cell23_6359989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 4, 4, 2].length) (baseStart_6359989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6359989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6359989 prefixEnd_6359989 := by exact prefixLift 6359989
  have htrace : WordTrace (prefixWord ++ tailWord_6359989) baseStart_6359989 baseEnd_6359989 := by
    simpa [prefixWord, tailWord_6359989, baseEnd_6359989] using wordTrace_append hprefix tailTrace_6359989
  have hstable : (prefixWord ++ tailWord_6359989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6359989).length < 2 ^ (prefixWord ++ tailWord_6359989).sum := by decide
  have hdescent : baseEnd_6359989 < baseStart_6359989 := by decide
  rcases family_descends (prefixWord ++ tailWord_6359989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6360005 : List Nat := [1, 3, 1, 1, 1, 1, 1, 2, 2, 1, 9]
def baseStart_6360005 : Nat := 118140960795 + 6360005 * 2 ^ 59
def prefixEnd_6360005 : Nat := 4983230072969 + 3 ^ 40 * 6360005 * 2
def baseEnd_6360005 : Nat := 3265739529998494184888375

theorem tailTrace_6360005 : CollatzResearch.WordTrace tailWord_6360005 prefixEnd_6360005 3265739529998494184888375 := by
  unfold tailWord_6360005
  simp only [CollatzResearch.WordTrace]
  refine ⟨231968439323795562222121469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154645626215863708148080979 231968439323795562222121469)
  ·
    refine ⟨86988164746423335833295551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 231968439323795562222121469 86988164746423335833295551)
    ·
      refine ⟨130482247119635003749943327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86988164746423335833295551 130482247119635003749943327)
      ·
        refine ⟨195723370679452505624914991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130482247119635003749943327 195723370679452505624914991)
        ·
          refine ⟨293585056019178758437372487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195723370679452505624914991 293585056019178758437372487)
          ·
            refine ⟨440377584028768137656058731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 293585056019178758437372487 440377584028768137656058731)
            ·
              refine ⟨660566376043152206484088097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 440377584028768137656058731 660566376043152206484088097)
              ·
                refine ⟨495424782032364154863066073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 660566376043152206484088097 495424782032364154863066073)
                ·
                  refine ⟨371568586524273116147299555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 495424782032364154863066073 371568586524273116147299555)
                  ·
                    refine ⟨557352879786409674220949333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 371568586524273116147299555 557352879786409674220949333)
                    ·
                      refine ⟨3265739529998494184888375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 557352879786409674220949333 3265739529998494184888375)
                      ·
                        rfl

theorem cell23_6360005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 1, 9].length) (baseStart_6360005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6360005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6360005 prefixEnd_6360005 := by exact prefixLift 6360005
  have htrace : WordTrace (prefixWord ++ tailWord_6360005) baseStart_6360005 baseEnd_6360005 := by
    simpa [prefixWord, tailWord_6360005, baseEnd_6360005] using wordTrace_append hprefix tailTrace_6360005
  have hstable : (prefixWord ++ tailWord_6360005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6360005).length < 2 ^ (prefixWord ++ tailWord_6360005).sum := by decide
  have hdescent : baseEnd_6360005 < baseStart_6360005 := by decide
  rcases family_descends (prefixWord ++ tailWord_6360005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6360050 : List Nat := [3, 2, 1, 5, 2, 1, 1, 1, 3, 4]
def baseStart_6360050 : Nat := 118140960795 + 6360050 * 2 ^ 59
def prefixEnd_6360050 : Nat := 4983230072969 + 3 ^ 40 * 6360050 * 2
def baseEnd_6360050 : Nat := 1088587545542648836275223

theorem tailTrace_6360050 : CollatzResearch.WordTrace tailWord_6360050 prefixEnd_6360050 1088587545542648836275223 := by
  unfold tailWord_6360050
  simp only [CollatzResearch.WordTrace]
  refine ⟨57992520152158133726877401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154646720405755023271673069 57992520152158133726877401)
  ·
    refine ⟨43494390114118600295158051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57992520152158133726877401 43494390114118600295158051)
    ·
      refine ⟨65241585171177900442737077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43494390114118600295158051 65241585171177900442737077)
      ·
        refine ⟨6116398609797928166506601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 65241585171177900442737077 6116398609797928166506601)
        ·
          refine ⟨4587298957348446124879951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6116398609797928166506601 4587298957348446124879951)
          ·
            refine ⟨6880948436022669187319927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4587298957348446124879951 6880948436022669187319927)
            ·
              refine ⟨10321422654034003780979891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6880948436022669187319927 10321422654034003780979891)
              ·
                refine ⟨15482133981051005671469837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10321422654034003780979891 15482133981051005671469837)
                ·
                  refine ⟨5805800242894127126801189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15482133981051005671469837 5805800242894127126801189)
                  ·
                    refine ⟨1088587545542648836275223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5805800242894127126801189 1088587545542648836275223)
                    ·
                      rfl

theorem cell23_6360050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 1, 3, 4].length) (baseStart_6360050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6360050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6360050 prefixEnd_6360050 := by exact prefixLift 6360050
  have htrace : WordTrace (prefixWord ++ tailWord_6360050) baseStart_6360050 baseEnd_6360050 := by
    simpa [prefixWord, tailWord_6360050, baseEnd_6360050] using wordTrace_append hprefix tailTrace_6360050
  have hstable : (prefixWord ++ tailWord_6360050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6360050).length < 2 ^ (prefixWord ++ tailWord_6360050).sum := by decide
  have hdescent : baseEnd_6360050 < baseStart_6360050 := by decide
  rcases family_descends (prefixWord ++ tailWord_6360050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6360076 : List Nat := [2, 2, 1, 2, 3, 4, 1, 2, 1, 5]
def baseStart_6360076 : Nat := 118140960795 + 6360076 * 2 ^ 59
def prefixEnd_6360076 : Nat := 4983230072969 + 3 ^ 40 * 6360076 * 2
def baseEnd_6360076 : Nat := 1088591995708321135700183

theorem tailTrace_6360076 : CollatzResearch.WordTrace tailWord_6360076 prefixEnd_6360076 1088591995708321135700183 := by
  unfold tailWord_6360076
  simp only [CollatzResearch.WordTrace]
  refine ⟨115985514453269170673978041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154647352604358894231970721 115985514453269170673978041)
  ·
    refine ⟨86989135839951878005483531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115985514453269170673978041 86989135839951878005483531)
    ·
      refine ⟨130483703759927817008225297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86989135839951878005483531 130483703759927817008225297)
      ·
        refine ⟨97862777819945862756168973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130483703759927817008225297 97862777819945862756168973)
        ·
          refine ⟨36698541682479698533563365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97862777819945862756168973 36698541682479698533563365)
          ·
            refine ⟨6880976565464943475043131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36698541682479698533563365 6880976565464943475043131)
            ·
              refine ⟨10321464848197415212564697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6880976565464943475043131 10321464848197415212564697)
              ·
                refine ⟨7741098636148061409423523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10321464848197415212564697 7741098636148061409423523)
                ·
                  refine ⟨11611647954222092114135285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7741098636148061409423523 11611647954222092114135285)
                  ·
                    refine ⟨1088591995708321135700183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11611647954222092114135285 1088591995708321135700183)
                    ·
                      rfl

theorem cell23_6360076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 2, 1, 5].length) (baseStart_6360076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6360076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6360076 prefixEnd_6360076 := by exact prefixLift 6360076
  have htrace : WordTrace (prefixWord ++ tailWord_6360076) baseStart_6360076 baseEnd_6360076 := by
    simpa [prefixWord, tailWord_6360076, baseEnd_6360076] using wordTrace_append hprefix tailTrace_6360076
  have hstable : (prefixWord ++ tailWord_6360076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6360076).length < 2 ^ (prefixWord ++ tailWord_6360076).sum := by decide
  have hdescent : baseEnd_6360076 < baseStart_6360076 := by decide
  rcases family_descends (prefixWord ++ tailWord_6360076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6360093 : List Nat := [1, 4, 2, 2, 3, 1, 3, 1, 1, 5]
def baseStart_6360093 : Nat := 118140960795 + 6360093 * 2 ^ 59
def prefixEnd_6360093 : Nat := 4983230072969 + 3 ^ 40 * 6360093 * 2
def baseEnd_6360093 : Nat := 1088594905432029946862657

theorem tailTrace_6360093 : CollatzResearch.WordTrace tailWord_6360093 prefixEnd_6360093 1088594905432029946862657 := by
  unfold tailWord_6360093
  simp only [CollatzResearch.WordTrace]
  refine ⟨231971648947476753251324933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154647765964984502167549955 231971648947476753251324933)
  ·
    refine ⟨43494684177651891234623425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 231971648947476753251324933 43494684177651891234623425)
    ·
      refine ⟨32621013133238918425967569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43494684177651891234623425 32621013133238918425967569)
      ·
        refine ⟨24465759849929188819475677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32621013133238918425967569 24465759849929188819475677)
        ·
          refine ⟨9174659943723445807303379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24465759849929188819475677 9174659943723445807303379)
          ·
            refine ⟨13761989915585168710955069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9174659943723445807303379 13761989915585168710955069)
            ·
              refine ⟨5160746218344438266608151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13761989915585168710955069 5160746218344438266608151)
              ·
                refine ⟨7741119327516657399912227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5160746218344438266608151 7741119327516657399912227)
                ·
                  refine ⟨11611678991274986099868341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7741119327516657399912227 11611678991274986099868341)
                  ·
                    refine ⟨1088594905432029946862657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11611678991274986099868341 1088594905432029946862657)
                    ·
                      rfl

theorem cell23_6360093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 3, 1, 1, 5].length) (baseStart_6360093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6360093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6360093 prefixEnd_6360093 := by exact prefixLift 6360093
  have htrace : WordTrace (prefixWord ++ tailWord_6360093) baseStart_6360093 baseEnd_6360093 := by
    simpa [prefixWord, tailWord_6360093, baseEnd_6360093] using wordTrace_append hprefix tailTrace_6360093
  have hstable : (prefixWord ++ tailWord_6360093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6360093).length < 2 ^ (prefixWord ++ tailWord_6360093).sum := by decide
  have hdescent : baseEnd_6360093 < baseStart_6360093 := by decide
  rcases family_descends (prefixWord ++ tailWord_6360093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6360099 : List Nat := [1, 1, 1, 4, 3, 2, 3, 1, 1, 1, 5]
def baseStart_6360099 : Nat := 118140960795 + 6360099 * 2 ^ 59
def prefixEnd_6360099 : Nat := 4983230072969 + 3 ^ 40 * 6360099 * 2
def baseEnd_6360099 : Nat := 3265787797180016817112943

theorem tailTrace_6360099 : CollatzResearch.WordTrace tailWord_6360099 prefixEnd_6360099 3265787797180016817112943 := by
  unfold tailWord_6360099
  simp only [CollatzResearch.WordTrace]
  refine ⟨231971867785455016276043351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154647911856970010850695567 231971867785455016276043351)
  ·
    refine ⟨347957801678182524414065027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231971867785455016276043351 347957801678182524414065027)
    ·
      refine ⟨521936702517273786621097541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 347957801678182524414065027 521936702517273786621097541)
      ·
        refine ⟨97863131721988834991455789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 521936702517273786621097541 97863131721988834991455789)
        ·
          refine ⟨36698674395745813121795921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97863131721988834991455789 36698674395745813121795921)
          ·
            refine ⟨27524005796809359841346941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36698674395745813121795921 27524005796809359841346941)
            ·
              refine ⟨10321502173803509940505103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27524005796809359841346941 10321502173803509940505103)
              ·
                refine ⟨15482253260705264910757655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10321502173803509940505103 15482253260705264910757655)
                ·
                  refine ⟨23223379891057897366136483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15482253260705264910757655 23223379891057897366136483)
                  ·
                    refine ⟨34835069836586846049204725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23223379891057897366136483 34835069836586846049204725)
                    ·
                      refine ⟨3265787797180016817112943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34835069836586846049204725 3265787797180016817112943)
                      ·
                        rfl

theorem cell23_6360099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 1, 1, 1, 5].length) (baseStart_6360099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6360099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6360099 prefixEnd_6360099 := by exact prefixLift 6360099
  have htrace : WordTrace (prefixWord ++ tailWord_6360099) baseStart_6360099 baseEnd_6360099 := by
    simpa [prefixWord, tailWord_6360099, baseEnd_6360099] using wordTrace_append hprefix tailTrace_6360099
  have hstable : (prefixWord ++ tailWord_6360099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6360099).length < 2 ^ (prefixWord ++ tailWord_6360099).sum := by decide
  have hdescent : baseEnd_6360099 < baseStart_6360099 := by decide
  rcases family_descends (prefixWord ++ tailWord_6360099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6360122 : List Nat := [3, 1, 1, 1, 3, 1, 2, 1, 2, 2, 6]
def baseStart_6360122 : Nat := 118140960795 + 6360122 * 2 ^ 59
def prefixEnd_6360122 : Nat := 4983230072969 + 3 ^ 40 * 6360122 * 2
def baseEnd_6360122 : Nat := 3265799607235070227125337

theorem tailTrace_6360122 : CollatzResearch.WordTrace tailWord_6360122 prefixEnd_6360122 3265799607235070227125337 := by
  unfold tailWord_6360122
  simp only [CollatzResearch.WordTrace]
  refine ⟨57993176666092922801032655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154648471109581127469420413 57993176666092922801032655)
  ·
    refine ⟨86989764999139384201548983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57993176666092922801032655 86989764999139384201548983)
    ·
      refine ⟨130484647498709076302323475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86989764999139384201548983 130484647498709076302323475)
      ·
        refine ⟨195726971248063614453485213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130484647498709076302323475 195726971248063614453485213)
        ·
          refine ⟨73397614218023855420056955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 195726971248063614453485213 73397614218023855420056955)
          ·
            refine ⟨110096421327035783130085433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73397614218023855420056955 110096421327035783130085433)
            ·
              refine ⟨82572315995276837347564075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110096421327035783130085433 82572315995276837347564075)
              ·
                refine ⟨123858473992915256021346113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82572315995276837347564075 123858473992915256021346113)
                ·
                  refine ⟨92893855494686442016009585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 123858473992915256021346113 92893855494686442016009585)
                  ·
                    refine ⟨69670391621014831512007189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 92893855494686442016009585 69670391621014831512007189)
                    ·
                      refine ⟨3265799607235070227125337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69670391621014831512007189 3265799607235070227125337)
                      ·
                        rfl

theorem cell23_6360122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 2, 2, 6].length) (baseStart_6360122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6360122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6360122 prefixEnd_6360122 := by exact prefixLift 6360122
  have htrace : WordTrace (prefixWord ++ tailWord_6360122) baseStart_6360122 baseEnd_6360122 := by
    simpa [prefixWord, tailWord_6360122, baseEnd_6360122] using wordTrace_append hprefix tailTrace_6360122
  have hstable : (prefixWord ++ tailWord_6360122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6360122).length < 2 ^ (prefixWord ++ tailWord_6360122).sum := by decide
  have hdescent : baseEnd_6360122 < baseStart_6360122 := by decide
  rcases family_descends (prefixWord ++ tailWord_6360122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6360126 : List Nat := [4, 2, 1, 3, 1, 1, 1, 3, 1, 2, 4]
def baseStart_6360126 : Nat := 118140960795 + 6360126 * 2 ^ 59
def prefixEnd_6360126 : Nat := 4983230072969 + 3 ^ 40 * 6360126 * 2
def baseEnd_6360126 : Nat := 3265801661157688211475319

theorem tailTrace_6360126 : CollatzResearch.WordTrace tailWord_6360126 prefixEnd_6360126 3265801661157688211475319 := by
  unfold tailWord_6360126
  simp only [CollatzResearch.WordTrace]
  refine ⟨28996606569544649985909529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154648568370904799924850821 28996606569544649985909529)
  ·
    refine ⟨21747454927158487489432147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28996606569544649985909529 21747454927158487489432147)
    ·
      refine ⟨32621182390737731234148221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21747454927158487489432147 32621182390737731234148221)
      ·
        refine ⟨12232943396526649212805583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32621182390737731234148221 12232943396526649212805583)
        ·
          refine ⟨18349415094789973819208375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12232943396526649212805583 18349415094789973819208375)
          ·
            refine ⟨27524122642184960728812563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18349415094789973819208375 27524122642184960728812563)
            ·
              refine ⟨41286183963277441093218845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27524122642184960728812563 41286183963277441093218845)
              ·
                refine ⟨15482318986229040409957067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41286183963277441093218845 15482318986229040409957067)
                ·
                  refine ⟨23223478479343560614935601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15482318986229040409957067 23223478479343560614935601)
                  ·
                    refine ⟨17417608859507670461201701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23223478479343560614935601 17417608859507670461201701)
                    ·
                      refine ⟨3265801661157688211475319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17417608859507670461201701 3265801661157688211475319)
                      ·
                        rfl

theorem cell23_6360126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_6360126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6360126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6360126 prefixEnd_6360126 := by exact prefixLift 6360126
  have htrace : WordTrace (prefixWord ++ tailWord_6360126) baseStart_6360126 baseEnd_6360126 := by
    simpa [prefixWord, tailWord_6360126, baseEnd_6360126] using wordTrace_append hprefix tailTrace_6360126
  have hstable : (prefixWord ++ tailWord_6360126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6360126).length < 2 ^ (prefixWord ++ tailWord_6360126).sum := by decide
  have hdescent : baseEnd_6360126 < baseStart_6360126 := by decide
  rcases family_descends (prefixWord ++ tailWord_6360126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6360146 : List Nat := [3, 2, 2, 1, 3, 1, 2, 2, 1, 3, 3]
def baseStart_6360146 : Nat := 118140960795 + 6360146 * 2 ^ 59
def prefixEnd_6360146 : Nat := 4983230072969 + 3 ^ 40 * 6360146 * 2
def baseEnd_6360146 : Nat := 3265811930770778133225227

theorem tailTrace_6360146 : CollatzResearch.WordTrace tailWord_6360146 prefixEnd_6360146 3265811930770778133225227 := by
  unfold tailWord_6360146
  simp only [CollatzResearch.WordTrace]
  refine ⟨57993395504071185825751073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154649054677523162202002861 57993395504071185825751073)
  ·
    refine ⟨43495046628053389369313305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57993395504071185825751073 43495046628053389369313305)
    ·
      refine ⟨32621284971040042026984979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43495046628053389369313305 32621284971040042026984979)
      ·
        refine ⟨48931927456560063040477469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32621284971040042026984979 48931927456560063040477469)
        ·
          refine ⟨18349472796210023640179051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48931927456560063040477469 18349472796210023640179051)
          ·
            refine ⟨27524209194315035460268577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18349472796210023640179051 27524209194315035460268577)
            ·
              refine ⟨20643156895736276595201433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27524209194315035460268577 20643156895736276595201433)
              ·
                refine ⟨15482367671802207446401075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20643156895736276595201433 15482367671802207446401075)
                ·
                  refine ⟨23223551507703311169601613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15482367671802207446401075 23223551507703311169601613)
                  ·
                    refine ⟨8708831815388741688600605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23223551507703311169601613 8708831815388741688600605)
                    ·
                      refine ⟨3265811930770778133225227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8708831815388741688600605 3265811930770778133225227)
                      ·
                        rfl

theorem cell23_6360146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 2, 1, 3, 3].length) (baseStart_6360146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6360146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6360146 prefixEnd_6360146 := by exact prefixLift 6360146
  have htrace : WordTrace (prefixWord ++ tailWord_6360146) baseStart_6360146 baseEnd_6360146 := by
    simpa [prefixWord, tailWord_6360146, baseEnd_6360146] using wordTrace_append hprefix tailTrace_6360146
  have hstable : (prefixWord ++ tailWord_6360146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6360146).length < 2 ^ (prefixWord ++ tailWord_6360146).sum := by decide
  have hdescent : baseEnd_6360146 < baseStart_6360146 := by decide
  rcases family_descends (prefixWord ++ tailWord_6360146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6360157 : List Nat := [1, 4, 4, 1, 3, 1, 1, 2, 2, 4]
def baseStart_6360157 : Nat := 118140960795 + 6360157 * 2 ^ 59
def prefixEnd_6360157 : Nat := 4983230072969 + 3 ^ 40 * 6360157 * 2
def baseEnd_6360157 : Nat := 1088605859685992530062559

theorem tailTrace_6360157 : CollatzResearch.WordTrace tailWord_6360157 prefixEnd_6360157 1088605859685992530062559 := by
  unfold tailWord_6360157
  simp only [CollatzResearch.WordTrace]
  refine ⟨231973983219244892181654725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154649322146163261454436483 231973983219244892181654725)
  ·
    refine ⟨43495121853608417284060261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 231973983219244892181654725 43495121853608417284060261)
    ·
      refine ⟨8155335347551578240761299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43495121853608417284060261 8155335347551578240761299)
      ·
        refine ⟨12233003021327367361141949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8155335347551578240761299 12233003021327367361141949)
        ·
          refine ⟨4587376132997762760428231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12233003021327367361141949 4587376132997762760428231)
          ·
            refine ⟨6881064199496644140642347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4587376132997762760428231 6881064199496644140642347)
            ·
              refine ⟨10321596299244966210963521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6881064199496644140642347 10321596299244966210963521)
              ·
                refine ⟨7741197224433724658222641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10321596299244966210963521 7741197224433724658222641)
                ·
                  refine ⟨5805897918325293493666981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7741197224433724658222641 5805897918325293493666981)
                  ·
                    refine ⟨1088605859685992530062559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5805897918325293493666981 1088605859685992530062559)
                    ·
                      rfl

theorem cell23_6360157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_6360157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6360157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6360157 prefixEnd_6360157 := by exact prefixLift 6360157
  have htrace : WordTrace (prefixWord ++ tailWord_6360157) baseStart_6360157 baseEnd_6360157 := by
    simpa [prefixWord, tailWord_6360157, baseEnd_6360157] using wordTrace_append hprefix tailTrace_6360157
  have hstable : (prefixWord ++ tailWord_6360157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6360157).length < 2 ^ (prefixWord ++ tailWord_6360157).sum := by decide
  have hdescent : baseEnd_6360157 < baseStart_6360157 := by decide
  rcases family_descends (prefixWord ++ tailWord_6360157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6360189 : List Nat := [1, 4, 1, 1, 3, 1, 2, 2, 2, 1, 5]
def baseStart_6360189 : Nat := 118140960795 + 6360189 * 2 ^ 59
def prefixEnd_6360189 : Nat := 4983230072969 + 3 ^ 40 * 6360189 * 2
def baseEnd_6360189 : Nat := 3265834010438921464987529

theorem tailTrace_6360189 : CollatzResearch.WordTrace tailWord_6360189 prefixEnd_6360189 3265834010438921464987529 := by
  unfold tailWord_6360189
  simp only [CollatzResearch.WordTrace]
  refine ⟨231975150355128961646819621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154650100236752641097879747 231975150355128961646819621)
  ·
    refine ⟨43495340691586680308778679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 231975150355128961646819621 43495340691586680308778679)
    ·
      refine ⟨65243011037380020463168019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43495340691586680308778679 65243011037380020463168019)
      ·
        refine ⟨97864516556070030694752029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65243011037380020463168019 97864516556070030694752029)
        ·
          refine ⟨36699193708526261510532011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97864516556070030694752029 36699193708526261510532011)
          ·
            refine ⟨55048790562789392265798017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36699193708526261510532011 55048790562789392265798017)
            ·
              refine ⟨41286592922092044199348513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55048790562789392265798017 41286592922092044199348513)
              ·
                refine ⟨30964944691569033149511385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41286592922092044199348513 30964944691569033149511385)
                ·
                  refine ⟨23223708518676774862133539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30964944691569033149511385 23223708518676774862133539)
                  ·
                    refine ⟨34835562778015162293200309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23223708518676774862133539 34835562778015162293200309)
                    ·
                      refine ⟨3265834010438921464987529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34835562778015162293200309 3265834010438921464987529)
                      ·
                        rfl

theorem cell23_6360189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 2, 2, 1, 5].length) (baseStart_6360189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6360189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6360189 prefixEnd_6360189 := by exact prefixLift 6360189
  have htrace : WordTrace (prefixWord ++ tailWord_6360189) baseStart_6360189 baseEnd_6360189 := by
    simpa [prefixWord, tailWord_6360189, baseEnd_6360189] using wordTrace_append hprefix tailTrace_6360189
  have hstable : (prefixWord ++ tailWord_6360189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6360189).length < 2 ^ (prefixWord ++ tailWord_6360189).sum := by decide
  have hdescent : baseEnd_6360189 < baseStart_6360189 := by decide
  rcases family_descends (prefixWord ++ tailWord_6360189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6360206 : List Nat := [4, 1, 1, 3, 2, 2, 1, 1, 2, 1, 5]
def baseStart_6360206 : Nat := 118140960795 + 6360206 * 2 ^ 59
def prefixEnd_6360206 : Nat := 4983230072969 + 3 ^ 40 * 6360206 * 2
def baseEnd_6360206 : Nat := 3265842739610047898474951

theorem tailTrace_6360206 : CollatzResearch.WordTrace tailWord_6360206 prefixEnd_6360206 3265842739610047898474951 := by
  unfold tailWord_6360206
  simp only [CollatzResearch.WordTrace]
  refine ⟨28996971299508421693773559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154650513597378249033458981 28996971299508421693773559)
  ·
    refine ⟨43495456949262632540660339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28996971299508421693773559 43495456949262632540660339)
    ·
      refine ⟨65243185423893948810990509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43495456949262632540660339 65243185423893948810990509)
      ·
        refine ⟨24466194533960230804121441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65243185423893948810990509 24466194533960230804121441)
        ·
          refine ⟨18349645900470173103091081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24466194533960230804121441 18349645900470173103091081)
          ·
            refine ⟨13762234425352629827318311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18349645900470173103091081 13762234425352629827318311)
            ·
              refine ⟨20643351638028944740977467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13762234425352629827318311 20643351638028944740977467)
              ·
                refine ⟨30965027457043417111466201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20643351638028944740977467 30965027457043417111466201)
                ·
                  refine ⟨23223770592782562833599651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30965027457043417111466201 23223770592782562833599651)
                  ·
                    refine ⟨34835655889173844250399477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23223770592782562833599651 34835655889173844250399477)
                    ·
                      refine ⟨3265842739610047898474951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34835655889173844250399477 3265842739610047898474951)
                      ·
                        rfl

theorem cell23_6360206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_6360206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6360206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6360206 prefixEnd_6360206 := by exact prefixLift 6360206
  have htrace : WordTrace (prefixWord ++ tailWord_6360206) baseStart_6360206 baseEnd_6360206 := by
    simpa [prefixWord, tailWord_6360206, baseEnd_6360206] using wordTrace_append hprefix tailTrace_6360206
  have hstable : (prefixWord ++ tailWord_6360206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6360206).length < 2 ^ (prefixWord ++ tailWord_6360206).sum := by decide
  have hdescent : baseEnd_6360206 < baseStart_6360206 := by decide
  rcases family_descends (prefixWord ++ tailWord_6360206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6360237 : List Nat := [1, 5, 2, 1, 3, 1, 1, 3, 2, 2, 2]
def baseStart_6360237 : Nat := 118140960795 + 6360237 * 2 ^ 59
def prefixEnd_6360237 : Nat := 4983230072969 + 3 ^ 40 * 6360237 * 2
def baseEnd_6360237 : Nat := 3265858657510337277187309

theorem tailTrace_6360237 : CollatzResearch.WordTrace tailWord_6360237 prefixEnd_6360237 3265858657510337277187309 := by
  unfold tailWord_6360237
  simp only [CollatzResearch.WordTrace]
  refine ⟨231976901058955065844566965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154651267372636710563044643 231976901058955065844566965)
  ·
    refine ⟨21747834474277037422928153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 231976901058955065844566965 21747834474277037422928153)
    ·
      refine ⟨16310875855707778067196115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21747834474277037422928153 16310875855707778067196115)
      ·
        refine ⟨24466313783561667100794173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16310875855707778067196115 24466313783561667100794173)
        ·
          refine ⟨9174867668835625162797815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24466313783561667100794173 9174867668835625162797815)
          ·
            refine ⟨13762301503253437744196723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9174867668835625162797815 13762301503253437744196723)
            ·
              refine ⟨20643452254880156616295085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13762301503253437744196723 20643452254880156616295085)
              ·
                refine ⟨7741294595580058731110657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20643452254880156616295085 7741294595580058731110657)
                ·
                  refine ⟨5805970946685044048332993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7741294595580058731110657 5805970946685044048332993)
                  ·
                    refine ⟨4354478210013783036249745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5805970946685044048332993 4354478210013783036249745)
                    ·
                      refine ⟨3265858657510337277187309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4354478210013783036249745 3265858657510337277187309)
                      ·
                        rfl

theorem cell23_6360237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 3, 2, 2, 2].length) (baseStart_6360237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6360237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6360237 prefixEnd_6360237 := by exact prefixLift 6360237
  have htrace : WordTrace (prefixWord ++ tailWord_6360237) baseStart_6360237 baseEnd_6360237 := by
    simpa [prefixWord, tailWord_6360237, baseEnd_6360237] using wordTrace_append hprefix tailTrace_6360237
  have hstable : (prefixWord ++ tailWord_6360237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6360237).length < 2 ^ (prefixWord ++ tailWord_6360237).sum := by decide
  have hdescent : baseEnd_6360237 < baseStart_6360237 := by decide
  rcases family_descends (prefixWord ++ tailWord_6360237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6360296 : List Nat := [2, 1, 4, 1, 2, 1, 2, 2, 1, 4, 3]
def baseStart_6360296 : Nat := 118140960795 + 6360296 * 2 ^ 59
def prefixEnd_6360296 : Nat := 4983230072969 + 3 ^ 40 * 6360296 * 2
def baseEnd_6360296 : Nat := 3265888952868952546349537

theorem tailTrace_6360296 : CollatzResearch.WordTrace tailWord_6360296 prefixEnd_6360296 3265888952868952546349537 := by
  unfold tailWord_6360296
  simp only [CollatzResearch.WordTrace]
  refine ⟨115989526482870659460482371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154652701977160879280643161 115989526482870659460482371)
  ·
    refine ⟨173984289724305989190723557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115989526482870659460482371 173984289724305989190723557)
    ·
      refine ⟨32622054323307372973260667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 173984289724305989190723557 32622054323307372973260667)
      ·
        refine ⟨48933081484961059459891001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32622054323307372973260667 48933081484961059459891001)
        ·
          refine ⟨36699811113720794594918251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48933081484961059459891001 36699811113720794594918251)
          ·
            refine ⟨55049716670581191892377377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36699811113720794594918251 55049716670581191892377377)
            ·
              refine ⟨41287287502935893919283033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55049716670581191892377377 41287287502935893919283033)
              ·
                refine ⟨30965465627201920439462275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41287287502935893919283033 30965465627201920439462275)
                ·
                  refine ⟨46448198440802880659193413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30965465627201920439462275 46448198440802880659193413)
                  ·
                    refine ⟨8709037207650540123598765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46448198440802880659193413 8709037207650540123598765)
                    ·
                      refine ⟨3265888952868952546349537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8709037207650540123598765 3265888952868952546349537)
                      ·
                        rfl

theorem cell23_6360296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 2, 1, 4, 3].length) (baseStart_6360296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6360296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6360296 prefixEnd_6360296 := by exact prefixLift 6360296
  have htrace : WordTrace (prefixWord ++ tailWord_6360296) baseStart_6360296 baseEnd_6360296 := by
    simpa [prefixWord, tailWord_6360296, baseEnd_6360296] using wordTrace_append hprefix tailTrace_6360296
  have hstable : (prefixWord ++ tailWord_6360296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6360296).length < 2 ^ (prefixWord ++ tailWord_6360296).sum := by decide
  have hdescent : baseEnd_6360296 < baseStart_6360296 := by decide
  rcases family_descends (prefixWord ++ tailWord_6360296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6360303 : List Nat := [1, 1, 2, 1, 7, 1, 1, 2, 3, 4]
def baseStart_6360303 : Nat := 118140960795 + 6360303 * 2 ^ 59
def prefixEnd_6360303 : Nat := 4983230072969 + 3 ^ 40 * 6360303 * 2
def baseEnd_6360303 : Nat := 1088630849077844672987335

theorem tailTrace_6360303 : CollatzResearch.WordTrace tailWord_6360303 prefixEnd_6360303 1088630849077844672987335 := by
  unfold tailWord_6360303
  simp only [CollatzResearch.WordTrace]
  refine ⟨231979308276715959116469563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154652872184477306077646375 231979308276715959116469563)
  ·
    refine ⟨347968962415073938674704345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231979308276715959116469563 347968962415073938674704345)
    ·
      refine ⟨260976721811305454006028259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 347968962415073938674704345 260976721811305454006028259)
      ·
        refine ⟨391465082716958181009042389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260976721811305454006028259 391465082716958181009042389)
        ·
          refine ⟨9174962876178707367399431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 391465082716958181009042389 9174962876178707367399431)
          ·
            refine ⟨13762444314268061051099147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9174962876178707367399431 13762444314268061051099147)
            ·
              refine ⟨20643666471402091576648721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13762444314268061051099147 20643666471402091576648721)
              ·
                refine ⟨15482749853551568682486541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20643666471402091576648721 15482749853551568682486541)
                ·
                  refine ⟨5806031195081838255932453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15482749853551568682486541 5806031195081838255932453)
                  ·
                    refine ⟨1088630849077844672987335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5806031195081838255932453 1088630849077844672987335)
                    ·
                      rfl

theorem cell23_6360303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 2, 3, 4].length) (baseStart_6360303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6360303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6360303 prefixEnd_6360303 := by exact prefixLift 6360303
  have htrace : WordTrace (prefixWord ++ tailWord_6360303) baseStart_6360303 baseEnd_6360303 := by
    simpa [prefixWord, tailWord_6360303, baseEnd_6360303] using wordTrace_append hprefix tailTrace_6360303
  have hstable : (prefixWord ++ tailWord_6360303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6360303).length < 2 ^ (prefixWord ++ tailWord_6360303).sum := by decide
  have hdescent : baseEnd_6360303 < baseStart_6360303 := by decide
  rcases family_descends (prefixWord ++ tailWord_6360303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6360360 : List Nat := [2, 1, 5, 1, 2, 1, 2, 2, 3, 1, 3]
def baseStart_6360360 : Nat := 118140960795 + 6360360 * 2 ^ 59
def prefixEnd_6360360 : Nat := 4983230072969 + 3 ^ 40 * 6360360 * 2
def baseEnd_6360360 : Nat := 3265921815630840295949243

theorem tailTrace_6360360 : CollatzResearch.WordTrace tailWord_6360360 prefixEnd_6360360 3265921815630840295949243 := by
  unfold tailWord_6360360
  simp only [CollatzResearch.WordTrace]
  refine ⟨115990693618754728925647267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154654258158339638567529689 115990693618754728925647267)
  ·
    refine ⟨173986040428132093388470901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115990693618754728925647267 173986040428132093388470901)
    ·
      refine ⟨16311191290137383755169147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 173986040428132093388470901 16311191290137383755169147)
      ·
        refine ⟨24466786935206075632753721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16311191290137383755169147 24466786935206075632753721)
        ·
          refine ⟨18350090201404556724565291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24466786935206075632753721 18350090201404556724565291)
          ·
            refine ⟨27525135302106835086847937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18350090201404556724565291 27525135302106835086847937)
            ·
              refine ⟨20643851476580126315135953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27525135302106835086847937 20643851476580126315135953)
              ·
                refine ⟨15482888607435094736351965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20643851476580126315135953 15482888607435094736351965)
                ·
                  refine ⟨5806083227788160526131987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15482888607435094736351965 5806083227788160526131987)
                  ·
                    refine ⟨8709124841682240789197981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5806083227788160526131987 8709124841682240789197981)
                    ·
                      refine ⟨3265921815630840295949243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8709124841682240789197981 3265921815630840295949243)
                      ·
                        rfl

theorem cell23_6360360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 2, 3, 1, 3].length) (baseStart_6360360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6360360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6360360 prefixEnd_6360360 := by exact prefixLift 6360360
  have htrace : WordTrace (prefixWord ++ tailWord_6360360) baseStart_6360360 baseEnd_6360360 := by
    simpa [prefixWord, tailWord_6360360, baseEnd_6360360] using wordTrace_append hprefix tailTrace_6360360
  have hstable : (prefixWord ++ tailWord_6360360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6360360).length < 2 ^ (prefixWord ++ tailWord_6360360).sum := by decide
  have hdescent : baseEnd_6360360 < baseStart_6360360 := by decide
  rcases family_descends (prefixWord ++ tailWord_6360360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6360383 : List Nat := [1, 1, 2, 2, 4, 2, 2, 3, 1, 1, 4]
def baseStart_6360383 : Nat := 118140960795 + 6360383 * 2 ^ 59
def prefixEnd_6360383 : Nat := 4983230072969 + 3 ^ 40 * 6360383 * 2
def baseEnd_6360383 : Nat := 3265933625685893705961637

theorem tailTrace_6360383 : CollatzResearch.WordTrace tailWord_6360383 prefixEnd_6360383 3265933625685893705961637 := by
  unfold tailWord_6360383
  simp only [CollatzResearch.WordTrace]
  refine ⟨231982226116426132779381803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154654817410950755186254535 231982226116426132779381803)
  ·
    refine ⟨347973339174639199169072705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231982226116426132779381803 347973339174639199169072705)
    ·
      refine ⟨260980004380979399376804529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 347973339174639199169072705 260980004380979399376804529)
      ·
        refine ⟨195735003285734549532603397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 260980004380979399376804529 195735003285734549532603397)
        ·
          refine ⟨36700313116075228037363137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 195735003285734549532603397 36700313116075228037363137)
          ·
            refine ⟨27525234837056421028022353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36700313116075228037363137 27525234837056421028022353)
            ·
              refine ⟨20643926127792315771016765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27525234837056421028022353 20643926127792315771016765)
              ·
                refine ⟨7741472297922118414131287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20643926127792315771016765 7741472297922118414131287)
                ·
                  refine ⟨11612208446883177621196931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7741472297922118414131287 11612208446883177621196931)
                  ·
                    refine ⟨17418312670324766431795397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11612208446883177621196931 17418312670324766431795397)
                    ·
                      refine ⟨3265933625685893705961637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17418312670324766431795397 3265933625685893705961637)
                      ·
                        rfl

theorem cell23_6360383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 3, 1, 1, 4].length) (baseStart_6360383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6360383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6360383 prefixEnd_6360383 := by exact prefixLift 6360383
  have htrace : WordTrace (prefixWord ++ tailWord_6360383) baseStart_6360383 baseEnd_6360383 := by
    simpa [prefixWord, tailWord_6360383, baseEnd_6360383] using wordTrace_append hprefix tailTrace_6360383
  have hstable : (prefixWord ++ tailWord_6360383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6360383).length < 2 ^ (prefixWord ++ tailWord_6360383).sum := by decide
  have hdescent : baseEnd_6360383 < baseStart_6360383 := by decide
  rcases family_descends (prefixWord ++ tailWord_6360383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6360396 : List Nat := [2, 2, 1, 3, 2, 2, 1, 2, 1, 1, 6]
def baseStart_6360396 : Nat := 118140960795 + 6360396 * 2 ^ 59
def prefixEnd_6360396 : Nat := 4983230072969 + 3 ^ 40 * 6360396 * 2
def baseEnd_6360396 : Nat := 3265940300934402155099077

theorem tailTrace_6360396 : CollatzResearch.WordTrace tailWord_6360396 prefixEnd_6360396 3265940300934402155099077 := by
  unfold tailWord_6360396
  simp only [CollatzResearch.WordTrace]
  refine ⟨115991350132689517999802521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154655133510252690666403361 115991350132689517999802521)
  ·
    refine ⟨86993512599517138499851891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115991350132689517999802521 86993512599517138499851891)
    ·
      refine ⟨130490268899275707749777837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86993512599517138499851891 130490268899275707749777837)
      ·
        refine ⟨48933850837228390406166689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130490268899275707749777837 48933850837228390406166689)
        ·
          refine ⟨36700388127921292804625017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48933850837228390406166689 36700388127921292804625017)
          ·
            refine ⟨27525291095940969603468763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36700388127921292804625017 27525291095940969603468763)
            ·
              refine ⟨41287936643911454405203145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27525291095940969603468763 41287936643911454405203145)
              ·
                refine ⟨30965952482933590803902359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41287936643911454405203145 30965952482933590803902359)
                ·
                  refine ⟨46448928724400386205853539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30965952482933590803902359 46448928724400386205853539)
                  ·
                    refine ⟨69673393086600579308780309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46448928724400386205853539 69673393086600579308780309)
                    ·
                      refine ⟨3265940300934402155099077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69673393086600579308780309 3265940300934402155099077)
                      ·
                        rfl

theorem cell23_6360396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 2, 1, 1, 6].length) (baseStart_6360396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6360396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6360396 prefixEnd_6360396 := by exact prefixLift 6360396
  have htrace : WordTrace (prefixWord ++ tailWord_6360396) baseStart_6360396 baseEnd_6360396 := by
    simpa [prefixWord, tailWord_6360396, baseEnd_6360396] using wordTrace_append hprefix tailTrace_6360396
  have hstable : (prefixWord ++ tailWord_6360396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6360396).length < 2 ^ (prefixWord ++ tailWord_6360396).sum := by decide
  have hdescent : baseEnd_6360396 < baseStart_6360396 := by decide
  rcases family_descends (prefixWord ++ tailWord_6360396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6360410 : List Nat := [3, 1, 1, 2, 1, 2, 6, 1, 2, 4]
def baseStart_6360410 : Nat := 118140960795 + 6360410 * 2 ^ 59
def prefixEnd_6360410 : Nat := 4983230072969 + 3 ^ 40 * 6360410 * 2
def baseEnd_6360410 : Nat := 1088649163221188366774671

theorem tailTrace_6360410 : CollatzResearch.WordTrace tailWord_6360410 prefixEnd_6360410 1088649163221188366774671 := by
  unfold tailWord_6360410
  simp only [CollatzResearch.WordTrace]
  refine ⟨57995802721832079097653671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154655473924885544260409789 57995802721832079097653671)
  ·
    refine ⟨86993704082748118646480507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57995802721832079097653671 86993704082748118646480507)
    ·
      refine ⟨130490556124122177969720761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86993704082748118646480507 130490556124122177969720761)
      ·
        refine ⟨97867917093091633477290571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130490556124122177969720761 97867917093091633477290571)
        ·
          refine ⟨146801875639637450215935857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97867917093091633477290571 146801875639637450215935857)
          ·
            refine ⟨110101406729728087661951893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146801875639637450215935857 110101406729728087661951893)
            ·
              refine ⟨5161003440456004109153995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 110101406729728087661951893 5161003440456004109153995)
              ·
                refine ⟨7741505160684006163730993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5161003440456004109153995 7741505160684006163730993)
                ·
                  refine ⟨5806128870513004622798245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7741505160684006163730993 5806128870513004622798245)
                  ·
                    refine ⟨1088649163221188366774671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5806128870513004622798245 1088649163221188366774671)
                    ·
                      rfl

theorem cell23_6360410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 6, 1, 2, 4].length) (baseStart_6360410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6360410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6360410 prefixEnd_6360410 := by exact prefixLift 6360410
  have htrace : WordTrace (prefixWord ++ tailWord_6360410) baseStart_6360410 baseEnd_6360410 := by
    simpa [prefixWord, tailWord_6360410, baseEnd_6360410] using wordTrace_append hprefix tailTrace_6360410
  have hstable : (prefixWord ++ tailWord_6360410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6360410).length < 2 ^ (prefixWord ++ tailWord_6360410).sum := by decide
  have hdescent : baseEnd_6360410 < baseStart_6360410 := by decide
  rcases family_descends (prefixWord ++ tailWord_6360410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6360420 : List Nat := [2, 3, 1, 1, 3, 2, 3, 2, 1, 2, 3]
def baseStart_6360420 : Nat := 118140960795 + 6360420 * 2 ^ 59
def prefixEnd_6360420 : Nat := 4983230072969 + 3 ^ 40 * 6360420 * 2
def baseEnd_6360420 : Nat := 3265952624470110061198967

theorem tailTrace_6360420 : CollatzResearch.WordTrace tailWord_6360420 prefixEnd_6360420 3265952624470110061198967 := by
  unfold tailWord_6360420
  simp only [CollatzResearch.WordTrace]
  refine ⟨115991787808646044049239357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154655717078194725398985809 115991787808646044049239357)
  ·
    refine ⟨43496920428242266518464759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115991787808646044049239357 43496920428242266518464759)
    ·
      refine ⟨65245380642363399777697139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43496920428242266518464759 65245380642363399777697139)
      ·
        refine ⟨97868070963545099666545709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65245380642363399777697139 97868070963545099666545709)
        ·
          refine ⟨36700526611329412374954641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97868070963545099666545709 36700526611329412374954641)
          ·
            refine ⟨27525394958497059281215981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36700526611329412374954641 27525394958497059281215981)
            ·
              refine ⟨10322023109436397230455993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27525394958497059281215981 10322023109436397230455993)
              ·
                refine ⟨7741517332077297922841995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10322023109436397230455993 7741517332077297922841995)
                ·
                  refine ⟨11612275998115946884262993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7741517332077297922841995 11612275998115946884262993)
                  ·
                    refine ⟨8709206998586960163197245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11612275998115946884262993 8709206998586960163197245)
                    ·
                      refine ⟨3265952624470110061198967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8709206998586960163197245 3265952624470110061198967)
                      ·
                        rfl

theorem cell23_6360420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 2, 1, 2, 3].length) (baseStart_6360420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6360420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6360420 prefixEnd_6360420 := by exact prefixLift 6360420
  have htrace : WordTrace (prefixWord ++ tailWord_6360420) baseStart_6360420 baseEnd_6360420 := by
    simpa [prefixWord, tailWord_6360420, baseEnd_6360420] using wordTrace_append hprefix tailTrace_6360420
  have hstable : (prefixWord ++ tailWord_6360420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6360420).length < 2 ^ (prefixWord ++ tailWord_6360420).sum := by decide
  have hdescent : baseEnd_6360420 < baseStart_6360420 := by decide
  rcases family_descends (prefixWord ++ tailWord_6360420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6360433 : List Nat := [1, 2, 2, 2, 1, 2, 2, 1, 6, 1, 3]
def baseStart_6360433 : Nat := 118140960795 + 6360433 * 2 ^ 59
def prefixEnd_6360433 : Nat := 4983230072969 + 3 ^ 40 * 6360433 * 2
def baseEnd_6360433 : Nat := 3265959299718618510336407

theorem tailTrace_6360433 : CollatzResearch.WordTrace tailWord_6360433 prefixEnd_6360433 3265959299718618510336407 := by
  unfold tailWord_6360433
  simp only [CollatzResearch.WordTrace]
  refine ⟨231984049766244991318701953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154656033177496660879134635 231984049766244991318701953)
  ·
    refine ⟨173988037324683743489026465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231984049766244991318701953 173988037324683743489026465)
    ·
      refine ⟨130491027993512807616769849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173988037324683743489026465 130491027993512807616769849)
      ·
        refine ⟨97868270995134605712577387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130491027993512807616769849 97868270995134605712577387)
        ·
          refine ⟨146802406492701908568866081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97868270995134605712577387 146802406492701908568866081)
          ·
            refine ⟨110101804869526431426649561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146802406492701908568866081 110101804869526431426649561)
            ·
              refine ⟨82576353652144823569987171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110101804869526431426649561 82576353652144823569987171)
              ·
                refine ⟨123864530478217235354980757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82576353652144823569987171 123864530478217235354980757)
                ·
                  refine ⟨5806149866166432907264723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 123864530478217235354980757 5806149866166432907264723)
                  ·
                    refine ⟨8709224799249649360897085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5806149866166432907264723 8709224799249649360897085)
                    ·
                      refine ⟨3265959299718618510336407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8709224799249649360897085 3265959299718618510336407)
                      ·
                        rfl

theorem cell23_6360433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 6, 1, 3].length) (baseStart_6360433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6360433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6360433 prefixEnd_6360433 := by exact prefixLift 6360433
  have htrace : WordTrace (prefixWord ++ tailWord_6360433) baseStart_6360433 baseEnd_6360433 := by
    simpa [prefixWord, tailWord_6360433, baseEnd_6360433] using wordTrace_append hprefix tailTrace_6360433
  have hstable : (prefixWord ++ tailWord_6360433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6360433).length < 2 ^ (prefixWord ++ tailWord_6360433).sum := by decide
  have hdescent : baseEnd_6360433 < baseStart_6360433 := by decide
  rcases family_descends (prefixWord ++ tailWord_6360433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6360437 : List Nat := [1, 3, 4, 1, 4, 1, 1, 1, 1, 1, 5]
def baseStart_6360437 : Nat := 118140960795 + 6360437 * 2 ^ 59
def prefixEnd_6360437 : Nat := 4983230072969 + 3 ^ 40 * 6360437 * 2
def baseEnd_6360437 : Nat := 3265961353641236494686389

theorem tailTrace_6360437 : CollatzResearch.WordTrace tailWord_6360437 prefixEnd_6360437 3265961353641236494686389 := by
  unfold tailWord_6360437
  simp only [CollatzResearch.WordTrace]
  refine ⟨231984195658230500001847565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154656130438820333334565043 231984195658230500001847565)
  ·
    refine ⟨86994073371836437500692837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 231984195658230500001847565 86994073371836437500692837)
    ·
      refine ⟨16311388757219332031379907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86994073371836437500692837 16311388757219332031379907)
      ·
        refine ⟨24467083135828998047069861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16311388757219332031379907 24467083135828998047069861)
        ·
          refine ⟨4587578087967937133825599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24467083135828998047069861 4587578087967937133825599)
          ·
            refine ⟨6881367131951905700738399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4587578087967937133825599 6881367131951905700738399)
            ·
              refine ⟨10322050697927858551107599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6881367131951905700738399 10322050697927858551107599)
              ·
                refine ⟨15483076046891787826661399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10322050697927858551107599 15483076046891787826661399)
                ·
                  refine ⟨23224614070337681739992099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15483076046891787826661399 23224614070337681739992099)
                  ·
                    refine ⟨34836921105506522609988149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23224614070337681739992099 34836921105506522609988149)
                    ·
                      refine ⟨3265961353641236494686389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34836921105506522609988149 3265961353641236494686389)
                      ·
                        rfl

theorem cell23_6360437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 1, 1, 1, 5].length) (baseStart_6360437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6360437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6360437 prefixEnd_6360437 := by exact prefixLift 6360437
  have htrace : WordTrace (prefixWord ++ tailWord_6360437) baseStart_6360437 baseEnd_6360437 := by
    simpa [prefixWord, tailWord_6360437, baseEnd_6360437] using wordTrace_append hprefix tailTrace_6360437
  have hstable : (prefixWord ++ tailWord_6360437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6360437).length < 2 ^ (prefixWord ++ tailWord_6360437).sum := by decide
  have hdescent : baseEnd_6360437 < baseStart_6360437 := by decide
  rcases family_descends (prefixWord ++ tailWord_6360437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6360451 : List Nat := [1, 1, 1, 3, 5, 3, 2, 2, 1, 2, 2]
def baseStart_6360451 : Nat := 118140960795 + 6360451 * 2 ^ 59
def prefixEnd_6360451 : Nat := 4983230072969 + 3 ^ 40 * 6360451 * 2
def baseEnd_6360451 : Nat := 3265968542370399439911325

theorem tailTrace_6360451 : CollatzResearch.WordTrace tailWord_6360451 prefixEnd_6360451 3265968542370399439911325 := by
  unfold tailWord_6360451
  simp only [CollatzResearch.WordTrace]
  refine ⟨231984706280179780392857207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154656470853453186928571471 231984706280179780392857207)
  ·
    refine ⟨347977059420269670589285811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231984706280179780392857207 347977059420269670589285811)
    ·
      refine ⟨521965589130404505883928717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 347977059420269670589285811 521965589130404505883928717)
      ·
        refine ⟨195737095923901689706473269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 521965589130404505883928717 195737095923901689706473269)
        ·
          refine ⟨18350352742865783409981869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 195737095923901689706473269 18350352742865783409981869)
          ·
            refine ⟨6881382278574668778743201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18350352742865783409981869 6881382278574668778743201)
            ·
              refine ⟨5161036708931001584057401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6881382278574668778743201 5161036708931001584057401)
              ·
                refine ⟨3870777531698251188043051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5161036708931001584057401 3870777531698251188043051)
                ·
                  refine ⟨5806166297547376782064577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3870777531698251188043051 5806166297547376782064577)
                  ·
                    refine ⟨4354624723160532586548433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5806166297547376782064577 4354624723160532586548433)
                    ·
                      refine ⟨3265968542370399439911325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4354624723160532586548433 3265968542370399439911325)
                      ·
                        rfl

theorem cell23_6360451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 2, 2, 1, 2, 2].length) (baseStart_6360451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6360451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6360451 prefixEnd_6360451 := by exact prefixLift 6360451
  have htrace : WordTrace (prefixWord ++ tailWord_6360451) baseStart_6360451 baseEnd_6360451 := by
    simpa [prefixWord, tailWord_6360451, baseEnd_6360451] using wordTrace_append hprefix tailTrace_6360451
  have hstable : (prefixWord ++ tailWord_6360451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6360451).length < 2 ^ (prefixWord ++ tailWord_6360451).sum := by decide
  have hdescent : baseEnd_6360451 < baseStart_6360451 := by decide
  rcases family_descends (prefixWord ++ tailWord_6360451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6360523 : List Nat := [1, 1, 1, 1, 3, 3, 4, 1, 2, 3, 3]
def baseStart_6360523 : Nat := 118140960795 + 6360523 * 2 ^ 59
def prefixEnd_6360523 : Nat := 4983230072969 + 3 ^ 40 * 6360523 * 2
def baseEnd_6360523 : Nat := 3266005512977523158210993

theorem tailTrace_6360523 : CollatzResearch.WordTrace tailWord_6360523 prefixEnd_6360523 3266005512977523158210993 := by
  unfold tailWord_6360523
  simp only [CollatzResearch.WordTrace]
  refine ⟨231987332335918936689478223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154658221557279291126318815 231987332335918936689478223)
  ·
    refine ⟨347980998503878405034217335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231987332335918936689478223 347980998503878405034217335)
    ·
      refine ⟨521971497755817607551326003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 347980998503878405034217335 521971497755817607551326003)
      ·
        refine ⟨782957246633726411326989005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 521971497755817607551326003 782957246633726411326989005)
        ·
          refine ⟨293608967487647404247620877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 782957246633726411326989005 293608967487647404247620877)
          ·
            refine ⟨110103362807867776592857829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 293608967487647404247620877 110103362807867776592857829)
            ·
              refine ⟨20644380526475208111160843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 110103362807867776592857829 20644380526475208111160843)
              ·
                refine ⟨30966570789712812166741265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20644380526475208111160843 30966570789712812166741265)
                ·
                  refine ⟨23224928092284609125055949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30966570789712812166741265 23224928092284609125055949)
                  ·
                    refine ⟨8709348034606728421895981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23224928092284609125055949 8709348034606728421895981)
                    ·
                      refine ⟨3266005512977523158210993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8709348034606728421895981 3266005512977523158210993)
                      ·
                        rfl

theorem cell23_6360523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 1, 2, 3, 3].length) (baseStart_6360523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6360523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6360523 prefixEnd_6360523 := by exact prefixLift 6360523
  have htrace : WordTrace (prefixWord ++ tailWord_6360523) baseStart_6360523 baseEnd_6360523 := by
    simpa [prefixWord, tailWord_6360523, baseEnd_6360523] using wordTrace_append hprefix tailTrace_6360523
  have hstable : (prefixWord ++ tailWord_6360523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6360523).length < 2 ^ (prefixWord ++ tailWord_6360523).sum := by decide
  have hdescent : baseEnd_6360523 < baseStart_6360523 := by decide
  rcases family_descends (prefixWord ++ tailWord_6360523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6360543 : List Nat := [1, 1, 2, 3, 3, 1, 2, 3, 2, 5]
def baseStart_6360543 : Nat := 118140960795 + 6360543 * 2 ^ 59
def prefixEnd_6360543 : Nat := 4983230072969 + 3 ^ 40 * 6360543 * 2
def baseEnd_6360543 : Nat := 1088671927530204359986967

theorem tailTrace_6360543 : CollatzResearch.WordTrace tailWord_6360543 prefixEnd_6360543 1088671927530204359986967 := by
  unfold tailWord_6360543
  simp only [CollatzResearch.WordTrace]
  refine ⟨231988061795846480105206283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154658707863897653403470855 231988061795846480105206283)
  ·
    refine ⟨347982092693769720157809425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231988061795846480105206283 347982092693769720157809425)
    ·
      refine ⟨260986569520327290118357069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 347982092693769720157809425 260986569520327290118357069)
      ·
        refine ⟨97869963570122733794383901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 260986569520327290118357069 97869963570122733794383901)
        ·
          refine ⟨36701236338796025172893963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97869963570122733794383901 36701236338796025172893963)
          ·
            refine ⟨55051854508194037759340945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36701236338796025172893963 55051854508194037759340945)
            ·
              refine ⟨41288890881145528319505709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55051854508194037759340945 41288890881145528319505709)
              ·
                refine ⟨15483334080429573119814641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41288890881145528319505709 15483334080429573119814641)
                ·
                  refine ⟨11612500560322179839860981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15483334080429573119814641 11612500560322179839860981)
                  ·
                    refine ⟨1088671927530204359986967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11612500560322179839860981 1088671927530204359986967)
                    ·
                      rfl

theorem cell23_6360543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 3, 2, 5].length) (baseStart_6360543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6360543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6360543 prefixEnd_6360543 := by exact prefixLift 6360543
  have htrace : WordTrace (prefixWord ++ tailWord_6360543) baseStart_6360543 baseEnd_6360543 := by
    simpa [prefixWord, tailWord_6360543, baseEnd_6360543] using wordTrace_append hprefix tailTrace_6360543
  have hstable : (prefixWord ++ tailWord_6360543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6360543).length < 2 ^ (prefixWord ++ tailWord_6360543).sum := by decide
  have hdescent : baseEnd_6360543 < baseStart_6360543 := by decide
  rcases family_descends (prefixWord ++ tailWord_6360543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6360547 : List Nat := [1, 1, 1, 6, 2, 3, 1, 3, 5]
def baseStart_6360547 : Nat := 118140960795 + 6360547 * 2 ^ 59
def prefixEnd_6360547 : Nat := 4983230072969 + 3 ^ 40 * 6360547 * 2
def baseEnd_6360547 : Nat := 362890870723692340478987

theorem tailTrace_6360547 : CollatzResearch.WordTrace tailWord_6360547 prefixEnd_6360547 362890870723692340478987 := by
  unfold tailWord_6360547
  simp only [CollatzResearch.WordTrace]
  refine ⟨231988207687831988788351895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154658805125221325858901263 231988207687831988788351895)
  ·
    refine ⟨347982311531747983182527843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231988207687831988788351895 347982311531747983182527843)
    ·
      refine ⟨521973467297621974773791765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 347982311531747983182527843 521973467297621974773791765)
      ·
        refine ⟨24467506279576030067521489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 521973467297621974773791765 24467506279576030067521489)
        ·
          refine ⟨18350629709682022550641117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24467506279576030067521489 18350629709682022550641117)
          ·
            refine ⟨6881486141130758456490419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18350629709682022550641117 6881486141130758456490419)
            ·
              refine ⟨10322229211696137684735629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6881486141130758456490419 10322229211696137684735629)
              ·
                refine ⟨3870835954386051631775861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10322229211696137684735629 3870835954386051631775861)
                ·
                  refine ⟨362890870723692340478987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3870835954386051631775861 362890870723692340478987)
                  ·
                    rfl

theorem cell23_6360547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 3, 5].length) (baseStart_6360547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6360547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6360547 prefixEnd_6360547 := by exact prefixLift 6360547
  have htrace : WordTrace (prefixWord ++ tailWord_6360547) baseStart_6360547 baseEnd_6360547 := by
    simpa [prefixWord, tailWord_6360547, baseEnd_6360547] using wordTrace_append hprefix tailTrace_6360547
  have hstable : (prefixWord ++ tailWord_6360547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6360547).length < 2 ^ (prefixWord ++ tailWord_6360547).sum := by decide
  have hdescent : baseEnd_6360547 < baseStart_6360547 := by decide
  rcases family_descends (prefixWord ++ tailWord_6360547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6360640 : List Nat := [2, 1, 1, 2, 2, 2, 1, 4, 1, 5, 2]
def baseStart_6360640 : Nat := 118140960795 + 6360640 * 2 ^ 59
def prefixEnd_6360640 : Nat := 4983230072969 + 3 ^ 40 * 6360640 * 2
def baseEnd_6360640 : Nat := 3266065590214099200447955

theorem tailTrace_6360640 : CollatzResearch.WordTrace tailWord_6360640 prefixEnd_6360640 3266065590214099200447955 := by
  unfold tailWord_6360640
  simp only [CollatzResearch.WordTrace]
  refine ⟨115995799838247532835743687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154661066450996710447658249 115995799838247532835743687)
  ·
    refine ⟨173993699757371299253615531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115995799838247532835743687 173993699757371299253615531)
    ·
      refine ⟨260990549636056948880423297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173993699757371299253615531 260990549636056948880423297)
      ·
        refine ⟨195742912227042711660317473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 260990549636056948880423297 195742912227042711660317473)
        ·
          refine ⟨146807184170282033745238105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 195742912227042711660317473 146807184170282033745238105)
          ·
            refine ⟨110105388127711525308928579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146807184170282033745238105 110105388127711525308928579)
            ·
              refine ⟨165158082191567287963392869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110105388127711525308928579 165158082191567287963392869)
              ·
                refine ⟨30967140410918866493136163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 165158082191567287963392869 30967140410918866493136163)
                ·
                  refine ⟨46450710616378299739704245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30967140410918866493136163 46450710616378299739704245)
                  ·
                    refine ⟨4354754120285465600597273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46450710616378299739704245 4354754120285465600597273)
                    ·
                      refine ⟨3266065590214099200447955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4354754120285465600597273 3266065590214099200447955)
                      ·
                        rfl

theorem cell23_6360640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 4, 1, 5, 2].length) (baseStart_6360640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6360640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6360640 prefixEnd_6360640 := by exact prefixLift 6360640
  have htrace : WordTrace (prefixWord ++ tailWord_6360640) baseStart_6360640 baseEnd_6360640 := by
    simpa [prefixWord, tailWord_6360640, baseEnd_6360640] using wordTrace_append hprefix tailTrace_6360640
  have hstable : (prefixWord ++ tailWord_6360640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6360640).length < 2 ^ (prefixWord ++ tailWord_6360640).sum := by decide
  have hdescent : baseEnd_6360640 < baseStart_6360640 := by decide
  rcases family_descends (prefixWord ++ tailWord_6360640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6360650 : List Nat := [3, 1, 2, 1, 1, 3, 2, 4, 1, 5]
def baseStart_6360650 : Nat := 118140960795 + 6360650 * 2 ^ 59
def prefixEnd_6360650 : Nat := 4983230072969 + 3 ^ 40 * 6360650 * 2
def baseEnd_6360650 : Nat := 1088690241673548053774303

theorem tailTrace_6360650 : CollatzResearch.WordTrace tailWord_6360650 prefixEnd_6360650 1088690241673548053774303 := by
  unfold tailWord_6360650
  simp only [CollatzResearch.WordTrace]
  refine ⟨57997991101614709344837851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154661309604305891586234269 57997991101614709344837851)
  ·
    refine ⟨86996986652422064017256777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57997991101614709344837851 86996986652422064017256777)
    ·
      refine ⟨65247739989316548012942583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86996986652422064017256777 65247739989316548012942583)
      ·
        refine ⟨97871609983974822019413875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65247739989316548012942583 97871609983974822019413875)
        ·
          refine ⟨146807414975962233029120813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97871609983974822019413875 146807414975962233029120813)
          ·
            refine ⟨55052780615985837385920305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 146807414975962233029120813 55052780615985837385920305)
            ·
              refine ⟨41289585461989378039440229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55052780615985837385920305 41289585461989378039440229)
              ·
                refine ⟨7741797274123008382395043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41289585461989378039440229 7741797274123008382395043)
                ·
                  refine ⟨11612695911184512573592565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7741797274123008382395043 11612695911184512573592565)
                  ·
                    refine ⟨1088690241673548053774303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11612695911184512573592565 1088690241673548053774303)
                    ·
                      rfl

theorem cell23_6360650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 4, 1, 5].length) (baseStart_6360650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6360650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6360650 prefixEnd_6360650 := by exact prefixLift 6360650
  have htrace : WordTrace (prefixWord ++ tailWord_6360650) baseStart_6360650 baseEnd_6360650 := by
    simpa [prefixWord, tailWord_6360650, baseEnd_6360650] using wordTrace_append hprefix tailTrace_6360650
  have hstable : (prefixWord ++ tailWord_6360650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6360650).length < 2 ^ (prefixWord ++ tailWord_6360650).sum := by decide
  have hdescent : baseEnd_6360650 < baseStart_6360650 := by decide
  rcases family_descends (prefixWord ++ tailWord_6360650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6360690 : List Nat := [3, 2, 1, 2, 3, 1, 1, 1, 3, 1, 5]
def baseStart_6360690 : Nat := 118140960795 + 6360690 * 2 ^ 59
def prefixEnd_6360690 : Nat := 4983230072969 + 3 ^ 40 * 6360690 * 2
def baseEnd_6360690 : Nat := 3266091264246824004822725

theorem tailTrace_6360690 : CollatzResearch.WordTrace tailWord_6360690 prefixEnd_6360690 3266091264246824004822725 := by
  unfold tailWord_6360690
  simp only [CollatzResearch.WordTrace]
  refine ⟨57998355831578481052701881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154662282217542616140538349 57998355831578481052701881)
  ·
    refine ⟨43498766873683860789526411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57998355831578481052701881 43498766873683860789526411)
    ·
      refine ⟨65248150310525791184289617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43498766873683860789526411 65248150310525791184289617)
      ·
        refine ⟨48936112732894343388217213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65248150310525791184289617 48936112732894343388217213)
        ·
          refine ⟨18351042274835378770581455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48936112732894343388217213 18351042274835378770581455)
          ·
            refine ⟨27526563412253068155872183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18351042274835378770581455 27526563412253068155872183)
            ·
              refine ⟨41289845118379602233808275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27526563412253068155872183 41289845118379602233808275)
              ·
                refine ⟨61934767677569403350712413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41289845118379602233808275 61934767677569403350712413)
                ·
                  refine ⟨23225537879088526256517155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61934767677569403350712413 23225537879088526256517155)
                  ·
                    refine ⟨34838306818632789384775733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23225537879088526256517155 34838306818632789384775733)
                    ·
                      refine ⟨3266091264246824004822725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34838306818632789384775733 3266091264246824004822725)
                      ·
                        rfl

theorem cell23_6360690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 1, 3, 1, 5].length) (baseStart_6360690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6360690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6360690 prefixEnd_6360690 := by exact prefixLift 6360690
  have htrace : WordTrace (prefixWord ++ tailWord_6360690) baseStart_6360690 baseEnd_6360690 := by
    simpa [prefixWord, tailWord_6360690, baseEnd_6360690] using wordTrace_append hprefix tailTrace_6360690
  have hstable : (prefixWord ++ tailWord_6360690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6360690).length < 2 ^ (prefixWord ++ tailWord_6360690).sum := by decide
  have hdescent : baseEnd_6360690 < baseStart_6360690 := by decide
  rcases family_descends (prefixWord ++ tailWord_6360690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6360720 : List Nat := [2, 1, 1, 1, 1, 1, 3, 6, 1, 3, 3]
def baseStart_6360720 : Nat := 118140960795 + 6360720 * 2 ^ 59
def prefixEnd_6360720 : Nat := 4983230072969 + 3 ^ 40 * 6360720 * 2
def baseEnd_6360720 : Nat := 3266106668666458887447587

theorem tailTrace_6360720 : CollatzResearch.WordTrace tailWord_6360720 prefixEnd_6360720 3266106668666458887447587 := by
  unfold tailWord_6360720
  simp only [CollatzResearch.WordTrace]
  refine ⟨115997258758102619667199807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154663011677470159556266409 115997258758102619667199807)
  ·
    refine ⟨173995888137153929500799711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115997258758102619667199807 173995888137153929500799711)
    ·
      refine ⟨260993832205730894251199567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173995888137153929500799711 260993832205730894251199567)
      ·
        refine ⟨391490748308596341376799351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260993832205730894251199567 391490748308596341376799351)
        ·
          refine ⟨587236122462894512065199027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 391490748308596341376799351 587236122462894512065199027)
          ·
            refine ⟨880854183694341768097798541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 587236122462894512065199027 880854183694341768097798541)
            ·
              refine ⟨330320318885378163036674453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 880854183694341768097798541 330320318885378163036674453)
              ·
                refine ⟨15483764947752101392344115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 330320318885378163036674453 15483764947752101392344115)
                ·
                  refine ⟨23225647421628152088516173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15483764947752101392344115 23225647421628152088516173)
                  ·
                    refine ⟨8709617783110557033193565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23225647421628152088516173 8709617783110557033193565)
                    ·
                      refine ⟨3266106668666458887447587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8709617783110557033193565 3266106668666458887447587)
                      ·
                        rfl

theorem cell23_6360720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 6, 1, 3, 3].length) (baseStart_6360720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6360720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6360720 prefixEnd_6360720 := by exact prefixLift 6360720
  have htrace : WordTrace (prefixWord ++ tailWord_6360720) baseStart_6360720 baseEnd_6360720 := by
    simpa [prefixWord, tailWord_6360720, baseEnd_6360720] using wordTrace_append hprefix tailTrace_6360720
  have hstable : (prefixWord ++ tailWord_6360720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6360720).length < 2 ^ (prefixWord ++ tailWord_6360720).sum := by decide
  have hdescent : baseEnd_6360720 < baseStart_6360720 := by decide
  rcases family_descends (prefixWord ++ tailWord_6360720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6360724 : List Nat := [2, 4, 2, 2, 2, 1, 2, 1, 1, 1, 5]
def baseStart_6360724 : Nat := 118140960795 + 6360724 * 2 ^ 59
def prefixEnd_6360724 : Nat := 4983230072969 + 3 ^ 40 * 6360724 * 2
def baseEnd_6360724 : Nat := 3266108722589076871797569

theorem tailTrace_6360724 : CollatzResearch.WordTrace tailWord_6360724 prefixEnd_6360724 3266108722589076871797569 := by
  unfold tailWord_6360724
  simp only [CollatzResearch.WordTrace]
  refine ⟨115997331704095374008772613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154663108938793832011696817 115997331704095374008772613)
  ·
    refine ⟨21749499694517882626644865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115997331704095374008772613 21749499694517882626644865)
    ·
      refine ⟨16312124770888411969983649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21749499694517882626644865 16312124770888411969983649)
      ·
        refine ⟨12234093578166308977487737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16312124770888411969983649 12234093578166308977487737)
        ·
          refine ⟨9175570183624731733115803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12234093578166308977487737 9175570183624731733115803)
          ·
            refine ⟨13763355275437097599673705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9175570183624731733115803 13763355275437097599673705)
            ·
              refine ⟨10322516456577823199755279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13763355275437097599673705 10322516456577823199755279)
              ·
                refine ⟨15483774684866734799632919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10322516456577823199755279 15483774684866734799632919)
                ·
                  refine ⟨23225662027300102199449379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15483774684866734799632919 23225662027300102199449379)
                  ·
                    refine ⟨34838493040950153299174069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23225662027300102199449379 34838493040950153299174069)
                    ·
                      refine ⟨3266108722589076871797569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34838493040950153299174069 3266108722589076871797569)
                      ·
                        rfl

theorem cell23_6360724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_6360724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6360724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6360724 prefixEnd_6360724 := by exact prefixLift 6360724
  have htrace : WordTrace (prefixWord ++ tailWord_6360724) baseStart_6360724 baseEnd_6360724 := by
    simpa [prefixWord, tailWord_6360724, baseEnd_6360724] using wordTrace_append hprefix tailTrace_6360724
  have hstable : (prefixWord ++ tailWord_6360724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6360724).length < 2 ^ (prefixWord ++ tailWord_6360724).sum := by decide
  have hdescent : baseEnd_6360724 < baseStart_6360724 := by decide
  rcases family_descends (prefixWord ++ tailWord_6360724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6360758 : List Nat := [5, 1, 3, 1, 1, 3, 1, 2, 1, 2, 3]
def baseStart_6360758 : Nat := 118140960795 + 6360758 * 2 ^ 59
def prefixEnd_6360758 : Nat := 4983230072969 + 3 ^ 40 * 6360758 * 2
def baseEnd_6360758 : Nat := 3266126180931329738772413

theorem tailTrace_6360758 : CollatzResearch.WordTrace tailWord_6360758 prefixEnd_6360758 3266126180931329738772413 := by
  unfold tailWord_6360758
  simp only [CollatzResearch.WordTrace]
  refine ⟨14499743968129223239017683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 154663935660045047882855285 14499743968129223239017683)
  ·
    refine ⟨21749615952193834858526525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14499743968129223239017683 21749615952193834858526525)
    ·
      refine ⟨8156105982072688071947447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21749615952193834858526525 8156105982072688071947447)
      ·
        refine ⟨12234158973109032107921171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8156105982072688071947447 12234158973109032107921171)
        ·
          refine ⟨18351238459663548161881757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12234158973109032107921171 18351238459663548161881757)
          ·
            refine ⟨6881714422373830560705659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18351238459663548161881757 6881714422373830560705659)
            ·
              refine ⟨10322571633560745841058489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6881714422373830560705659 10322571633560745841058489)
              ·
                refine ⟨7741928725170559380793867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10322571633560745841058489 7741928725170559380793867)
                ·
                  refine ⟨11612893087755839071190801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7741928725170559380793867 11612893087755839071190801)
                  ·
                    refine ⟨8709669815816879303393101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11612893087755839071190801 8709669815816879303393101)
                    ·
                      refine ⟨3266126180931329738772413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8709669815816879303393101 3266126180931329738772413)
                      ·
                        rfl

theorem cell23_6360758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_6360758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6360758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6360758 prefixEnd_6360758 := by exact prefixLift 6360758
  have htrace : WordTrace (prefixWord ++ tailWord_6360758) baseStart_6360758 baseEnd_6360758 := by
    simpa [prefixWord, tailWord_6360758, baseEnd_6360758] using wordTrace_append hprefix tailTrace_6360758
  have hstable : (prefixWord ++ tailWord_6360758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6360758).length < 2 ^ (prefixWord ++ tailWord_6360758).sum := by decide
  have hdescent : baseEnd_6360758 < baseStart_6360758 := by decide
  rcases family_descends (prefixWord ++ tailWord_6360758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6360764 : List Nat := [2, 2, 2, 3, 1, 3, 1, 1, 3, 3, 2]
def baseStart_6360764 : Nat := 118140960795 + 6360764 * 2 ^ 59
def prefixEnd_6360764 : Nat := 4983230072969 + 3 ^ 40 * 6360764 * 2
def baseEnd_6360764 : Nat := 3266129261815256715297385

theorem tailTrace_6360764 : CollatzResearch.WordTrace tailWord_6360764 prefixEnd_6360764 3266129261815256715297385 := by
  unfold tailWord_6360764
  simp only [CollatzResearch.WordTrace]
  refine ⟨115998061164022917424500673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154664081552030556566000897 115998061164022917424500673)
  ·
    refine ⟨86998545873017188068375505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115998061164022917424500673 86998545873017188068375505)
    ·
      refine ⟨65248909404762891051281629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86998545873017188068375505 65248909404762891051281629)
      ·
        refine ⟨24468341026786084144230611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65248909404762891051281629 24468341026786084144230611)
        ·
          refine ⟨36702511540179126216345917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24468341026786084144230611 36702511540179126216345917)
          ·
            refine ⟨13763441827567172331129719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36702511540179126216345917 13763441827567172331129719)
            ·
              refine ⟨20645162741350758496694579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13763441827567172331129719 20645162741350758496694579)
              ·
                refine ⟨30967744112026137745041869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20645162741350758496694579 30967744112026137745041869)
                ·
                  refine ⟨11612904042009801654390701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30967744112026137745041869 11612904042009801654390701)
                  ·
                    refine ⟨4354839015753675620396513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11612904042009801654390701 4354839015753675620396513)
                    ·
                      refine ⟨3266129261815256715297385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4354839015753675620396513 3266129261815256715297385)
                      ·
                        rfl

theorem cell23_6360764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 1, 3, 3, 2].length) (baseStart_6360764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6360764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6360764 prefixEnd_6360764 := by exact prefixLift 6360764
  have htrace : WordTrace (prefixWord ++ tailWord_6360764) baseStart_6360764 baseEnd_6360764 := by
    simpa [prefixWord, tailWord_6360764, baseEnd_6360764] using wordTrace_append hprefix tailTrace_6360764
  have hstable : (prefixWord ++ tailWord_6360764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6360764).length < 2 ^ (prefixWord ++ tailWord_6360764).sum := by decide
  have hdescent : baseEnd_6360764 < baseStart_6360764 := by decide
  rcases family_descends (prefixWord ++ tailWord_6360764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6360862 : List Nat := [4, 3, 2, 2, 2, 1, 1, 1, 1, 4, 2]
def baseStart_6360862 : Nat := 118140960795 + 6360862 * 2 ^ 59
def prefixEnd_6360862 : Nat := 4983230072969 + 3 ^ 40 * 6360862 * 2
def baseEnd_6360862 : Nat := 3266179582919397331871935

theorem tailTrace_6360862 : CollatzResearch.WordTrace tailWord_6360862 prefixEnd_6360862 3266179582919397331871935 := by
  unfold tailWord_6360862
  simp only [CollatzResearch.WordTrace]
  refine ⟨28999962085211349698258605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154666464454460531724045893 28999962085211349698258605)
  ·
    refine ⟨10874985781954256136846977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28999962085211349698258605 10874985781954256136846977)
    ·
      refine ⟨8156239336465692102635233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10874985781954256136846977 8156239336465692102635233)
      ·
        refine ⟨6117179502349269076976425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8156239336465692102635233 6117179502349269076976425)
        ·
          refine ⟨4587884626761951807732319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6117179502349269076976425 4587884626761951807732319)
          ·
            refine ⟨6881826940142927711598479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4587884626761951807732319 6881826940142927711598479)
            ·
              refine ⟨10322740410214391567397719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6881826940142927711598479 10322740410214391567397719)
              ·
                refine ⟨15484110615321587351096579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10322740410214391567397719 15484110615321587351096579)
                ·
                  refine ⟨23226165922982381026644869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15484110615321587351096579 23226165922982381026644869)
                  ·
                    refine ⟨4354906110559196442495913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23226165922982381026644869 4354906110559196442495913)
                    ·
                      refine ⟨3266179582919397331871935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4354906110559196442495913 3266179582919397331871935)
                      ·
                        rfl

theorem cell23_6360862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_6360862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6360862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6360862 prefixEnd_6360862 := by exact prefixLift 6360862
  have htrace : WordTrace (prefixWord ++ tailWord_6360862) baseStart_6360862 baseEnd_6360862 := by
    simpa [prefixWord, tailWord_6360862, baseEnd_6360862] using wordTrace_append hprefix tailTrace_6360862
  have hstable : (prefixWord ++ tailWord_6360862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6360862).length < 2 ^ (prefixWord ++ tailWord_6360862).sum := by decide
  have hdescent : baseEnd_6360862 < baseStart_6360862 := by decide
  rcases family_descends (prefixWord ++ tailWord_6360862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6360884 : List Nat := [2, 5, 1, 1, 2, 1, 2, 1, 1, 3, 4]
def baseStart_6360884 : Nat := 118140960795 + 6360884 * 2 ^ 59
def prefixEnd_6360884 : Nat := 4983230072969 + 3 ^ 40 * 6360884 * 2
def baseEnd_6360884 : Nat := 3266190879493796245796833

theorem tailTrace_6360884 : CollatzResearch.WordTrace tailWord_6360884 prefixEnd_6360884 3266190879493796245796833 := by
  unfold tailWord_6360884
  simp only [CollatzResearch.WordTrace]
  refine ⟨116000249543805547671684853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154666999391740730228913137 116000249543805547671684853)
  ·
    refine ⟨10875023394731770094220455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 116000249543805547671684853 10875023394731770094220455)
    ·
      refine ⟨16312535092097655141330683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10875023394731770094220455 16312535092097655141330683)
      ·
        refine ⟨24468802638146482711996025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16312535092097655141330683 24468802638146482711996025)
        ·
          refine ⟨18351601978609862033997019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24468802638146482711996025 18351601978609862033997019)
          ·
            refine ⟨27527402967914793050995529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18351601978609862033997019 27527402967914793050995529)
            ·
              refine ⟨20645552225936094788246647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27527402967914793050995529 20645552225936094788246647)
              ·
                refine ⟨30968328338904142182369971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20645552225936094788246647 30968328338904142182369971)
                ·
                  refine ⟨46452492508356213273554957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30968328338904142182369971 46452492508356213273554957)
                  ·
                    refine ⟨17419684690633579977583109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46452492508356213273554957 17419684690633579977583109)
                    ·
                      refine ⟨3266190879493796245796833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17419684690633579977583109 3266190879493796245796833)
                      ·
                        rfl

theorem cell23_6360884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_6360884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6360884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6360884 prefixEnd_6360884 := by exact prefixLift 6360884
  have htrace : WordTrace (prefixWord ++ tailWord_6360884) baseStart_6360884 baseEnd_6360884 := by
    simpa [prefixWord, tailWord_6360884, baseEnd_6360884] using wordTrace_append hprefix tailTrace_6360884
  have hstable : (prefixWord ++ tailWord_6360884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6360884).length < 2 ^ (prefixWord ++ tailWord_6360884).sum := by decide
  have hdescent : baseEnd_6360884 < baseStart_6360884 := by decide
  rcases family_descends (prefixWord ++ tailWord_6360884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6360904 : List Nat := [2, 1, 3, 1, 1, 5, 1, 2, 2, 2, 3]
def baseStart_6360904 : Nat := 118140960795 + 6360904 * 2 ^ 59
def prefixEnd_6360904 : Nat := 4983230072969 + 3 ^ 40 * 6360904 * 2
def baseEnd_6360904 : Nat := 3266201149106886167546741

theorem tailTrace_6360904 : CollatzResearch.WordTrace tailWord_6360904 prefixEnd_6360904 3266201149106886167546741 := by
  unfold tailWord_6360904
  simp only [CollatzResearch.WordTrace]
  refine ⟨116000614273769319379548883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154667485698359092506065177 116000614273769319379548883)
  ·
    refine ⟨174000921410653979069323325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116000614273769319379548883 174000921410653979069323325)
    ·
      refine ⟨65250345528995242150996247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174000921410653979069323325 65250345528995242150996247)
      ·
        refine ⟨97875518293492863226494371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65250345528995242150996247 97875518293492863226494371)
        ·
          refine ⟨146813277440239294839741557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97875518293492863226494371 146813277440239294839741557)
          ·
            refine ⟨13763744760022433891225771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 146813277440239294839741557 13763744760022433891225771)
            ·
              refine ⟨20645617140033650836838657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13763744760022433891225771 20645617140033650836838657)
              ·
                refine ⟨15484212855025238127628993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20645617140033650836838657 15484212855025238127628993)
                ·
                  refine ⟨11613159641268928595721745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15484212855025238127628993 11613159641268928595721745)
                  ·
                    refine ⟨8709869730951696446791309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11613159641268928595721745 8709869730951696446791309)
                    ·
                      refine ⟨3266201149106886167546741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8709869730951696446791309 3266201149106886167546741)
                      ·
                        rfl

theorem cell23_6360904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 2, 2, 2, 3].length) (baseStart_6360904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6360904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6360904 prefixEnd_6360904 := by exact prefixLift 6360904
  have htrace : WordTrace (prefixWord ++ tailWord_6360904) baseStart_6360904 baseEnd_6360904 := by
    simpa [prefixWord, tailWord_6360904, baseEnd_6360904] using wordTrace_append hprefix tailTrace_6360904
  have hstable : (prefixWord ++ tailWord_6360904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6360904).length < 2 ^ (prefixWord ++ tailWord_6360904).sum := by decide
  have hdescent : baseEnd_6360904 < baseStart_6360904 := by decide
  rcases family_descends (prefixWord ++ tailWord_6360904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6360920 : List Nat := [2, 1, 2, 2, 1, 1, 1, 1, 1, 11]
def baseStart_6360920 : Nat := 118140960795 + 6360920 * 2 ^ 59
def prefixEnd_6360920 : Nat := 4983230072969 + 3 ^ 40 * 6360920 * 2
def baseEnd_6360920 : Nat := 1088736454932452701648889

theorem tailTrace_6360920 : CollatzResearch.WordTrace tailWord_6360920 prefixEnd_6360920 1088736454932452701648889 := by
  unfold tailWord_6360920
  simp only [CollatzResearch.WordTrace]
  refine ⟨116000906057740336745840107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154667874743653782327786809 116000906057740336745840107)
  ·
    refine ⟨174001359086610505118760161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116000906057740336745840107 174001359086610505118760161)
    ·
      refine ⟨130501019314957878839070121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174001359086610505118760161 130501019314957878839070121)
      ·
        refine ⟨97875764486218409129302591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130501019314957878839070121 97875764486218409129302591)
        ·
          refine ⟨146813646729327613693953887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97875764486218409129302591 146813646729327613693953887)
          ·
            refine ⟨220220470093991420540930831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146813646729327613693953887 220220470093991420540930831)
            ·
              refine ⟨330330705140987130811396247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 220220470093991420540930831 330330705140987130811396247)
              ·
                refine ⟨495496057711480696217094371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 330330705140987130811396247 495496057711480696217094371)
                ·
                  refine ⟨743244086567221044325641557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 495496057711480696217094371 743244086567221044325641557)
                  ·
                    refine ⟨1088736454932452701648889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 743244086567221044325641557 1088736454932452701648889)
                    ·
                      rfl

theorem cell23_6360920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 1, 11].length) (baseStart_6360920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6360920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6360920 prefixEnd_6360920 := by exact prefixLift 6360920
  have htrace : WordTrace (prefixWord ++ tailWord_6360920) baseStart_6360920 baseEnd_6360920 := by
    simpa [prefixWord, tailWord_6360920, baseEnd_6360920] using wordTrace_append hprefix tailTrace_6360920
  have hstable : (prefixWord ++ tailWord_6360920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6360920).length < 2 ^ (prefixWord ++ tailWord_6360920).sum := by decide
  have hdescent : baseEnd_6360920 < baseStart_6360920 := by decide
  rcases family_descends (prefixWord ++ tailWord_6360920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6360938 : List Nat := [3, 1, 3, 4, 1, 1, 2, 1, 2, 2, 3]
def baseStart_6360938 : Nat := 118140960795 + 6360938 * 2 ^ 59
def prefixEnd_6360938 : Nat := 4983230072969 + 3 ^ 40 * 6360938 * 2
def baseEnd_6360938 : Nat := 3266218607449139034521585

theorem tailTrace_6360938 : CollatzResearch.WordTrace tailWord_6360938 prefixEnd_6360938 3266218607449139034521585 := by
  unfold tailWord_6360938
  simp only [CollatzResearch.WordTrace]
  refine ⟨58000617157353865641458867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154668312419610308377223645 58000617157353865641458867)
  ·
    refine ⟨87000925736030798462188301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58000617157353865641458867 87000925736030798462188301)
    ·
      refine ⟨32625347151011549423320613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87000925736030798462188301 32625347151011549423320613)
      ·
        refine ⟨6117252590814665516872615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32625347151011549423320613 6117252590814665516872615)
        ·
          refine ⟨9175878886221998275308923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6117252590814665516872615 9175878886221998275308923)
          ·
            refine ⟨13763818329332997412963385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9175878886221998275308923 13763818329332997412963385)
            ·
              refine ⟨10322863746999748059722539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13763818329332997412963385 10322863746999748059722539)
              ·
                refine ⟨15484295620499622089583809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10322863746999748059722539 15484295620499622089583809)
                ·
                  refine ⟨11613221715374716567187857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15484295620499622089583809 11613221715374716567187857)
                  ·
                    refine ⟨8709916286531037425390893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11613221715374716567187857 8709916286531037425390893)
                    ·
                      refine ⟨3266218607449139034521585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8709916286531037425390893 3266218607449139034521585)
                      ·
                        rfl

theorem cell23_6360938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_6360938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6360938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6360938 prefixEnd_6360938 := by exact prefixLift 6360938
  have htrace : WordTrace (prefixWord ++ tailWord_6360938) baseStart_6360938 baseEnd_6360938 := by
    simpa [prefixWord, tailWord_6360938, baseEnd_6360938] using wordTrace_append hprefix tailTrace_6360938
  have hstable : (prefixWord ++ tailWord_6360938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6360938).length < 2 ^ (prefixWord ++ tailWord_6360938).sum := by decide
  have hdescent : baseEnd_6360938 < baseStart_6360938 := by decide
  rcases family_descends (prefixWord ++ tailWord_6360938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6360977 : List Nat := [1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 5]
def baseStart_6360977 : Nat := 118140960795 + 6360977 * 2 ^ 59
def prefixEnd_6360977 : Nat := 4983230072969 + 3 ^ 40 * 6360977 * 2
def baseEnd_6360977 : Nat := 3266238633194664381933905

theorem tailTrace_6360977 : CollatzResearch.WordTrace tailWord_6360977 prefixEnd_6360977 3266238633194664381933905 := by
  unfold tailWord_6360977
  simp only [CollatzResearch.WordTrace]
  refine ⟨232003891076274172226505185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154669260717516114817670123 232003891076274172226505185)
  ·
    refine ⟨174002918307205629169878889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232003891076274172226505185 174002918307205629169878889)
    ·
      refine ⟨130502188730404221877409167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174002918307205629169878889 130502188730404221877409167)
      ·
        refine ⟨195753283095606332816113751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130502188730404221877409167 195753283095606332816113751)
        ·
          refine ⟨293629924643409499224170627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195753283095606332816113751 293629924643409499224170627)
          ·
            refine ⟨440444886965114248836255941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 293629924643409499224170627 440444886965114248836255941)
            ·
              refine ⟨82583416305958921656797989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 440444886965114248836255941 82583416305958921656797989)
              ·
                refine ⟨15484390557367297810649623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82583416305958921656797989 15484390557367297810649623)
                ·
                  refine ⟨23226585836050946715974435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15484390557367297810649623 23226585836050946715974435)
                  ·
                    refine ⟨34839878754076420073961653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23226585836050946715974435 34839878754076420073961653)
                    ·
                      refine ⟨3266238633194664381933905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34839878754076420073961653 3266238633194664381933905)
                      ·
                        rfl

theorem cell23_6360977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 5].length) (baseStart_6360977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6360977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6360977 prefixEnd_6360977 := by exact prefixLift 6360977
  have htrace : WordTrace (prefixWord ++ tailWord_6360977) baseStart_6360977 baseEnd_6360977 := by
    simpa [prefixWord, tailWord_6360977, baseEnd_6360977] using wordTrace_append hprefix tailTrace_6360977
  have hstable : (prefixWord ++ tailWord_6360977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6360977).length < 2 ^ (prefixWord ++ tailWord_6360977).sum := by decide
  have hdescent : baseEnd_6360977 < baseStart_6360977 := by decide
  rcases family_descends (prefixWord ++ tailWord_6360977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6361057 : List Nat := [1, 2, 3, 1, 2, 1, 2, 2, 1, 8]
def baseStart_6361057 : Nat := 118140960795 + 6361057 * 2 ^ 59
def prefixEnd_6361057 : Nat := 4983230072969 + 3 ^ 40 * 6361057 * 2
def baseEnd_6361057 : Nat := 1088759903882341356311179

theorem tailTrace_6361057 : CollatzResearch.WordTrace tailWord_6361057 prefixEnd_6361057 1088759903882341356311179 := by
  unfold tailWord_6361057
  simp only [CollatzResearch.WordTrace]
  refine ⟨232006808915984345889417425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154671205943989563926278283 232006808915984345889417425)
  ·
    refine ⟨174005106686988259417063069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232006808915984345889417425 174005106686988259417063069)
    ·
      refine ⟨65251915007620597281398651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174005106686988259417063069 65251915007620597281398651)
      ·
        refine ⟨97877872511430895922097977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65251915007620597281398651 97877872511430895922097977)
        ·
          refine ⟨73408404383573171941573483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97877872511430895922097977 73408404383573171941573483)
          ·
            refine ⟨110112606575359757912360225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73408404383573171941573483 110112606575359757912360225)
            ·
              refine ⟨82584454931519818434270169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110112606575359757912360225 82584454931519818434270169)
              ·
                refine ⟨61938341198639863825702627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82584454931519818434270169 61938341198639863825702627)
                ·
                  refine ⟨92907511797959795738553941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61938341198639863825702627 92907511797959795738553941)
                  ·
                    refine ⟨1088759903882341356311179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 92907511797959795738553941 1088759903882341356311179)
                    ·
                      rfl

theorem cell23_6361057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 2, 1, 8].length) (baseStart_6361057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6361057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6361057 prefixEnd_6361057 := by exact prefixLift 6361057
  have htrace : WordTrace (prefixWord ++ tailWord_6361057) baseStart_6361057 baseEnd_6361057 := by
    simpa [prefixWord, tailWord_6361057, baseEnd_6361057] using wordTrace_append hprefix tailTrace_6361057
  have hstable : (prefixWord ++ tailWord_6361057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6361057).length < 2 ^ (prefixWord ++ tailWord_6361057).sum := by decide
  have hdescent : baseEnd_6361057 < baseStart_6361057 := by decide
  rcases family_descends (prefixWord ++ tailWord_6361057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6361084 : List Nat := [2, 2, 2, 1, 2, 2, 2, 1, 2, 4, 3]
def baseStart_6361084 : Nat := 118140960795 + 6361084 * 2 ^ 59
def prefixEnd_6361084 : Nat := 4983230072969 + 3 ^ 40 * 6361084 * 2
def baseEnd_6361084 : Nat := 3266293575624695463295913

theorem tailTrace_6361084 : CollatzResearch.WordTrace tailWord_6361084 prefixEnd_6361084 3266293575624695463295913 := by
  unfold tailWord_6361084
  simp only [CollatzResearch.WordTrace]
  refine ⟨116003896843443264750325153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154671862457924353000433537 116003896843443264750325153)
  ·
    refine ⟨87002922632582448562743865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116003896843443264750325153 87002922632582448562743865)
    ·
      refine ⟨65252191974436836422057899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87002922632582448562743865 65252191974436836422057899)
      ·
        refine ⟨97878287961655254633086849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65252191974436836422057899 97878287961655254633086849)
        ·
          refine ⟨73408715971241440974815137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97878287961655254633086849 73408715971241440974815137)
          ·
            refine ⟨55056536978431080731111353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73408715971241440974815137 55056536978431080731111353)
            ·
              refine ⟨41292402733823310548333515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55056536978431080731111353 41292402733823310548333515)
              ·
                refine ⟨61938604100734965822500273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41292402733823310548333515 61938604100734965822500273)
                ·
                  refine ⟨46453953075551224366875205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61938604100734965822500273 46453953075551224366875205)
                  ·
                    refine ⟨8710116201665854568789101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46453953075551224366875205 8710116201665854568789101)
                    ·
                      refine ⟨3266293575624695463295913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8710116201665854568789101 3266293575624695463295913)
                      ·
                        rfl

theorem cell23_6361084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 4, 3].length) (baseStart_6361084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6361084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6361084 prefixEnd_6361084 := by exact prefixLift 6361084
  have htrace : WordTrace (prefixWord ++ tailWord_6361084) baseStart_6361084 baseEnd_6361084 := by
    simpa [prefixWord, tailWord_6361084, baseEnd_6361084] using wordTrace_append hprefix tailTrace_6361084
  have hstable : (prefixWord ++ tailWord_6361084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6361084).length < 2 ^ (prefixWord ++ tailWord_6361084).sum := by decide
  have hdescent : baseEnd_6361084 < baseStart_6361084 := by decide
  rcases family_descends (prefixWord ++ tailWord_6361084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6361138 : List Nat := [3, 2, 1, 1, 2, 3, 4, 2, 5]
def baseStart_6361138 : Nat := 118140960795 + 6361138 * 2 ^ 59
def prefixEnd_6361138 : Nat := 4983230072969 + 3 ^ 40 * 6361138 * 2
def baseEnd_6361138 : Nat := 362924589286670916891185

theorem tailTrace_6361138 : CollatzResearch.WordTrace tailWord_6361138 prefixEnd_6361138 362924589286670916891185 := by
  unfold tailWord_6361138
  simp only [CollatzResearch.WordTrace]
  refine ⟨58002440807172724180779017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154673175485793931148744045 58002440807172724180779017)
  ·
    refine ⟨43501830605379543135584263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58002440807172724180779017 43501830605379543135584263)
    ·
      refine ⟨65252745908069314703376395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43501830605379543135584263 65252745908069314703376395)
      ·
        refine ⟨97879118862103972055064593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65252745908069314703376395 97879118862103972055064593)
        ·
          refine ⟨73409339146577979041298445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97879118862103972055064593 73409339146577979041298445)
          ·
            refine ⟨27528502179966742140486917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73409339146577979041298445 27528502179966742140486917)
            ·
              refine ⟨5161594158743764151341297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27528502179966742140486917 5161594158743764151341297)
              ·
                refine ⟨3871195619057823113505973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5161594158743764151341297 3871195619057823113505973)
                ·
                  refine ⟨362924589286670916891185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3871195619057823113505973 362924589286670916891185)
                  ·
                    rfl

theorem cell23_6361138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 4, 2, 5].length) (baseStart_6361138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6361138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6361138 prefixEnd_6361138 := by exact prefixLift 6361138
  have htrace : WordTrace (prefixWord ++ tailWord_6361138) baseStart_6361138 baseEnd_6361138 := by
    simpa [prefixWord, tailWord_6361138, baseEnd_6361138] using wordTrace_append hprefix tailTrace_6361138
  have hstable : (prefixWord ++ tailWord_6361138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6361138).length < 2 ^ (prefixWord ++ tailWord_6361138).sum := by decide
  have hdescent : baseEnd_6361138 < baseStart_6361138 := by decide
  rcases family_descends (prefixWord ++ tailWord_6361138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6361141 : List Nat := [1, 3, 3, 1, 1, 1, 3, 1, 2, 5, 2]
def baseStart_6361141 : Nat := 118140960795 + 6361141 * 2 ^ 59
def prefixEnd_6361141 : Nat := 4983230072969 + 3 ^ 40 * 6361141 * 2
def baseEnd_6361141 : Nat := 3266322844022001740283151

theorem tailTrace_6361141 : CollatzResearch.WordTrace tailWord_6361141 prefixEnd_6361141 3266322844022001740283151 := by
  unfold tailWord_6361141
  simp only [CollatzResearch.WordTrace]
  refine ⟨232009872647680028235475277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154673248431786685490316851 232009872647680028235475277)
  ·
    refine ⟨87003702242880010588303229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 232009872647680028235475277 87003702242880010588303229)
    ·
      refine ⟨32626388341080003970613711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87003702242880010588303229 32626388341080003970613711)
      ·
        refine ⟨48939582511620005955920567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32626388341080003970613711 48939582511620005955920567)
        ·
          refine ⟨73409373767430008933880851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48939582511620005955920567 73409373767430008933880851)
          ·
            refine ⟨110114060651145013400821277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73409373767430008933880851 110114060651145013400821277)
            ·
              refine ⟨41292772744179380025307979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110114060651145013400821277 41292772744179380025307979)
              ·
                refine ⟨61939159116269070037961969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41292772744179380025307979 61939159116269070037961969)
                ·
                  refine ⟨46454369337201802528471477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61939159116269070037961969 46454369337201802528471477)
                  ·
                    refine ⟨4355097125362668987044201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46454369337201802528471477 4355097125362668987044201)
                    ·
                      refine ⟨3266322844022001740283151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4355097125362668987044201 3266322844022001740283151)
                      ·
                        rfl

theorem cell23_6361141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 1, 2, 5, 2].length) (baseStart_6361141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6361141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6361141 prefixEnd_6361141 := by exact prefixLift 6361141
  have htrace : WordTrace (prefixWord ++ tailWord_6361141) baseStart_6361141 baseEnd_6361141 := by
    simpa [prefixWord, tailWord_6361141, baseEnd_6361141] using wordTrace_append hprefix tailTrace_6361141
  have hstable : (prefixWord ++ tailWord_6361141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6361141).length < 2 ^ (prefixWord ++ tailWord_6361141).sum := by decide
  have hdescent : baseEnd_6361141 < baseStart_6361141 := by decide
  rcases family_descends (prefixWord ++ tailWord_6361141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6361184 : List Nat := [2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 6]
def baseStart_6361184 : Nat := 118140960795 + 6361184 * 2 ^ 59
def prefixEnd_6361184 : Nat := 4983230072969 + 3 ^ 40 * 6361184 * 2
def baseEnd_6361184 : Nat := 3266344923690145072045453

theorem tailTrace_6361184 : CollatzResearch.WordTrace tailWord_6361184 prefixEnd_6361184 3266344923690145072045453 := by
  unfold tailWord_6361184
  simp only [CollatzResearch.WordTrace]
  refine ⟨116005720493262123289645303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154674293991016164386193737 116005720493262123289645303)
  ·
    refine ⟨174008580739893184934467955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116005720493262123289645303 174008580739893184934467955)
    ·
      refine ⟨261012871109839777401701933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174008580739893184934467955 261012871109839777401701933)
      ·
        refine ⟨97879826666189916525638225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 261012871109839777401701933 97879826666189916525638225)
        ·
          refine ⟨73409869999642437394228669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97879826666189916525638225 73409869999642437394228669)
          ·
            refine ⟨27528701249865914022835751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73409869999642437394228669 27528701249865914022835751)
            ·
              refine ⟨41293051874798871034253627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27528701249865914022835751 41293051874798871034253627)
              ·
                refine ⟨61939577812198306551380441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41293051874798871034253627 61939577812198306551380441)
                ·
                  refine ⟨46454683359148729913535331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61939577812198306551380441 46454683359148729913535331)
                  ·
                    refine ⟨69682025038723094870302997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46454683359148729913535331 69682025038723094870302997)
                    ·
                      refine ⟨3266344923690145072045453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69682025038723094870302997 3266344923690145072045453)
                      ·
                        rfl

theorem cell23_6361184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 6].length) (baseStart_6361184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6361184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6361184 prefixEnd_6361184 := by exact prefixLift 6361184
  have htrace : WordTrace (prefixWord ++ tailWord_6361184) baseStart_6361184 baseEnd_6361184 := by
    simpa [prefixWord, tailWord_6361184, baseEnd_6361184] using wordTrace_append hprefix tailTrace_6361184
  have hstable : (prefixWord ++ tailWord_6361184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6361184).length < 2 ^ (prefixWord ++ tailWord_6361184).sum := by decide
  have hdescent : baseEnd_6361184 < baseStart_6361184 := by decide
  rcases family_descends (prefixWord ++ tailWord_6361184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6361191 : List Nat := [1, 1, 5, 1, 1, 2, 2, 1, 4, 2, 3]
def baseStart_6361191 : Nat := 118140960795 + 6361191 * 2 ^ 59
def prefixEnd_6361191 : Nat := 4983230072969 + 3 ^ 40 * 6361191 * 2
def baseEnd_6361191 : Nat := 3266348518054726544657921

theorem tailTrace_6361191 : CollatzResearch.WordTrace tailWord_6361191 prefixEnd_6361191 3266348518054726544657921 := by
  unfold tailWord_6361191
  simp only [CollatzResearch.WordTrace]
  refine ⟨232011696297498886774795427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154674464198332591183196951 232011696297498886774795427)
  ·
    refine ⟨348017544446248330162193141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232011696297498886774795427 348017544446248330162193141)
    ·
      refine ⟨32626644791835780952705607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 348017544446248330162193141 32626644791835780952705607)
      ·
        refine ⟨48939967187753671429058411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32626644791835780952705607 48939967187753671429058411)
        ·
          refine ⟨73409950781630507143587617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48939967187753671429058411 73409950781630507143587617)
          ·
            refine ⟨55057463086222880357690713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73409950781630507143587617 55057463086222880357690713)
            ·
              refine ⟨41293097314667160268268035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55057463086222880357690713 41293097314667160268268035)
              ·
                refine ⟨61939645972000740402402053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41293097314667160268268035 61939645972000740402402053)
                ·
                  refine ⟨11613683619750138825450385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61939645972000740402402053 11613683619750138825450385)
                  ·
                    refine ⟨8710262714812604119087789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11613683619750138825450385 8710262714812604119087789)
                    ·
                      refine ⟨3266348518054726544657921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8710262714812604119087789 3266348518054726544657921)
                      ·
                        rfl

theorem cell23_6361191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 1, 4, 2, 3].length) (baseStart_6361191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6361191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6361191 prefixEnd_6361191 := by exact prefixLift 6361191
  have htrace : WordTrace (prefixWord ++ tailWord_6361191) baseStart_6361191 baseEnd_6361191 := by
    simpa [prefixWord, tailWord_6361191, baseEnd_6361191] using wordTrace_append hprefix tailTrace_6361191
  have hstable : (prefixWord ++ tailWord_6361191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6361191).length < 2 ^ (prefixWord ++ tailWord_6361191).sum := by decide
  have hdescent : baseEnd_6361191 < baseStart_6361191 := by decide
  rcases family_descends (prefixWord ++ tailWord_6361191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6361198 : List Nat := [4, 1, 2, 2, 1, 1, 4, 1, 3, 4]
def baseStart_6361198 : Nat := 118140960795 + 6361198 * 2 ^ 59
def prefixEnd_6361198 : Nat := 4983230072969 + 3 ^ 40 * 6361198 * 2
def baseEnd_6361198 : Nat := 1088784037473102672423463

theorem tailTrace_6361198 : CollatzResearch.WordTrace tailWord_6361198 prefixEnd_6361198 1088784037473102672423463 := by
  unfold tailWord_6361198
  simp only [CollatzResearch.WordTrace]
  refine ⟨29001493951059190871287531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154674634405649017980200165 29001493951059190871287531)
  ·
    refine ⟨43502240926588786306931297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29001493951059190871287531 43502240926588786306931297)
    ·
      refine ⟨32626680694941589730198473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43502240926588786306931297 32626680694941589730198473)
      ·
        refine ⟨24470010521206192297648855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32626680694941589730198473 24470010521206192297648855)
        ·
          refine ⟨36705015781809288446473283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24470010521206192297648855 36705015781809288446473283)
          ·
            refine ⟨55057523672713932669709925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36705015781809288446473283 55057523672713932669709925)
            ·
              refine ⟨10323285688633862375570611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55057523672713932669709925 10323285688633862375570611)
              ·
                refine ⟨15484928532950793563355917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10323285688633862375570611 15484928532950793563355917)
                ·
                  refine ⟨5806848199856547586258469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15484928532950793563355917 5806848199856547586258469)
                  ·
                    refine ⟨1088784037473102672423463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5806848199856547586258469 1088784037473102672423463)
                    ·
                      rfl

theorem cell23_6361198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 1, 3, 4].length) (baseStart_6361198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6361198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6361198 prefixEnd_6361198 := by exact prefixLift 6361198
  have htrace : WordTrace (prefixWord ++ tailWord_6361198) baseStart_6361198 baseEnd_6361198 := by
    simpa [prefixWord, tailWord_6361198, baseEnd_6361198] using wordTrace_append hprefix tailTrace_6361198
  have hstable : (prefixWord ++ tailWord_6361198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6361198).length < 2 ^ (prefixWord ++ tailWord_6361198).sum := by decide
  have hdescent : baseEnd_6361198 < baseStart_6361198 := by decide
  rcases family_descends (prefixWord ++ tailWord_6361198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6361248 : List Nat := [2, 1, 1, 4, 2, 2, 1, 1, 4, 3, 2]
def baseStart_6361248 : Nat := 118140960795 + 6361248 * 2 ^ 59
def prefixEnd_6361248 : Nat := 4983230072969 + 3 ^ 40 * 6361248 * 2
def baseEnd_6361248 : Nat := 3266377786452032821645159

theorem tailTrace_6361248 : CollatzResearch.WordTrace tailWord_6361248 prefixEnd_6361248 3266377786452032821645159 := by
  unfold tailWord_6361248
  simp only [CollatzResearch.WordTrace]
  refine ⟨116006887629146192754810199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154675850172194923673080265 116006887629146192754810199)
  ·
    refine ⟨174010331443719289132215299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116006887629146192754810199 174010331443719289132215299)
    ·
      refine ⟨261015497165578933698322949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174010331443719289132215299 261015497165578933698322949)
      ·
        refine ⟨48940405718546050068435553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 261015497165578933698322949 48940405718546050068435553)
        ·
          refine ⟨36705304288909537551326665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48940405718546050068435553 36705304288909537551326665)
          ·
            refine ⟨27528978216682153163494999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36705304288909537551326665 27528978216682153163494999)
            ·
              refine ⟨41293467325023229745242499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27528978216682153163494999 41293467325023229745242499)
              ·
                refine ⟨61940200987534844617863749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41293467325023229745242499 61940200987534844617863749)
                ·
                  refine ⟨11613787685162783365849453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61940200987534844617863749 11613787685162783365849453)
                  ·
                    refine ⟨4355170381936043762193545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11613787685162783365849453 4355170381936043762193545)
                    ·
                      refine ⟨3266377786452032821645159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4355170381936043762193545 3266377786452032821645159)
                      ·
                        rfl

theorem cell23_6361248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 1, 4, 3, 2].length) (baseStart_6361248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6361248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6361248 prefixEnd_6361248 := by exact prefixLift 6361248
  have htrace : WordTrace (prefixWord ++ tailWord_6361248) baseStart_6361248 baseEnd_6361248 := by
    simpa [prefixWord, tailWord_6361248, baseEnd_6361248] using wordTrace_append hprefix tailTrace_6361248
  have hstable : (prefixWord ++ tailWord_6361248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6361248).length < 2 ^ (prefixWord ++ tailWord_6361248).sum := by decide
  have hdescent : baseEnd_6361248 < baseStart_6361248 := by decide
  rcases family_descends (prefixWord ++ tailWord_6361248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6361291 : List Nat := [1, 1, 1, 1, 3, 2, 5, 2, 1, 2, 4]
def baseStart_6361291 : Nat := 118140960795 + 6361291 * 2 ^ 59
def prefixEnd_6361291 : Nat := 4983230072969 + 3 ^ 40 * 6361291 * 2
def baseEnd_6361291 : Nat := 3266399866120176153407461

theorem tailTrace_6361291 : CollatzResearch.WordTrace tailWord_6361291 prefixEnd_6361291 3266399866120176153407461 := by
  unfold tailWord_6361291
  simp only [CollatzResearch.WordTrace]
  refine ⟨232015343597136603853435727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154676895731424402568957151 232015343597136603853435727)
  ·
    refine ⟨348023015395704905780153591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232015343597136603853435727 348023015395704905780153591)
    ·
      refine ⟨522034523093557358670230387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348023015395704905780153591 522034523093557358670230387)
      ·
        refine ⟨783051784640336038005345581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 522034523093557358670230387 783051784640336038005345581)
        ·
          refine ⟨293644419240126014252004593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 783051784640336038005345581 293644419240126014252004593)
          ·
            refine ⟨220233314430094510689003445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 293644419240126014252004593 220233314430094510689003445)
            ·
              refine ⟨20646873227821360377094073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 220233314430094510689003445 20646873227821360377094073)
              ·
                refine ⟨15485154920866020282820555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20646873227821360377094073 15485154920866020282820555)
                ·
                  refine ⟨23227732381299030424230833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15485154920866020282820555 23227732381299030424230833)
                  ·
                    refine ⟨17420799285974272818173125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23227732381299030424230833 17420799285974272818173125)
                    ·
                      refine ⟨3266399866120176153407461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17420799285974272818173125 3266399866120176153407461)
                      ·
                        rfl

theorem cell23_6361291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 2, 1, 2, 4].length) (baseStart_6361291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6361291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6361291 prefixEnd_6361291 := by exact prefixLift 6361291
  have htrace : WordTrace (prefixWord ++ tailWord_6361291) baseStart_6361291 baseEnd_6361291 := by
    simpa [prefixWord, tailWord_6361291, baseEnd_6361291] using wordTrace_append hprefix tailTrace_6361291
  have hstable : (prefixWord ++ tailWord_6361291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6361291).length < 2 ^ (prefixWord ++ tailWord_6361291).sum := by decide
  have hdescent : baseEnd_6361291 < baseStart_6361291 := by decide
  rcases family_descends (prefixWord ++ tailWord_6361291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6361292 : List Nat := [2, 2, 1, 6, 1, 1, 3, 1, 1, 5]
def baseStart_6361292 : Nat := 118140960795 + 6361292 * 2 ^ 59
def prefixEnd_6361292 : Nat := 4983230072969 + 3 ^ 40 * 6361292 * 2
def baseEnd_6361292 : Nat := 1088800126533610216498319

theorem tailTrace_6361292 : CollatzResearch.WordTrace tailWord_6361292 prefixEnd_6361292 1088800126533610216498319 := by
  unfold tailWord_6361292
  simp only [CollatzResearch.WordTrace]
  refine ⟨116007690035066490512111065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154676920046755320682814753 116007690035066490512111065)
  ·
    refine ⟨87005767526299867884083299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116007690035066490512111065 87005767526299867884083299)
    ·
      refine ⟨130508651289449801826124949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87005767526299867884083299 130508651289449801826124949)
      ·
        refine ⟨6117593029192959460599607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 130508651289449801826124949 6117593029192959460599607)
        ·
          refine ⟨9176389543789439190899411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6117593029192959460599607 9176389543789439190899411)
          ·
            refine ⟨13764584315684158786349117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9176389543789439190899411 13764584315684158786349117)
            ·
              refine ⟨5161719118381559544880919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13764584315684158786349117 5161719118381559544880919)
              ·
                refine ⟨7742578677572339317321379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5161719118381559544880919 7742578677572339317321379)
                ·
                  refine ⟨11613868016358508975982069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7742578677572339317321379 11613868016358508975982069)
                  ·
                    refine ⟨1088800126533610216498319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11613868016358508975982069 1088800126533610216498319)
                    ·
                      rfl

theorem cell23_6361292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 3, 1, 1, 5].length) (baseStart_6361292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6361292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6361292 prefixEnd_6361292 := by exact prefixLift 6361292
  have htrace : WordTrace (prefixWord ++ tailWord_6361292) baseStart_6361292 baseEnd_6361292 := by
    simpa [prefixWord, tailWord_6361292, baseEnd_6361292] using wordTrace_append hprefix tailTrace_6361292
  have hstable : (prefixWord ++ tailWord_6361292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6361292).length < 2 ^ (prefixWord ++ tailWord_6361292).sum := by decide
  have hdescent : baseEnd_6361292 < baseStart_6361292 := by decide
  rcases family_descends (prefixWord ++ tailWord_6361292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6361298 : List Nat := [3, 2, 2, 2, 1, 2, 3, 1, 1, 1, 5]
def baseStart_6361298 : Nat := 118140960795 + 6361298 * 2 ^ 59
def prefixEnd_6361298 : Nat := 4983230072969 + 3 ^ 40 * 6361298 * 2
def baseEnd_6361298 : Nat := 3266403460484757626019929

theorem tailTrace_6361298 : CollatzResearch.WordTrace tailWord_6361298 prefixEnd_6361298 3266403460484757626019929 := by
  unfold tailWord_6361298
  simp only [CollatzResearch.WordTrace]
  refine ⟨58003899727027811012235137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154677065938740829365960365 58003899727027811012235137)
  ·
    refine ⟨43502924795270858259176353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58003899727027811012235137 43502924795270858259176353)
    ·
      refine ⟨32627193596453143694382265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43502924795270858259176353 32627193596453143694382265)
      ·
        refine ⟨24470395197339857770786699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32627193596453143694382265 24470395197339857770786699)
        ·
          refine ⟨36705592796009786656180049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24470395197339857770786699 36705592796009786656180049)
          ·
            refine ⟨27529194597007339992135037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36705592796009786656180049 27529194597007339992135037)
            ·
              refine ⟨10323447973877752497050639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27529194597007339992135037 10323447973877752497050639)
              ·
                refine ⟨15485171960816628745575959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10323447973877752497050639 15485171960816628745575959)
                ·
                  refine ⟨23227757941224943118363939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15485171960816628745575959 23227757941224943118363939)
                  ·
                    refine ⟨34841636911837414677545909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23227757941224943118363939 34841636911837414677545909)
                    ·
                      refine ⟨3266403460484757626019929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34841636911837414677545909 3266403460484757626019929)
                      ·
                        rfl

theorem cell23_6361298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 1, 1, 1, 5].length) (baseStart_6361298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6361298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6361298 prefixEnd_6361298 := by exact prefixLift 6361298
  have htrace : WordTrace (prefixWord ++ tailWord_6361298) baseStart_6361298 baseEnd_6361298 := by
    simpa [prefixWord, tailWord_6361298, baseEnd_6361298] using wordTrace_append hprefix tailTrace_6361298
  have hstable : (prefixWord ++ tailWord_6361298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6361298).length < 2 ^ (prefixWord ++ tailWord_6361298).sum := by decide
  have hdescent : baseEnd_6361298 < baseStart_6361298 := by decide
  rcases family_descends (prefixWord ++ tailWord_6361298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6361301 : List Nat := [1, 3, 2, 4, 2, 11]
def baseStart_6361301 : Nat := 118140960795 + 6361301 * 2 ^ 59
def prefixEnd_6361301 : Nat := 4983230072969 + 3 ^ 40 * 6361301 * 2
def baseEnd_6361301 : Nat := 13441995888587329688405

theorem tailTrace_6361301 : CollatzResearch.WordTrace tailWord_6361301 prefixEnd_6361301 13441995888587329688405 := by
  unfold tailWord_6361301
  simp only [CollatzResearch.WordTrace]
  refine ⟨232015708327100375561299757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154677138884733583707533171 232015708327100375561299757)
  ·
    refine ⟨87005890622662640835487409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 232015708327100375561299757 87005890622662640835487409)
    ·
      refine ⟨65254417966996980626615557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87005890622662640835487409 65254417966996980626615557)
      ·
        refine ⟨12235203368811933867490417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65254417966996980626615557 12235203368811933867490417)
        ·
          refine ⟨9176402526608950400617813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12235203368811933867490417 9176402526608950400617813)
          ·
            refine ⟨13441995888587329688405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 9176402526608950400617813 13441995888587329688405)
            ·
              rfl

theorem cell23_6361301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 11].length) (baseStart_6361301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6361301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6361301 prefixEnd_6361301 := by exact prefixLift 6361301
  have htrace : WordTrace (prefixWord ++ tailWord_6361301) baseStart_6361301 baseEnd_6361301 := by
    simpa [prefixWord, tailWord_6361301, baseEnd_6361301] using wordTrace_append hprefix tailTrace_6361301
  have hstable : (prefixWord ++ tailWord_6361301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6361301).length < 2 ^ (prefixWord ++ tailWord_6361301).sum := by decide
  have hdescent : baseEnd_6361301 < baseStart_6361301 := by decide
  rcases family_descends (prefixWord ++ tailWord_6361301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6361311 : List Nat := [1, 1, 2, 3, 2, 1, 1, 1, 5, 3, 3]
def baseStart_6361311 : Nat := 118140960795 + 6361311 * 2 ^ 59
def prefixEnd_6361311 : Nat := 4983230072969 + 3 ^ 40 * 6361311 * 2
def baseEnd_6361311 : Nat := 3266410135733266075157369

theorem tailTrace_6361311 : CollatzResearch.WordTrace tailWord_6361311 prefixEnd_6361311 3266410135733266075157369 := by
  unfold tailWord_6361311
  simp only [CollatzResearch.WordTrace]
  refine ⟨232016073057064147269163787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154677382038042764846109191 232016073057064147269163787)
  ·
    refine ⟨348024109585596220903745681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232016073057064147269163787 348024109585596220903745681)
    ·
      refine ⟨261018082189197165677809261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 348024109585596220903745681 261018082189197165677809261)
      ·
        refine ⟨97881780820948937129178473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 261018082189197165677809261 97881780820948937129178473)
        ·
          refine ⟨73411335615711702846883855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97881780820948937129178473 73411335615711702846883855)
          ·
            refine ⟨110117003423567554270325783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73411335615711702846883855 110117003423567554270325783)
            ·
              refine ⟨165175505135351331405488675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110117003423567554270325783 165175505135351331405488675)
              ·
                refine ⟨247763257703026997108233013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 165175505135351331405488675 247763257703026997108233013)
                ·
                  refine ⟨23227805409658780978896845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 247763257703026997108233013 23227805409658780978896845)
                  ·
                    refine ⟨8710427028622042867086317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23227805409658780978896845 8710427028622042867086317)
                    ·
                      refine ⟨3266410135733266075157369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8710427028622042867086317 3266410135733266075157369)
                      ·
                        rfl

theorem cell23_6361311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 5, 3, 3].length) (baseStart_6361311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6361311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6361311 prefixEnd_6361311 := by exact prefixLift 6361311
  have htrace : WordTrace (prefixWord ++ tailWord_6361311) baseStart_6361311 baseEnd_6361311 := by
    simpa [prefixWord, tailWord_6361311, baseEnd_6361311] using wordTrace_append hprefix tailTrace_6361311
  have hstable : (prefixWord ++ tailWord_6361311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6361311).length < 2 ^ (prefixWord ++ tailWord_6361311).sum := by decide
  have hdescent : baseEnd_6361311 < baseStart_6361311 := by decide
  rcases family_descends (prefixWord ++ tailWord_6361311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6361312 : List Nat := [2, 1, 1, 3, 1, 3, 3, 4, 1, 2, 2]
def baseStart_6361312 : Nat := 118140960795 + 6361312 * 2 ^ 59
def prefixEnd_6361312 : Nat := 4983230072969 + 3 ^ 40 * 6361312 * 2
def baseEnd_6361312 : Nat := 3266410649213920571244865

theorem tailTrace_6361312 : CollatzResearch.WordTrace tailWord_6361312 prefixEnd_6361312 3266410649213920571244865 := by
  unfold tailWord_6361312
  simp only [CollatzResearch.WordTrace]
  refine ⟨116008054765030262219975095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154677406353373682959966793 116008054765030262219975095)
  ·
    refine ⟨174012082147545393329962643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116008054765030262219975095 174012082147545393329962643)
    ·
      refine ⟨261018123221318089994943965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174012082147545393329962643 261018123221318089994943965)
      ·
        refine ⟨97881796207994283748103987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 261018123221318089994943965 97881796207994283748103987)
        ·
          refine ⟨146822694311991425622155981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97881796207994283748103987 146822694311991425622155981)
          ·
            refine ⟨55058510366996784608308493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 146822694311991425622155981 55058510366996784608308493)
            ·
              refine ⟨20646941387623794228115685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55058510366996784608308493 20646941387623794228115685)
              ·
                refine ⟨3871301510179461417771691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20646941387623794228115685 3871301510179461417771691)
                ·
                  refine ⟨5806952265269192126657537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3871301510179461417771691 5806952265269192126657537)
                  ·
                    refine ⟨4355214198951894094993153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5806952265269192126657537 4355214198951894094993153)
                    ·
                      refine ⟨3266410649213920571244865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4355214198951894094993153 3266410649213920571244865)
                      ·
                        rfl

theorem cell23_6361312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 4, 1, 2, 2].length) (baseStart_6361312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6361312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6361312 prefixEnd_6361312 := by exact prefixLift 6361312
  have htrace : WordTrace (prefixWord ++ tailWord_6361312) baseStart_6361312 baseEnd_6361312 := by
    simpa [prefixWord, tailWord_6361312, baseEnd_6361312] using wordTrace_append hprefix tailTrace_6361312
  have hstable : (prefixWord ++ tailWord_6361312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6361312).length < 2 ^ (prefixWord ++ tailWord_6361312).sum := by decide
  have hdescent : baseEnd_6361312 < baseStart_6361312 := by decide
  rcases family_descends (prefixWord ++ tailWord_6361312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6361325 : List Nat := [1, 5, 1, 2, 3, 1, 2, 1, 1, 2, 4]
def baseStart_6361325 : Nat := 118140960795 + 6361325 * 2 ^ 59
def prefixEnd_6361325 : Nat := 4983230072969 + 3 ^ 40 * 6361325 * 2
def baseEnd_6361325 : Nat := 3266417324462429020382305

theorem tailTrace_6361325 : CollatzResearch.WordTrace tailWord_6361325 prefixEnd_6361325 3266417324462429020382305 := by
  unfold tailWord_6361325
  simp only [CollatzResearch.WordTrace]
  refine ⟨232016583679013427660173429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154677722452675618440115619 232016583679013427660173429)
  ·
    refine ⟨21751554719907508843141259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 232016583679013427660173429 21751554719907508843141259)
    ·
      refine ⟨32627332079861263264711889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21751554719907508843141259 32627332079861263264711889)
      ·
        refine ⟨24470499059895947448533917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32627332079861263264711889 24470499059895947448533917)
        ·
          refine ⟨9176437147460980293200219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24470499059895947448533917 9176437147460980293200219)
          ·
            refine ⟨13764655721191470439800329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9176437147460980293200219 13764655721191470439800329)
            ·
              refine ⟨10323491790893602829850247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13764655721191470439800329 10323491790893602829850247)
              ·
                refine ⟨15485237686340404244775371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10323491790893602829850247 15485237686340404244775371)
                ·
                  refine ⟨23227856529510606367163057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15485237686340404244775371 23227856529510606367163057)
                  ·
                    refine ⟨17420892397132954775372293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23227856529510606367163057 17420892397132954775372293)
                    ·
                      refine ⟨3266417324462429020382305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17420892397132954775372293 3266417324462429020382305)
                      ·
                        rfl

theorem cell23_6361325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 1, 1, 2, 4].length) (baseStart_6361325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6361325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6361325 prefixEnd_6361325 := by exact prefixLift 6361325
  have htrace : WordTrace (prefixWord ++ tailWord_6361325) baseStart_6361325 baseEnd_6361325 := by
    simpa [prefixWord, tailWord_6361325, baseEnd_6361325] using wordTrace_append hprefix tailTrace_6361325
  have hstable : (prefixWord ++ tailWord_6361325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6361325).length < 2 ^ (prefixWord ++ tailWord_6361325).sum := by decide
  have hdescent : baseEnd_6361325 < baseStart_6361325 := by decide
  rcases family_descends (prefixWord ++ tailWord_6361325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6361346 : List Nat := [3, 4, 1, 1, 2, 2, 2, 3, 1, 2, 2]
def baseStart_6361346 : Nat := 118140960795 + 6361346 * 2 ^ 59
def prefixEnd_6361346 : Nat := 4983230072969 + 3 ^ 40 * 6361346 * 2
def baseEnd_6361346 : Nat := 3266428107556173438219709

theorem tailTrace_6361346 : CollatzResearch.WordTrace tailWord_6361346 prefixEnd_6361346 3266428107556173438219709 := by
  unfold tailWord_6361346
  simp only [CollatzResearch.WordTrace]
  refine ⟨58004337402984337061671973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154678233074624898831125261 58004337402984337061671973)
  ·
    refine ⟨10875813263059563199063495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58004337402984337061671973 10875813263059563199063495)
    ·
      refine ⟨16313719894589344798595243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10875813263059563199063495 16313719894589344798595243)
      ·
        refine ⟨24470579841884017197892865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16313719894589344798595243 24470579841884017197892865)
        ·
          refine ⟨18352934881413012898419649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24470579841884017197892865 18352934881413012898419649)
          ·
            refine ⟨13764701161059759673814737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18352934881413012898419649 13764701161059759673814737)
            ·
              refine ⟨10323525870794819755361053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13764701161059759673814737 10323525870794819755361053)
              ·
                refine ⟨3871322201548057408260395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10323525870794819755361053 3871322201548057408260395)
                ·
                  refine ⟨5806983302322086112390593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3871322201548057408260395 5806983302322086112390593)
                  ·
                    refine ⟨4355237476741564584292945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5806983302322086112390593 4355237476741564584292945)
                    ·
                      refine ⟨3266428107556173438219709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4355237476741564584292945 3266428107556173438219709)
                      ·
                        rfl

theorem cell23_6361346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 3, 1, 2, 2].length) (baseStart_6361346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6361346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6361346 prefixEnd_6361346 := by exact prefixLift 6361346
  have htrace : WordTrace (prefixWord ++ tailWord_6361346) baseStart_6361346 baseEnd_6361346 := by
    simpa [prefixWord, tailWord_6361346, baseEnd_6361346] using wordTrace_append hprefix tailTrace_6361346
  have hstable : (prefixWord ++ tailWord_6361346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6361346).length < 2 ^ (prefixWord ++ tailWord_6361346).sum := by decide
  have hdescent : baseEnd_6361346 < baseStart_6361346 := by decide
  rcases family_descends (prefixWord ++ tailWord_6361346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6361355 : List Nat := [1, 1, 1, 1, 5, 2, 3, 3, 1, 3, 2]
def baseStart_6361355 : Nat := 118140960795 + 6361355 * 2 ^ 59
def prefixEnd_6361355 : Nat := 4983230072969 + 3 ^ 40 * 6361355 * 2
def baseEnd_6361355 : Nat := 3266432728882063903007167

theorem tailTrace_6361355 : CollatzResearch.WordTrace tailWord_6361355 prefixEnd_6361355 3266432728882063903007167 := by
  unfold tailWord_6361355
  simp only [CollatzResearch.WordTrace]
  refine ⟨232017677868904742783765519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154678451912603161855843679 232017677868904742783765519)
  ·
    refine ⟨348026516803357114175648279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232017677868904742783765519 348026516803357114175648279)
    ·
      refine ⟨522039775205035671263472419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348026516803357114175648279 522039775205035671263472419)
      ·
        refine ⟨783059662807553506895208629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 522039775205035671263472419 783059662807553506895208629)
        ·
          refine ⟨73411843388208141271425809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 783059662807553506895208629 73411843388208141271425809)
          ·
            refine ⟨55058882541156105953569357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73411843388208141271425809 55058882541156105953569357)
            ·
              refine ⟨20647080952933539732588509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55058882541156105953569357 20647080952933539732588509)
              ·
                refine ⟨7742655357350077399720691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20647080952933539732588509 7742655357350077399720691)
                ·
                  refine ⟨11613983036025116099581037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7742655357350077399720691 11613983036025116099581037)
                  ·
                    refine ⟨4355243638509418537342889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11613983036025116099581037 4355243638509418537342889)
                    ·
                      refine ⟨3266432728882063903007167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4355243638509418537342889 3266432728882063903007167)
                      ·
                        rfl

theorem cell23_6361355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 3, 1, 3, 2].length) (baseStart_6361355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6361355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6361355 prefixEnd_6361355 := by exact prefixLift 6361355
  have htrace : WordTrace (prefixWord ++ tailWord_6361355) baseStart_6361355 baseEnd_6361355 := by
    simpa [prefixWord, tailWord_6361355, baseEnd_6361355] using wordTrace_append hprefix tailTrace_6361355
  have hstable : (prefixWord ++ tailWord_6361355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6361355).length < 2 ^ (prefixWord ++ tailWord_6361355).sum := by decide
  have hdescent : baseEnd_6361355 < baseStart_6361355 := by decide
  rcases family_descends (prefixWord ++ tailWord_6361355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6361361 : List Nat := [1, 2, 2, 1, 1, 5, 1, 2, 2, 6]
def baseStart_6361361 : Nat := 118140960795 + 6361361 * 2 ^ 59
def prefixEnd_6361361 : Nat := 4983230072969 + 3 ^ 40 * 6361361 * 2
def baseEnd_6361361 : Nat := 1088811936588663626510713

theorem tailTrace_6361361 : CollatzResearch.WordTrace tailWord_6361361 prefixEnd_6361361 1088811936588663626510713 := by
  unfold tailWord_6361361
  simp only [CollatzResearch.WordTrace]
  refine ⟨232017896706883005808483937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154678597804588670538989291 232017896706883005808483937)
  ·
    refine ⟨174013422530162254356362953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232017896706883005808483937 174013422530162254356362953)
    ·
      refine ⟨130510066897621690767272215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174013422530162254356362953 130510066897621690767272215)
      ·
        refine ⟨195765100346432536150908323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130510066897621690767272215 195765100346432536150908323)
        ·
          refine ⟨293647650519648804226362485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195765100346432536150908323 293647650519648804226362485)
          ·
            refine ⟨27529467236217075396221483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 293647650519648804226362485 27529467236217075396221483)
            ·
              refine ⟨41294200854325613094332225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27529467236217075396221483 41294200854325613094332225)
              ·
                refine ⟨30970650640744209820749169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41294200854325613094332225 30970650640744209820749169)
                ·
                  refine ⟨23227987980558157365561877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30970650640744209820749169 23227987980558157365561877)
                  ·
                    refine ⟨1088811936588663626510713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23227987980558157365561877 1088811936588663626510713)
                    ·
                      rfl

theorem cell23_6361361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 6].length) (baseStart_6361361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6361361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6361361 prefixEnd_6361361 := by exact prefixLift 6361361
  have htrace : WordTrace (prefixWord ++ tailWord_6361361) baseStart_6361361 baseEnd_6361361 := by
    simpa [prefixWord, tailWord_6361361, baseEnd_6361361] using wordTrace_append hprefix tailTrace_6361361
  have hstable : (prefixWord ++ tailWord_6361361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6361361).length < 2 ^ (prefixWord ++ tailWord_6361361).sum := by decide
  have hdescent : baseEnd_6361361 < baseStart_6361361 := by decide
  rcases family_descends (prefixWord ++ tailWord_6361361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6361371 : List Nat := [1, 1, 1, 1, 1, 1, 6, 1, 1, 6, 3]
def baseStart_6361371 : Nat := 118140960795 + 6361371 * 2 ^ 59
def prefixEnd_6361371 : Nat := 4983230072969 + 3 ^ 40 * 6361371 * 2
def baseEnd_6361371 : Nat := 3266440944572535840407093

theorem tailTrace_6361371 : CollatzResearch.WordTrace tailWord_6361371 prefixEnd_6361371 3266440944572535840407093 := by
  unfold tailWord_6361371
  simp only [CollatzResearch.WordTrace]
  refine ⟨232018261436846777516347967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154678840957897851677565311 232018261436846777516347967)
  ·
    refine ⟨348027392155270166274521951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232018261436846777516347967 348027392155270166274521951)
    ·
      refine ⟨522041088232905249411782927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348027392155270166274521951 522041088232905249411782927)
      ·
        refine ⟨783061632349357874117674391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 522041088232905249411782927 783061632349357874117674391)
        ·
          refine ⟨1174592448524036811176511587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 783061632349357874117674391 1174592448524036811176511587)
          ·
            refine ⟨1761888672786055216764767381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1174592448524036811176511587 1761888672786055216764767381)
            ·
              refine ⟨82588531536846338285848471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1761888672786055216764767381 82588531536846338285848471)
              ·
                refine ⟨123882797305269507428772707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82588531536846338285848471 123882797305269507428772707)
                ·
                  refine ⟨185824195957904261143159061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 123882797305269507428772707 185824195957904261143159061)
                  ·
                    refine ⟨8710509185526762241085581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 185824195957904261143159061 8710509185526762241085581)
                    ·
                      refine ⟨3266440944572535840407093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8710509185526762241085581 3266440944572535840407093)
                      ·
                        rfl

theorem cell23_6361371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 6, 3].length) (baseStart_6361371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6361371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6361371 prefixEnd_6361371 := by exact prefixLift 6361371
  have htrace : WordTrace (prefixWord ++ tailWord_6361371) baseStart_6361371 baseEnd_6361371 := by
    simpa [prefixWord, tailWord_6361371, baseEnd_6361371] using wordTrace_append hprefix tailTrace_6361371
  have hstable : (prefixWord ++ tailWord_6361371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6361371).length < 2 ^ (prefixWord ++ tailWord_6361371).sum := by decide
  have hdescent : baseEnd_6361371 < baseStart_6361371 := by decide
  rcases family_descends (prefixWord ++ tailWord_6361371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6361378 : List Nat := [3, 3, 1, 1, 3, 1, 2, 1, 2, 6]
def baseStart_6361378 : Nat := 118140960795 + 6361378 * 2 ^ 59
def prefixEnd_6361378 : Nat := 4983230072969 + 3 ^ 40 * 6361378 * 2
def baseEnd_6361378 : Nat := 1088814846312372437673187

theorem tailTrace_6361378 : CollatzResearch.WordTrace tailWord_6361378 prefixEnd_6361378 1088814846312372437673187 := by
  unfold tailWord_6361378
  simp only [CollatzResearch.WordTrace]
  refine ⟨58004629186955354427963197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154679011165214278474568525 58004629186955354427963197)
  ·
    refine ⟨21751735945108257910486199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58004629186955354427963197 21751735945108257910486199)
    ·
      refine ⟨32627603917662386865729299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21751735945108257910486199 32627603917662386865729299)
      ·
        refine ⟨48941405876493580298593949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32627603917662386865729299 48941405876493580298593949)
        ·
          refine ⟨18353027203685092611972731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48941405876493580298593949 18353027203685092611972731)
          ·
            refine ⟨27529540805527638917959097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18353027203685092611972731 27529540805527638917959097)
            ·
              refine ⟨20647155604145729188469323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27529540805527638917959097 20647155604145729188469323)
              ·
                refine ⟨30970733406218593782703985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20647155604145729188469323 30970733406218593782703985)
                ·
                  refine ⟨23228050054663945337027989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30970733406218593782703985 23228050054663945337027989)
                  ·
                    refine ⟨1088814846312372437673187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23228050054663945337027989 1088814846312372437673187)
                    ·
                      rfl

theorem cell23_6361378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 1, 2, 6].length) (baseStart_6361378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6361378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6361378 prefixEnd_6361378 := by exact prefixLift 6361378
  have htrace : WordTrace (prefixWord ++ tailWord_6361378) baseStart_6361378 baseEnd_6361378 := by
    simpa [prefixWord, tailWord_6361378, baseEnd_6361378] using wordTrace_append hprefix tailTrace_6361378
  have hstable : (prefixWord ++ tailWord_6361378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6361378).length < 2 ^ (prefixWord ++ tailWord_6361378).sum := by decide
  have hdescent : baseEnd_6361378 < baseStart_6361378 := by decide
  rcases family_descends (prefixWord ++ tailWord_6361378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6361391 : List Nat := [1, 1, 2, 1, 2, 1, 6, 2, 7]
def baseStart_6361391 : Nat := 118140960795 + 6361391 * 2 ^ 59
def prefixEnd_6361391 : Nat := 4983230072969 + 3 ^ 40 * 6361391 * 2
def baseEnd_6361391 : Nat := 362939023798402862461889

theorem tailTrace_6361391 : CollatzResearch.WordTrace tailWord_6361391 prefixEnd_6361391 362939023798402862461889 := by
  unfold tailWord_6361391
  simp only [CollatzResearch.WordTrace]
  refine ⟨232018990896774320932076027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154679327264516213954717351 232018990896774320932076027)
  ·
    refine ⟨348028486345161481398114041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232018990896774320932076027 348028486345161481398114041)
    ·
      refine ⟨261021364758871111048585531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 348028486345161481398114041 261021364758871111048585531)
      ·
        refine ⟨391532047138306666572878297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261021364758871111048585531 391532047138306666572878297)
        ·
          refine ⟨293649035353729999929658723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 391532047138306666572878297 293649035353729999929658723)
          ·
            refine ⟨440473553030594999894488085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 293649035353729999929658723 440473553030594999894488085)
            ·
              refine ⟨20647197798309140620054129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 440473553030594999894488085 20647197798309140620054129)
              ·
                refine ⟨15485398348731855465040597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20647197798309140620054129 15485398348731855465040597)
                ·
                  refine ⟨362939023798402862461889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15485398348731855465040597 362939023798402862461889)
                  ·
                    rfl

theorem cell23_6361391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 2, 7].length) (baseStart_6361391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6361391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6361391 prefixEnd_6361391 := by exact prefixLift 6361391
  have htrace : WordTrace (prefixWord ++ tailWord_6361391) baseStart_6361391 baseEnd_6361391 := by
    simpa [prefixWord, tailWord_6361391, baseEnd_6361391] using wordTrace_append hprefix tailTrace_6361391
  have hstable : (prefixWord ++ tailWord_6361391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6361391).length < 2 ^ (prefixWord ++ tailWord_6361391).sum := by decide
  have hdescent : baseEnd_6361391 < baseStart_6361391 := by decide
  rcases family_descends (prefixWord ++ tailWord_6361391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6361408 : List Nat := [2, 1, 1, 2, 2, 1, 2, 7, 5]
def baseStart_6361408 : Nat := 118140960795 + 6361408 * 2 ^ 59
def prefixEnd_6361408 : Nat := 4983230072969 + 3 ^ 40 * 6361408 * 2
def baseEnd_6361408 : Nat := 362939993706305799516047

theorem tailTrace_6361408 : CollatzResearch.WordTrace tailWord_6361408 prefixEnd_6361408 362939993706305799516047 := by
  unfold tailWord_6361408
  simp only [CollatzResearch.WordTrace]
  refine ⟨116009805468856366417722439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154679740625141821890296585 116009805468856366417722439)
  ·
    refine ⟨174014708203284549626583659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116009805468856366417722439 174014708203284549626583659)
    ·
      refine ⟨261022062304926824439875489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174014708203284549626583659 261022062304926824439875489)
      ·
        refine ⟨195766546728695118329906617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 261022062304926824439875489 195766546728695118329906617)
        ·
          refine ⟨146824910046521338747429963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 195766546728695118329906617 146824910046521338747429963)
          ·
            refine ⟨220237365069782008121144945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146824910046521338747429963 220237365069782008121144945)
            ·
              refine ⟨165178023802336506090858709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 220237365069782008121144945 165178023802336506090858709)
              ·
                refine ⟨3871359932867261861504501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 165178023802336506090858709 3871359932867261861504501)
                ·
                  refine ⟨362939993706305799516047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3871359932867261861504501 362939993706305799516047)
                  ·
                    rfl

theorem cell23_6361408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 7, 5].length) (baseStart_6361408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6361408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6361408 prefixEnd_6361408 := by exact prefixLift 6361408
  have htrace : WordTrace (prefixWord ++ tailWord_6361408) baseStart_6361408 baseEnd_6361408 := by
    simpa [prefixWord, tailWord_6361408, baseEnd_6361408] using wordTrace_append hprefix tailTrace_6361408
  have hstable : (prefixWord ++ tailWord_6361408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6361408).length < 2 ^ (prefixWord ++ tailWord_6361408).sum := by decide
  have hdescent : baseEnd_6361408 < baseStart_6361408 := by decide
  rcases family_descends (prefixWord ++ tailWord_6361408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6361436 : List Nat := [2, 2, 4, 3, 1, 1, 1, 3, 2, 2, 2]
def baseStart_6361436 : Nat := 118140960795 + 6361436 * 2 ^ 59
def prefixEnd_6361436 : Nat := 4983230072969 + 3 ^ 40 * 6361436 * 2
def baseEnd_6361436 : Nat := 3266474320815078086094295

theorem tailTrace_6361436 : CollatzResearch.WordTrace tailWord_6361436 prefixEnd_6361436 3266474320815078086094295 := by
  unfold tailWord_6361436
  simp only [CollatzResearch.WordTrace]
  refine ⟨116010316090805646808732081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154680421454407529078309441 116010316090805646808732081)
  ·
    refine ⟨87007737068104235106549061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116010316090805646808732081 87007737068104235106549061)
    ·
      refine ⟨16313950700269544082477949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87007737068104235106549061 16313950700269544082477949)
      ·
        refine ⟨6117731512601079030929231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16313950700269544082477949 6117731512601079030929231)
        ·
          refine ⟨9176597268901618546393847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6117731512601079030929231 9176597268901618546393847)
          ·
            refine ⟨13764895903352427819590771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9176597268901618546393847 13764895903352427819590771)
            ·
              refine ⟨20647343855028641729386157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13764895903352427819590771 20647343855028641729386157)
              ·
                refine ⟨7742753945635740648519809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20647343855028641729386157 7742753945635740648519809)
                ·
                  refine ⟨5807065459226805486389857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7742753945635740648519809 5807065459226805486389857)
                  ·
                    refine ⟨4355299094420104114792393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5807065459226805486389857 4355299094420104114792393)
                    ·
                      refine ⟨3266474320815078086094295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4355299094420104114792393 3266474320815078086094295)
                      ·
                        rfl

theorem cell23_6361436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_6361436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6361436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6361436 prefixEnd_6361436 := by exact prefixLift 6361436
  have htrace : WordTrace (prefixWord ++ tailWord_6361436) baseStart_6361436 baseEnd_6361436 := by
    simpa [prefixWord, tailWord_6361436, baseEnd_6361436] using wordTrace_append hprefix tailTrace_6361436
  have hstable : (prefixWord ++ tailWord_6361436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6361436).length < 2 ^ (prefixWord ++ tailWord_6361436).sum := by decide
  have hdescent : baseEnd_6361436 < baseStart_6361436 := by decide
  rcases family_descends (prefixWord ++ tailWord_6361436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6361468 : List Nat := [2, 2, 2, 1, 1, 1, 2, 1, 7, 4]
def baseStart_6361468 : Nat := 118140960795 + 6361468 * 2 ^ 59
def prefixEnd_6361468 : Nat := 4983230072969 + 3 ^ 40 * 6361468 * 2
def baseEnd_6361468 : Nat := 1088830250732007320298049

theorem tailTrace_6361468 : CollatzResearch.WordTrace tailWord_6361468 prefixEnd_6361468 1088830250732007320298049 := by
  unfold tailWord_6361468
  simp only [CollatzResearch.WordTrace]
  refine ⟨116010899658747681541314529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154681199544996908721752705 116010899658747681541314529)
  ·
    refine ⟨87008174744060761155985897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116010899658747681541314529 87008174744060761155985897)
    ·
      refine ⟨65256131058045570866989423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87008174744060761155985897 65256131058045570866989423)
      ·
        refine ⟨97884196587068356300484135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65256131058045570866989423 97884196587068356300484135)
        ·
          refine ⟨146826294880602534450726203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97884196587068356300484135 146826294880602534450726203)
          ·
            refine ⟨220239442320903801676089305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146826294880602534450726203 220239442320903801676089305)
            ·
              refine ⟨165179581740677851257066979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 220239442320903801676089305 165179581740677851257066979)
              ·
                refine ⟨247769372611016776885600469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 165179581740677851257066979 247769372611016776885600469)
                ·
                  refine ⟨5807094670570705708256261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 247769372611016776885600469 5807094670570705708256261)
                  ·
                    refine ⟨1088830250732007320298049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5807094670570705708256261 1088830250732007320298049)
                    ·
                      rfl

theorem cell23_6361468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 7, 4].length) (baseStart_6361468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6361468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6361468 prefixEnd_6361468 := by exact prefixLift 6361468
  have htrace : WordTrace (prefixWord ++ tailWord_6361468) baseStart_6361468 baseEnd_6361468 := by
    simpa [prefixWord, tailWord_6361468, baseEnd_6361468] using wordTrace_append hprefix tailTrace_6361468
  have hstable : (prefixWord ++ tailWord_6361468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6361468).length < 2 ^ (prefixWord ++ tailWord_6361468).sum := by decide
  have hdescent : baseEnd_6361468 < baseStart_6361468 := by decide
  rcases family_descends (prefixWord ++ tailWord_6361468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6361471 : List Nat := [1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 6]
def baseStart_6361471 : Nat := 118140960795 + 6361471 * 2 ^ 59
def prefixEnd_6361471 : Nat := 4983230072969 + 3 ^ 40 * 6361471 * 2
def baseEnd_6361471 : Nat := 3266492292637985449156633

theorem tailTrace_6361471 : CollatzResearch.WordTrace tailWord_6361471 prefixEnd_6361471 3266492292637985449156633 := by
  unfold tailWord_6361471
  simp only [CollatzResearch.WordTrace]
  refine ⟨232021908736484494594988267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154681272490989663063325511 232021908736484494594988267)
  ·
    refine ⟨348032863104726741892482401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232021908736484494594988267 348032863104726741892482401)
    ·
      refine ⟨261024647328545056419361801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 348032863104726741892482401 261024647328545056419361801)
      ·
        refine ⟨195768485496408792314521351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 261024647328545056419361801 195768485496408792314521351)
        ·
          refine ⟨293652728244613188471782027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195768485496408792314521351 293652728244613188471782027)
          ·
            refine ⟨440479092366919782707673041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 293652728244613188471782027 440479092366919782707673041)
            ·
              refine ⟨330359319275189837030754781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 440479092366919782707673041 330359319275189837030754781)
              ·
                refine ⟨123884744728196188886533043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 330359319275189837030754781 123884744728196188886533043)
                ·
                  refine ⟨185827117092294283329799565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 123884744728196188886533043 185827117092294283329799565)
                  ·
                    refine ⟨69685168909610356248674837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 185827117092294283329799565 69685168909610356248674837)
                    ·
                      refine ⟨3266492292637985449156633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69685168909610356248674837 3266492292637985449156633)
                      ·
                        rfl

theorem cell23_6361471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 6].length) (baseStart_6361471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6361471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6361471 prefixEnd_6361471 := by exact prefixLift 6361471
  have htrace : WordTrace (prefixWord ++ tailWord_6361471) baseStart_6361471 baseEnd_6361471 := by
    simpa [prefixWord, tailWord_6361471, baseEnd_6361471] using wordTrace_append hprefix tailTrace_6361471
  have hstable : (prefixWord ++ tailWord_6361471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6361471).length < 2 ^ (prefixWord ++ tailWord_6361471).sum := by decide
  have hdescent : baseEnd_6361471 < baseStart_6361471 := by decide
  rcases family_descends (prefixWord ++ tailWord_6361471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6361502 : List Nat := [4, 3, 1, 2, 1, 1, 1, 1, 5, 4]
def baseStart_6361502 : Nat := 118140960795 + 6361502 * 2 ^ 59
def prefixEnd_6361502 : Nat := 4983230072969 + 3 ^ 40 * 6361502 * 2
def baseEnd_6361502 : Nat := 1088836070179424942622997

theorem tailTrace_6361502 : CollatzResearch.WordTrace tailWord_6361502 prefixEnd_6361502 1088836070179424942622997 := by
  unfold tailWord_6361502
  simp only [CollatzResearch.WordTrace]
  refine ⟨29002879924921523361170845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154682026266248124592911173 29002879924921523361170845)
  ·
    refine ⟨10876079971845571260439067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29002879924921523361170845 10876079971845571260439067)
    ·
      refine ⟨16314119957768356890658601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10876079971845571260439067 16314119957768356890658601)
      ·
        refine ⟨12235589968326267667993951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16314119957768356890658601 12235589968326267667993951)
        ·
          refine ⟨18353384952489401501990927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12235589968326267667993951 18353384952489401501990927)
          ·
            refine ⟨27530077428734102252986391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18353384952489401501990927 27530077428734102252986391)
            ·
              refine ⟨41295116143101153379479587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27530077428734102252986391 41295116143101153379479587)
              ·
                refine ⟨61942674214651730069219381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41295116143101153379479587 61942674214651730069219381)
                ·
                  refine ⟨5807125707623599693989317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61942674214651730069219381 5807125707623599693989317)
                  ·
                    refine ⟨1088836070179424942622997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5807125707623599693989317 1088836070179424942622997)
                    ·
                      rfl

theorem cell23_6361502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 1, 5, 4].length) (baseStart_6361502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6361502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6361502 prefixEnd_6361502 := by exact prefixLift 6361502
  have htrace : WordTrace (prefixWord ++ tailWord_6361502) baseStart_6361502 baseEnd_6361502 := by
    simpa [prefixWord, tailWord_6361502, baseEnd_6361502] using wordTrace_append hprefix tailTrace_6361502
  have hstable : (prefixWord ++ tailWord_6361502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6361502).length < 2 ^ (prefixWord ++ tailWord_6361502).sum := by decide
  have hdescent : baseEnd_6361502 < baseStart_6361502 := by decide
  rcases family_descends (prefixWord ++ tailWord_6361502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6361512 : List Nat := [2, 1, 6, 1, 1, 2, 1, 1, 1, 4, 3]
def baseStart_6361512 : Nat := 118140960795 + 6361512 * 2 ^ 59
def prefixEnd_6361512 : Nat := 4983230072969 + 3 ^ 40 * 6361512 * 2
def baseEnd_6361512 : Nat := 3266513345344819788743945

theorem tailTrace_6361512 : CollatzResearch.WordTrace tailWord_6361512 prefixEnd_6361512 3266513345344819788743945 := by
  unfold tailWord_6361512
  simp only [CollatzResearch.WordTrace]
  refine ⟨116011702064667979298615395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154682269419557305731487193 116011702064667979298615395)
  ·
    refine ⟨174017553097001968947923093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116011702064667979298615395 174017553097001968947923093)
    ·
      refine ⟨8157072801421967294433895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 174017553097001968947923093 8157072801421967294433895)
      ·
        refine ⟨12235609202132950941650843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8157072801421967294433895 12235609202132950941650843)
        ·
          refine ⟨18353413803199426412476265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12235609202132950941650843 18353413803199426412476265)
          ·
            refine ⟨13765060352399569809357199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18353413803199426412476265 13765060352399569809357199)
            ·
              refine ⟨20647590528599354714035799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13765060352399569809357199 20647590528599354714035799)
              ·
                refine ⟨30971385792899032071053699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20647590528599354714035799 30971385792899032071053699)
                ·
                  refine ⟨46457078689348548106580549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30971385792899032071053699 46457078689348548106580549)
                  ·
                    refine ⟨8710702254252852769983853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46457078689348548106580549 8710702254252852769983853)
                    ·
                      refine ⟨3266513345344819788743945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8710702254252852769983853 3266513345344819788743945)
                      ·
                        rfl

theorem cell23_6361512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_6361512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6361512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6361512 prefixEnd_6361512 := by exact prefixLift 6361512
  have htrace : WordTrace (prefixWord ++ tailWord_6361512) baseStart_6361512 baseEnd_6361512 := by
    simpa [prefixWord, tailWord_6361512, baseEnd_6361512] using wordTrace_append hprefix tailTrace_6361512
  have hstable : (prefixWord ++ tailWord_6361512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6361512).length < 2 ^ (prefixWord ++ tailWord_6361512).sum := by decide
  have hdescent : baseEnd_6361512 < baseStart_6361512 := by decide
  rcases family_descends (prefixWord ++ tailWord_6361512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6361532 : List Nat := [2, 2, 2, 4, 1, 3, 1, 2, 6]
def baseStart_6361532 : Nat := 118140960795 + 6361532 * 2 ^ 59
def prefixEnd_6361532 : Nat := 4983230072969 + 3 ^ 40 * 6361532 * 2
def baseEnd_6361532 : Nat := 362947068328656634499317

theorem tailTrace_6361532 : CollatzResearch.WordTrace tailWord_6361532 prefixEnd_6361532 362947068328656634499317 := by
  unfold tailWord_6361532
  simp only [CollatzResearch.WordTrace]
  refine ⟨116012066794631751006479425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154682755726175668008639233 116012066794631751006479425)
  ·
    refine ⟨87009050095973813254859569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116012066794631751006479425 87009050095973813254859569)
    ·
      refine ⟨65256787571980359941144677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87009050095973813254859569 65256787571980359941144677)
      ·
        refine ⟨12235647669746317488964627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65256787571980359941144677 12235647669746317488964627)
        ·
          refine ⟨18353471504619476233446941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12235647669746317488964627 18353471504619476233446941)
          ·
            refine ⟨6882551814232303587542603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18353471504619476233446941 6882551814232303587542603)
            ·
              refine ⟨10323827721348455381313905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6882551814232303587542603 10323827721348455381313905)
              ·
                refine ⟨7742870791011341535985429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10323827721348455381313905 7742870791011341535985429)
                ·
                  refine ⟨362947068328656634499317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7742870791011341535985429 362947068328656634499317)
                  ·
                    rfl

theorem cell23_6361532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 2, 6].length) (baseStart_6361532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6361532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6361532 prefixEnd_6361532 := by exact prefixLift 6361532
  have htrace : WordTrace (prefixWord ++ tailWord_6361532) baseStart_6361532 baseEnd_6361532 := by
    simpa [prefixWord, tailWord_6361532, baseEnd_6361532] using wordTrace_append hprefix tailTrace_6361532
  have hstable : (prefixWord ++ tailWord_6361532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6361532).length < 2 ^ (prefixWord ++ tailWord_6361532).sum := by decide
  have hdescent : baseEnd_6361532 < baseStart_6361532 := by decide
  rcases family_descends (prefixWord ++ tailWord_6361532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6361568 : List Nat := [2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 5]
def baseStart_6361568 : Nat := 118140960795 + 6361568 * 2 ^ 59
def prefixEnd_6361568 : Nat := 4983230072969 + 3 ^ 40 * 6361568 * 2
def baseEnd_6361568 : Nat := 3266542100261471569643687

theorem tailTrace_6361568 : CollatzResearch.WordTrace tailWord_6361568 prefixEnd_6361568 3266542100261471569643687 := by
  unfold tailWord_6361568
  simp only [CollatzResearch.WordTrace]
  refine ⟨116012723308566540080634679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154683631078088720107512905 116012723308566540080634679)
  ·
    refine ⟨174019084962849810120952019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116012723308566540080634679 174019084962849810120952019)
    ·
      refine ⟨261028627444274715181428029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174019084962849810120952019 261028627444274715181428029)
      ·
        refine ⟨97885735291603018193035511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 261028627444274715181428029 97885735291603018193035511)
        ·
          refine ⟨146828602937404527289553267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97885735291603018193035511 146828602937404527289553267)
          ·
            refine ⟨220242904406106790934329901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146828602937404527289553267 220242904406106790934329901)
            ·
              refine ⟨82591089152290046600373713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 220242904406106790934329901 82591089152290046600373713)
              ·
                refine ⟨61943316864217534950280285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82591089152290046600373713 61943316864217534950280285)
                ·
                  refine ⟨23228743824081575606355107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61943316864217534950280285 23228743824081575606355107)
                  ·
                    refine ⟨34843115736122363409532661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23228743824081575606355107 34843115736122363409532661)
                    ·
                      refine ⟨3266542100261471569643687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34843115736122363409532661 3266542100261471569643687)
                      ·
                        rfl

theorem cell23_6361568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 5].length) (baseStart_6361568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6361568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6361568 prefixEnd_6361568 := by exact prefixLift 6361568
  have htrace : WordTrace (prefixWord ++ tailWord_6361568) baseStart_6361568 baseEnd_6361568 := by
    simpa [prefixWord, tailWord_6361568, baseEnd_6361568] using wordTrace_append hprefix tailTrace_6361568
  have hstable : (prefixWord ++ tailWord_6361568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6361568).length < 2 ^ (prefixWord ++ tailWord_6361568).sum := by decide
  have hdescent : baseEnd_6361568 < baseStart_6361568 := by decide
  rcases family_descends (prefixWord ++ tailWord_6361568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6361570 : List Nat := [3, 3, 3, 2, 2, 1, 1, 3, 1, 4]
def baseStart_6361570 : Nat := 118140960795 + 6361570 * 2 ^ 59
def prefixEnd_6361570 : Nat := 4983230072969 + 3 ^ 40 * 6361570 * 2
def baseEnd_6361570 : Nat := 1088847709074260187272893

theorem tailTrace_6361570 : CollatzResearch.WordTrace tailWord_6361570 prefixEnd_6361570 1088847709074260187272893 := by
  unfold tailWord_6361570
  simp only [CollatzResearch.WordTrace]
  refine ⟨58006379890781458625710541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154683679708750556335228109 58006379890781458625710541)
  ·
    refine ⟨21752392459043046984641453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58006379890781458625710541 21752392459043046984641453)
    ·
      refine ⟨8157147172141142619240545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21752392459043046984641453 8157147172141142619240545)
      ·
        refine ⟨6117860379105856964430409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8157147172141142619240545 6117860379105856964430409)
        ·
          refine ⟨4588395284329392723322807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6117860379105856964430409 4588395284329392723322807)
          ·
            refine ⟨6882592926494089084984211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4588395284329392723322807 6882592926494089084984211)
            ·
              refine ⟨10323889389741133627476317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6882592926494089084984211 10323889389741133627476317)
              ·
                refine ⟨3871458521152925110303619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10323889389741133627476317 3871458521152925110303619)
                ·
                  refine ⟨5807187781729387665455429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3871458521152925110303619 5807187781729387665455429)
                  ·
                    refine ⟨1088847709074260187272893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5807187781729387665455429 1088847709074260187272893)
                    ·
                      rfl

theorem cell23_6361570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_6361570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6361570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6361570 prefixEnd_6361570 := by exact prefixLift 6361570
  have htrace : WordTrace (prefixWord ++ tailWord_6361570) baseStart_6361570 baseEnd_6361570 := by
    simpa [prefixWord, tailWord_6361570, baseEnd_6361570] using wordTrace_append hprefix tailTrace_6361570
  have hstable : (prefixWord ++ tailWord_6361570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6361570).length < 2 ^ (prefixWord ++ tailWord_6361570).sum := by decide
  have hdescent : baseEnd_6361570 < baseStart_6361570 := by decide
  rcases family_descends (prefixWord ++ tailWord_6361570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6361575 : List Nat := [1, 1, 5, 2, 1, 1, 1, 1, 6, 4]
def baseStart_6361575 : Nat := 118140960795 + 6361575 * 2 ^ 59
def prefixEnd_6361575 : Nat := 4983230072969 + 3 ^ 40 * 6361575 * 2
def baseEnd_6361575 : Nat := 1088848564875351014085385

theorem tailTrace_6361575 : CollatzResearch.WordTrace tailWord_6361575 prefixEnd_6361575 1088848564875351014085385 := by
  unfold tailWord_6361575
  simp only [CollatzResearch.WordTrace]
  refine ⟨232025701928107720356774179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154683801285405146904516119 232025701928107720356774179)
  ·
    refine ⟨348038552892161580535161269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232025701928107720356774179 348038552892161580535161269)
    ·
      refine ⟨32628614333640148175171369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 348038552892161580535161269 32628614333640148175171369)
      ·
        refine ⟨24471460750230111131378527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32628614333640148175171369 24471460750230111131378527)
        ·
          refine ⟨36707191125345166697067791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24471460750230111131378527 36707191125345166697067791)
          ·
            refine ⟨55060786688017750045601687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36707191125345166697067791 55060786688017750045601687)
            ·
              refine ⟨82591180032026625068402531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55060786688017750045601687 82591180032026625068402531)
              ·
                refine ⟨123886770048039937602603797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82591180032026625068402531 123886770048039937602603797)
                ·
                  refine ⟨5807192346001872075122053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 123886770048039937602603797 5807192346001872075122053)
                  ·
                    refine ⟨1088848564875351014085385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5807192346001872075122053 1088848564875351014085385)
                    ·
                      rfl

theorem cell23_6361575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 6, 4].length) (baseStart_6361575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6361575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6361575 prefixEnd_6361575 := by exact prefixLift 6361575
  have htrace : WordTrace (prefixWord ++ tailWord_6361575) baseStart_6361575 baseEnd_6361575 := by
    simpa [prefixWord, tailWord_6361575, baseEnd_6361575] using wordTrace_append hprefix tailTrace_6361575
  have hstable : (prefixWord ++ tailWord_6361575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6361575).length < 2 ^ (prefixWord ++ tailWord_6361575).sum := by decide
  have hdescent : baseEnd_6361575 < baseStart_6361575 := by decide
  rcases family_descends (prefixWord ++ tailWord_6361575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6361576 : List Nat := [2, 1, 4, 1, 1, 5, 1, 3, 1, 1, 3]
def baseStart_6361576 : Nat := 118140960795 + 6361576 * 2 ^ 59
def prefixEnd_6361576 : Nat := 4983230072969 + 3 ^ 40 * 6361576 * 2
def baseEnd_6361576 : Nat := 3266546208106707538343651

theorem tailTrace_6361576 : CollatzResearch.WordTrace tailWord_6361576 prefixEnd_6361576 3266546208106707538343651 := by
  unfold tailWord_6361576
  simp only [CollatzResearch.WordTrace]
  refine ⟨116012869200552048763780291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154683825600736065018373721 116012869200552048763780291)
  ·
    refine ⟨174019303800828073145670437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116012869200552048763780291 174019303800828073145670437)
    ·
      refine ⟨32628619462655263714813207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 174019303800828073145670437 32628619462655263714813207)
      ·
        refine ⟨48942929193982895572219811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32628619462655263714813207 48942929193982895572219811)
        ·
          refine ⟨73414393790974343358329717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48942929193982895572219811 73414393790974343358329717)
          ·
            refine ⟨6882599417903844689843411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 73414393790974343358329717 6882599417903844689843411)
            ·
              refine ⟨10323899126855767034765117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6882599417903844689843411 10323899126855767034765117)
              ·
                refine ⟨3871462172570912638036919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10323899126855767034765117 3871462172570912638036919)
                ·
                  refine ⟨5807193258856368957055379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3871462172570912638036919 5807193258856368957055379)
                  ·
                    refine ⟨8710789888284553435583069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5807193258856368957055379 8710789888284553435583069)
                    ·
                      refine ⟨3266546208106707538343651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8710789888284553435583069 3266546208106707538343651)
                      ·
                        rfl

theorem cell23_6361576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 3, 1, 1, 3].length) (baseStart_6361576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6361576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6361576 prefixEnd_6361576 := by exact prefixLift 6361576
  have htrace : WordTrace (prefixWord ++ tailWord_6361576) baseStart_6361576 baseEnd_6361576 := by
    simpa [prefixWord, tailWord_6361576, baseEnd_6361576] using wordTrace_append hprefix tailTrace_6361576
  have hstable : (prefixWord ++ tailWord_6361576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6361576).length < 2 ^ (prefixWord ++ tailWord_6361576).sum := by decide
  have hdescent : baseEnd_6361576 < baseStart_6361576 := by decide
  rcases family_descends (prefixWord ++ tailWord_6361576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6361582 : List Nat := [4, 1, 2, 1, 2, 2, 2, 3, 1, 1, 4]
def baseStart_6361582 : Nat := 118140960795 + 6361582 * 2 ^ 59
def prefixEnd_6361582 : Nat := 4983230072969 + 3 ^ 40 * 6361582 * 2
def baseEnd_6361582 : Nat := 3266549288990634514868623

theorem tailTrace_6361582 : CollatzResearch.WordTrace tailWord_6361582 prefixEnd_6361582 3266549288990634514868623 := by
  unfold tailWord_6361582
  simp only [CollatzResearch.WordTrace]
  refine ⟨29003244654885295069034875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154683971492721573701519333 29003244654885295069034875)
  ·
    refine ⟨43504866982327942603552313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29003244654885295069034875 43504866982327942603552313)
    ·
      refine ⟨32628650236745956952664235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43504866982327942603552313 32628650236745956952664235)
      ·
        refine ⟨48942975355118935428996353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32628650236745956952664235 48942975355118935428996353)
        ·
          refine ⟨36707231516339201571747265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48942975355118935428996353 36707231516339201571747265)
          ·
            refine ⟨27530423637254401178810449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36707231516339201571747265 27530423637254401178810449)
            ·
              refine ⟨20647817727940800884107837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27530423637254401178810449 20647817727940800884107837)
              ·
                refine ⟨7742931647977800331540439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20647817727940800884107837 7742931647977800331540439)
                ·
                  refine ⟨11614397471966700497310659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7742931647977800331540439 11614397471966700497310659)
                  ·
                    refine ⟨17421596207950050745965989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11614397471966700497310659 17421596207950050745965989)
                    ·
                      refine ⟨3266549288990634514868623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17421596207950050745965989 3266549288990634514868623)
                      ·
                        rfl

theorem cell23_6361582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 3, 1, 1, 4].length) (baseStart_6361582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6361582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6361582 prefixEnd_6361582 := by exact prefixLift 6361582
  have htrace : WordTrace (prefixWord ++ tailWord_6361582) baseStart_6361582 baseEnd_6361582 := by
    simpa [prefixWord, tailWord_6361582, baseEnd_6361582] using wordTrace_append hprefix tailTrace_6361582
  have hstable : (prefixWord ++ tailWord_6361582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6361582).length < 2 ^ (prefixWord ++ tailWord_6361582).sum := by decide
  have hdescent : baseEnd_6361582 < baseStart_6361582 := by decide
  rcases family_descends (prefixWord ++ tailWord_6361582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6361585 : List Nat := [1, 2, 2, 2, 3, 1, 4, 1, 1, 1, 5]
def baseStart_6361585 : Nat := 118140960795 + 6361585 * 2 ^ 59
def prefixEnd_6361585 : Nat := 4983230072969 + 3 ^ 40 * 6361585 * 2
def baseEnd_6361585 : Nat := 3266550829432598003131109

theorem tailTrace_6361585 : CollatzResearch.WordTrace tailWord_6361585 prefixEnd_6361585 3266550829432598003131109 := by
  unfold tailWord_6361585
  simp only [CollatzResearch.WordTrace]
  refine ⟨232026066658071492064638209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154684044438714328043092139 232026066658071492064638209)
  ·
    refine ⟨174019549993553619048478657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232026066658071492064638209 174019549993553619048478657)
    ·
      refine ⟨130514662495165214286358993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174019549993553619048478657 130514662495165214286358993)
      ·
        refine ⟨97885996871373910714769245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130514662495165214286358993 97885996871373910714769245)
        ·
          refine ⟨36707248826765216518038467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97885996871373910714769245 36707248826765216518038467)
          ·
            refine ⟨55060873240147824777057701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36707248826765216518038467 55060873240147824777057701)
            ·
              refine ⟨10323913732527717145698319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55060873240147824777057701 10323913732527717145698319)
              ·
                refine ⟨15485870598791575718547479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10323913732527717145698319 15485870598791575718547479)
                ·
                  refine ⟨23228805898187363577821219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15485870598791575718547479 23228805898187363577821219)
                  ·
                    refine ⟨34843208847281045366731829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23228805898187363577821219 34843208847281045366731829)
                    ·
                      refine ⟨3266550829432598003131109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34843208847281045366731829 3266550829432598003131109)
                      ·
                        rfl

theorem cell23_6361585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 1, 1, 1, 5].length) (baseStart_6361585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6361585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6361585 prefixEnd_6361585 := by exact prefixLift 6361585
  have htrace : WordTrace (prefixWord ++ tailWord_6361585) baseStart_6361585 baseEnd_6361585 := by
    simpa [prefixWord, tailWord_6361585, baseEnd_6361585] using wordTrace_append hprefix tailTrace_6361585
  have hstable : (prefixWord ++ tailWord_6361585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6361585).length < 2 ^ (prefixWord ++ tailWord_6361585).sum := by decide
  have hdescent : baseEnd_6361585 < baseStart_6361585 := by decide
  rcases family_descends (prefixWord ++ tailWord_6361585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6361608 : List Nat := [2, 1, 3, 2, 1, 1, 1, 1, 1, 4, 6]
def baseStart_6361608 : Nat := 118140960795 + 6361608 * 2 ^ 59
def prefixEnd_6361608 : Nat := 4983230072969 + 3 ^ 40 * 6361608 * 2
def baseEnd_6361608 : Nat := 3266562639487651413143503

theorem tailTrace_6361608 : CollatzResearch.WordTrace tailWord_6361608 prefixEnd_6361608 3266562639487651413143503 := by
  unfold tailWord_6361608
  simp only [CollatzResearch.WordTrace]
  refine ⟨116013452768494083496362739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154684603691325444661816985 116013452768494083496362739)
  ·
    refine ⟨174020179152741125244544109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116013452768494083496362739 174020179152741125244544109)
    ·
      refine ⟨65257567182277921966704041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174020179152741125244544109 65257567182277921966704041)
      ·
        refine ⟨48943175386708441475028031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65257567182277921966704041 48943175386708441475028031)
        ·
          refine ⟨73414763080062662212542047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48943175386708441475028031 73414763080062662212542047)
          ·
            refine ⟨110122144620093993318813071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73414763080062662212542047 110122144620093993318813071)
            ·
              refine ⟨165183216930140989978219607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110122144620093993318813071 165183216930140989978219607)
              ·
                refine ⟨247774825395211484967329411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 165183216930140989978219607 247774825395211484967329411)
                ·
                  refine ⟨371662238092817227450994117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 247774825395211484967329411 371662238092817227450994117)
                  ·
                    refine ⟨69686669642403230147061397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 371662238092817227450994117 69686669642403230147061397)
                    ·
                      refine ⟨3266562639487651413143503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69686669642403230147061397 3266562639487651413143503)
                      ·
                        rfl

theorem cell23_6361608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_6361608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6361608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6361608 prefixEnd_6361608 := by exact prefixLift 6361608
  have htrace : WordTrace (prefixWord ++ tailWord_6361608) baseStart_6361608 baseEnd_6361608 := by
    simpa [prefixWord, tailWord_6361608, baseEnd_6361608] using wordTrace_append hprefix tailTrace_6361608
  have hstable : (prefixWord ++ tailWord_6361608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6361608).length < 2 ^ (prefixWord ++ tailWord_6361608).sum := by decide
  have hdescent : baseEnd_6361608 < baseStart_6361608 := by decide
  rcases family_descends (prefixWord ++ tailWord_6361608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6361625 : List Nat := [1, 2, 1, 2, 1, 1, 2, 2, 2, 7, 2]
def baseStart_6361625 : Nat := 118140960795 + 6361625 * 2 ^ 59
def prefixEnd_6361625 : Nat := 4983230072969 + 3 ^ 40 * 6361625 * 2
def baseEnd_6361625 : Nat := 3266571368658777846630925

theorem tailTrace_6361625 : CollatzResearch.WordTrace tailWord_6361625 prefixEnd_6361625 3266571368658777846630925 := by
  unfold tailWord_6361625
  simp only [CollatzResearch.WordTrace]
  refine ⟨232027525577926578896094329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154685017051951052597396219 232027525577926578896094329)
  ·
    refine ⟨174020644183444934172070747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232027525577926578896094329 174020644183444934172070747)
    ·
      refine ⟨261030966275167401258106121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174020644183444934172070747 261030966275167401258106121)
      ·
        refine ⟨195773224706375550943579591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 261030966275167401258106121 195773224706375550943579591)
        ·
          refine ⟨293659837059563326415369387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195773224706375550943579591 293659837059563326415369387)
          ·
            refine ⟨440489755589344989623054081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 293659837059563326415369387 440489755589344989623054081)
            ·
              refine ⟨330367316692008742217290561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 440489755589344989623054081 330367316692008742217290561)
              ·
                refine ⟨247775487519006556662967921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 330367316692008742217290561 247775487519006556662967921)
                ·
                  refine ⟨185831615639254917497225941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 247775487519006556662967921 185831615639254917497225941)
                  ·
                    refine ⟨4355428491545037128841233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 185831615639254917497225941 4355428491545037128841233)
                    ·
                      refine ⟨3266571368658777846630925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4355428491545037128841233 3266571368658777846630925)
                      ·
                        rfl

theorem cell23_6361625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 7, 2].length) (baseStart_6361625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6361625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6361625 prefixEnd_6361625 := by exact prefixLift 6361625
  have htrace : WordTrace (prefixWord ++ tailWord_6361625) baseStart_6361625 baseEnd_6361625 := by
    simpa [prefixWord, tailWord_6361625, baseEnd_6361625] using wordTrace_append hprefix tailTrace_6361625
  have hstable : (prefixWord ++ tailWord_6361625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6361625).length < 2 ^ (prefixWord ++ tailWord_6361625).sum := by decide
  have hdescent : baseEnd_6361625 < baseStart_6361625 := by decide
  rcases family_descends (prefixWord ++ tailWord_6361625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6361636 : List Nat := [2, 3, 1, 5, 2, 1, 1, 1, 1, 1, 5]
def baseStart_6361636 : Nat := 118140960795 + 6361636 * 2 ^ 59
def prefixEnd_6361636 : Nat := 4983230072969 + 3 ^ 40 * 6361636 * 2
def baseEnd_6361636 : Nat := 3266577016945977303593375

theorem tailTrace_6361636 : CollatzResearch.WordTrace tailWord_6361636 prefixEnd_6361636 3266577016945977303593375 := by
  unfold tailWord_6361636
  simp only [CollatzResearch.WordTrace]
  refine ⟨116013963390443363887372381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154685284520591151849829841 116013963390443363887372381)
  ·
    refine ⟨43505236271416261457764643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116013963390443363887372381 43505236271416261457764643)
    ·
      refine ⟨65257854407124392186646965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43505236271416261457764643 65257854407124392186646965)
      ·
        refine ⟨6117923850667911767498153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 65257854407124392186646965 6117923850667911767498153)
        ·
          refine ⟨4588442888000933825623615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6117923850667911767498153 4588442888000933825623615)
          ·
            refine ⟨6882664332001400738435423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4588442888000933825623615 6882664332001400738435423)
            ·
              refine ⟨10323996498002101107653135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6882664332001400738435423 10323996498002101107653135)
              ·
                refine ⟨15485994747003151661479703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10323996498002101107653135 15485994747003151661479703)
                ·
                  refine ⟨23228992120504727492219555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15485994747003151661479703 23228992120504727492219555)
                  ·
                    refine ⟨34843488180757091238329333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23228992120504727492219555 34843488180757091238329333)
                    ·
                      refine ⟨3266577016945977303593375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34843488180757091238329333 3266577016945977303593375)
                      ·
                        rfl

theorem cell23_6361636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_6361636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6361636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6361636 prefixEnd_6361636 := by exact prefixLift 6361636
  have htrace : WordTrace (prefixWord ++ tailWord_6361636) baseStart_6361636 baseEnd_6361636 := by
    simpa [prefixWord, tailWord_6361636, baseEnd_6361636] using wordTrace_append hprefix tailTrace_6361636
  have hstable : (prefixWord ++ tailWord_6361636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6361636).length < 2 ^ (prefixWord ++ tailWord_6361636).sum := by decide
  have hdescent : baseEnd_6361636 < baseStart_6361636 := by decide
  rcases family_descends (prefixWord ++ tailWord_6361636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6361665 : List Nat := [1, 2, 5, 1, 1, 2, 1, 1, 1, 8]
def baseStart_6361665 : Nat := 118140960795 + 6361665 * 2 ^ 59
def prefixEnd_6361665 : Nat := 4983230072969 + 3 ^ 40 * 6361665 * 2
def baseEnd_6361665 : Nat := 1088863969294985896710247

theorem tailTrace_6361665 : CollatzResearch.WordTrace tailWord_6361665 prefixEnd_6361665 1088863969294985896710247 := by
  unfold tailWord_6361665
  simp only [CollatzResearch.WordTrace]
  refine ⟨232028984497781665727550449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154685989665187777151700299 232028984497781665727550449)
  ·
    refine ⟨174021738373336249295662837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232028984497781665727550449 174021738373336249295662837)
    ·
      refine ⟨16314537972500273371468391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 174021738373336249295662837 16314537972500273371468391)
      ·
        refine ⟨24471806958750410057202587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16314537972500273371468391 24471806958750410057202587)
        ·
          refine ⟨36707710438125615085803881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24471806958750410057202587 36707710438125615085803881)
          ·
            refine ⟨27530782828594211314352911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36707710438125615085803881 27530782828594211314352911)
            ·
              refine ⟨41296174242891316971529367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27530782828594211314352911 41296174242891316971529367)
              ·
                refine ⟨61944261364336975457294051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41296174242891316971529367 61944261364336975457294051)
                ·
                  refine ⟨92916392046505463185941077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61944261364336975457294051 92916392046505463185941077)
                  ·
                    refine ⟨1088863969294985896710247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 92916392046505463185941077 1088863969294985896710247)
                    ·
                      rfl

theorem cell23_6361665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_6361665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6361665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6361665 prefixEnd_6361665 := by exact prefixLift 6361665
  have htrace : WordTrace (prefixWord ++ tailWord_6361665) baseStart_6361665 baseEnd_6361665 := by
    simpa [prefixWord, tailWord_6361665, baseEnd_6361665] using wordTrace_append hprefix tailTrace_6361665
  have hstable : (prefixWord ++ tailWord_6361665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6361665).length < 2 ^ (prefixWord ++ tailWord_6361665).sum := by decide
  have hdescent : baseEnd_6361665 < baseStart_6361665 := by decide
  rcases family_descends (prefixWord ++ tailWord_6361665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6361712 : List Nat := [2, 1, 1, 1, 7, 1, 2, 1, 7]
def baseStart_6361712 : Nat := 118140960795 + 6361712 * 2 ^ 59
def prefixEnd_6361712 : Nat := 4983230072969 + 3 ^ 40 * 6361712 * 2
def baseEnd_6361712 : Nat := 362957337941746556249225

theorem tailTrace_6361712 : CollatzResearch.WordTrace tailWord_6361712 prefixEnd_6361712 362957337941746556249225 := by
  unfold tailWord_6361712
  simp only [CollatzResearch.WordTrace]
  refine ⟨116015349364305696377255695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154687132485740928503007593 116015349364305696377255695)
  ·
    refine ⟨174023024046458544565883543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116015349364305696377255695 174023024046458544565883543)
    ·
      refine ⟨261034536069687816848825315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174023024046458544565883543 261034536069687816848825315)
      ·
        refine ⟨391551804104531725273237973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261034536069687816848825315 391551804104531725273237973)
        ·
          refine ⟨9176995408699962311091515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 391551804104531725273237973 9176995408699962311091515)
          ·
            refine ⟨13765493113049943466637273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9176995408699962311091515 13765493113049943466637273)
            ·
              refine ⟨10324119834787457599977955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13765493113049943466637273 10324119834787457599977955)
              ·
                refine ⟨15486179752181186399966933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10324119834787457599977955 15486179752181186399966933)
                ·
                  refine ⟨362957337941746556249225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15486179752181186399966933 362957337941746556249225)
                  ·
                    rfl

theorem cell23_6361712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 1, 7].length) (baseStart_6361712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6361712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6361712 prefixEnd_6361712 := by exact prefixLift 6361712
  have htrace : WordTrace (prefixWord ++ tailWord_6361712) baseStart_6361712 baseEnd_6361712 := by
    simpa [prefixWord, tailWord_6361712, baseEnd_6361712] using wordTrace_append hprefix tailTrace_6361712
  have hstable : (prefixWord ++ tailWord_6361712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6361712).length < 2 ^ (prefixWord ++ tailWord_6361712).sum := by decide
  have hdescent : baseEnd_6361712 < baseStart_6361712 := by decide
  rcases family_descends (prefixWord ++ tailWord_6361712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6361742 : List Nat := [4, 1, 1, 3, 1, 1, 2, 3, 2, 5]
def baseStart_6361742 : Nat := 118140960795 + 6361742 * 2 ^ 59
def prefixEnd_6361742 : Nat := 4983230072969 + 3 ^ 40 * 6361742 * 2
def baseEnd_6361742 : Nat := 1088877148631784629622629

theorem tailTrace_6361742 : CollatzResearch.WordTrace tailWord_6361742 prefixEnd_6361742 1088877148631784629622629 := by
  unfold tailWord_6361742
  simp only [CollatzResearch.WordTrace]
  refine ⟨29003974114812838484762935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154687861945668471918735653 29003974114812838484762935)
  ·
    refine ⟨43505961172219257727144403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29003974114812838484762935 43505961172219257727144403)
    ·
      refine ⟨65258941758328886590716605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43505961172219257727144403 65258941758328886590716605)
      ·
        refine ⟨24472103159373332471518727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65258941758328886590716605 24472103159373332471518727)
        ·
          refine ⟨36708154739059998707278091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24472103159373332471518727 36708154739059998707278091)
          ·
            refine ⟨55062232108589998060917137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36708154739059998707278091 55062232108589998060917137)
            ·
              refine ⟨41296674081442498545687853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55062232108589998060917137 41296674081442498545687853)
              ·
                refine ⟨15486252780540936954632945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41296674081442498545687853 15486252780540936954632945)
                ·
                  refine ⟨11614689585405702715974709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15486252780540936954632945 11614689585405702715974709)
                  ·
                    refine ⟨1088877148631784629622629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11614689585405702715974709 1088877148631784629622629)
                    ·
                      rfl

theorem cell23_6361742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 3, 2, 5].length) (baseStart_6361742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6361742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6361742 prefixEnd_6361742 := by exact prefixLift 6361742
  have htrace : WordTrace (prefixWord ++ tailWord_6361742) baseStart_6361742 baseEnd_6361742 := by
    simpa [prefixWord, tailWord_6361742, baseEnd_6361742] using wordTrace_append hprefix tailTrace_6361742
  have hstable : (prefixWord ++ tailWord_6361742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6361742).length < 2 ^ (prefixWord ++ tailWord_6361742).sum := by decide
  have hdescent : baseEnd_6361742 < baseStart_6361742 := by decide
  rcases family_descends (prefixWord ++ tailWord_6361742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6361746 : List Nat := [3, 2, 3, 1, 2, 3, 1, 3, 5]
def baseStart_6361746 : Nat := 118140960795 + 6361746 * 2 ^ 59
def prefixEnd_6361746 : Nat := 4983230072969 + 3 ^ 40 * 6361746 * 2
def baseEnd_6361746 : Nat := 362959277757552430357541

theorem tailTrace_6361746 : CollatzResearch.WordTrace tailWord_6361746 prefixEnd_6361746 362959277757552430357541 := by
  unfold tailWord_6361746
  simp only [CollatzResearch.WordTrace]
  refine ⟨58007984702622054140312273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154687959206992144374166061 58007984702622054140312273)
  ·
    refine ⟨43505988526966540605234205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58007984702622054140312273 43505988526966540605234205)
    ·
      refine ⟨16314745697612452726962827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43505988526966540605234205 16314745697612452726962827)
      ·
        refine ⟨24472118546418679090444241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16314745697612452726962827 24472118546418679090444241)
        ·
          refine ⟨18354088909814009317833181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24472118546418679090444241 18354088909814009317833181)
          ·
            refine ⟨6882783341180253494187443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18354088909814009317833181 6882783341180253494187443)
            ·
              refine ⟨10324175011770380241281165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6882783341180253494187443 10324175011770380241281165)
              ·
                refine ⟨3871565629413892590480437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10324175011770380241281165 3871565629413892590480437)
                ·
                  refine ⟨362959277757552430357541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3871565629413892590480437 362959277757552430357541)
                  ·
                    rfl

theorem cell23_6361746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 3, 5].length) (baseStart_6361746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6361746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6361746 prefixEnd_6361746 := by exact prefixLift 6361746
  have htrace : WordTrace (prefixWord ++ tailWord_6361746) baseStart_6361746 baseEnd_6361746 := by
    simpa [prefixWord, tailWord_6361746, baseEnd_6361746] using wordTrace_append hprefix tailTrace_6361746
  have hstable : (prefixWord ++ tailWord_6361746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6361746).length < 2 ^ (prefixWord ++ tailWord_6361746).sum := by decide
  have hdescent : baseEnd_6361746 < baseStart_6361746 := by decide
  rcases family_descends (prefixWord ++ tailWord_6361746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6361823 : List Nat := [1, 1, 2, 3, 2, 5, 2, 2, 1, 4]
def baseStart_6361823 : Nat := 118140960795 + 6361823 * 2 ^ 59
def prefixEnd_6361823 : Nat := 4983230072969 + 3 ^ 40 * 6361823 * 2
def baseEnd_6361823 : Nat := 1088891012609456023985005

theorem tailTrace_6361823 : CollatzResearch.WordTrace tailWord_6361823 prefixEnd_6361823 1088891012609456023985005 := by
  unfold tailWord_6361823
  simp only [CollatzResearch.WordTrace]
  refine ⟨232034747231209258711802123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154689831487472839141201415 232034747231209258711802123)
  ·
    refine ⟨348052120846813888067703185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232034747231209258711802123 348052120846813888067703185)
    ·
      refine ⟨261039090635110416050777389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 348052120846813888067703185 261039090635110416050777389)
      ·
        refine ⟨97889658988166406019041521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 261039090635110416050777389 97889658988166406019041521)
        ·
          refine ⟨73417244241124804514281141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97889658988166406019041521 73417244241124804514281141)
          ·
            refine ⟨6882866647605450423213857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 73417244241124804514281141 6882866647605450423213857)
            ·
              refine ⟨5162149985704087817410393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6882866647605450423213857 5162149985704087817410393)
              ·
                refine ⟨3871612489278065863057795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5162149985704087817410393 3871612489278065863057795)
                ·
                  refine ⟨5807418733917098794586693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3871612489278065863057795 5807418733917098794586693)
                  ·
                    refine ⟨1088891012609456023985005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5807418733917098794586693 1088891012609456023985005)
                    ·
                      rfl

theorem cell23_6361823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 2, 2, 1, 4].length) (baseStart_6361823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6361823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6361823 prefixEnd_6361823 := by exact prefixLift 6361823
  have htrace : WordTrace (prefixWord ++ tailWord_6361823) baseStart_6361823 baseEnd_6361823 := by
    simpa [prefixWord, tailWord_6361823, baseEnd_6361823] using wordTrace_append hprefix tailTrace_6361823
  have hstable : (prefixWord ++ tailWord_6361823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6361823).length < 2 ^ (prefixWord ++ tailWord_6361823).sum := by decide
  have hdescent : baseEnd_6361823 < baseStart_6361823 := by decide
  rcases family_descends (prefixWord ++ tailWord_6361823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6361846 : List Nat := [5, 1, 1, 1, 1, 2, 3, 2, 3, 1, 3]
def baseStart_6361846 : Nat := 118140960795 + 6361846 * 2 ^ 59
def prefixEnd_6361846 : Nat := 4983230072969 + 3 ^ 40 * 6361846 * 2
def baseEnd_6361846 : Nat := 3266684847883421481967409

theorem tailTrace_6361846 : CollatzResearch.WordTrace tailWord_6361846 prefixEnd_6361846 3266684847883421481967409 := by
  unfold tailWord_6361846
  simp only [CollatzResearch.WordTrace]
  refine ⟨14502224131882870852493087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 154690390740083955759926261 14502224131882870852493087)
  ·
    refine ⟨21753336197824306278739631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14502224131882870852493087 21753336197824306278739631)
    ·
      refine ⟨32630004296736459418109447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21753336197824306278739631 32630004296736459418109447)
      ·
        refine ⟨48945006445104689127164171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32630004296736459418109447 48945006445104689127164171)
        ·
          refine ⟨73417509667657033690746257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48945006445104689127164171 73417509667657033690746257)
          ·
            refine ⟨55063132250742775268059693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73417509667657033690746257 55063132250742775268059693)
            ·
              refine ⟨20648674594028540725522385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55063132250742775268059693 20648674594028540725522385)
              ·
                refine ⟨15486505945521405544141789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20648674594028540725522385 15486505945521405544141789)
                ·
                  refine ⟨5807439729570527079053171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15486505945521405544141789 5807439729570527079053171)
                  ·
                    refine ⟨8711159594355790618579757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5807439729570527079053171 8711159594355790618579757)
                    ·
                      refine ⟨3266684847883421481967409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8711159594355790618579757 3266684847883421481967409)
                      ·
                        rfl

theorem cell23_6361846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 2, 3, 1, 3].length) (baseStart_6361846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6361846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6361846 prefixEnd_6361846 := by exact prefixLift 6361846
  have htrace : WordTrace (prefixWord ++ tailWord_6361846) baseStart_6361846 baseEnd_6361846 := by
    simpa [prefixWord, tailWord_6361846, baseEnd_6361846] using wordTrace_append hprefix tailTrace_6361846
  have hstable : (prefixWord ++ tailWord_6361846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6361846).length < 2 ^ (prefixWord ++ tailWord_6361846).sum := by decide
  have hdescent : baseEnd_6361846 < baseStart_6361846 := by decide
  rcases family_descends (prefixWord ++ tailWord_6361846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6361863 : List Nat := [1, 1, 4, 4, 1, 1, 1, 5, 1, 1, 3]
def baseStart_6361863 : Nat := 118140960795 + 6361863 * 2 ^ 59
def prefixEnd_6361863 : Nat := 4983230072969 + 3 ^ 40 * 6361863 * 2
def baseEnd_6361863 : Nat := 3266693577054547915454831

theorem tailTrace_6361863 : CollatzResearch.WordTrace tailWord_6361863 prefixEnd_6361863 3266693577054547915454831 := by
  unfold tailWord_6361863
  simp only [CollatzResearch.WordTrace]
  refine ⟨232036206151064345543258243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154690804100709563695505495 232036206151064345543258243)
  ·
    refine ⟨348054309226596518314887365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232036206151064345543258243 348054309226596518314887365)
    ·
      refine ⟨65260182979986847184041381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 348054309226596518314887365 65260182979986847184041381)
      ·
        refine ⟨12236284308747533847007759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65260182979986847184041381 12236284308747533847007759)
        ·
          refine ⟨18354426463121300770511639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12236284308747533847007759 18354426463121300770511639)
          ·
            refine ⟨27531639694681951155767459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18354426463121300770511639 27531639694681951155767459)
            ·
              refine ⟨41297459542022926733651189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27531639694681951155767459 41297459542022926733651189)
              ·
                refine ⟨3871636832064649381279799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41297459542022926733651189 3871636832064649381279799)
                ·
                  refine ⟨5807455248096974071919699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3871636832064649381279799 5807455248096974071919699)
                  ·
                    refine ⟨8711182872145461107879549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5807455248096974071919699 8711182872145461107879549)
                    ·
                      refine ⟨3266693577054547915454831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8711182872145461107879549 3266693577054547915454831)
                      ·
                        rfl

theorem cell23_6361863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 5, 1, 1, 3].length) (baseStart_6361863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6361863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6361863 prefixEnd_6361863 := by exact prefixLift 6361863
  have htrace : WordTrace (prefixWord ++ tailWord_6361863) baseStart_6361863 baseEnd_6361863 := by
    simpa [prefixWord, tailWord_6361863, baseEnd_6361863] using wordTrace_append hprefix tailTrace_6361863
  have hstable : (prefixWord ++ tailWord_6361863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6361863).length < 2 ^ (prefixWord ++ tailWord_6361863).sum := by decide
  have hdescent : baseEnd_6361863 < baseStart_6361863 := by decide
  rcases family_descends (prefixWord ++ tailWord_6361863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6361875 : List Nat := [1, 1, 1, 2, 1, 3, 14]
def baseStart_6361875 : Nat := 118140960795 + 6361875 * 2 ^ 59
def prefixEnd_6361875 : Nat := 4983230072969 + 3 ^ 40 * 6361875 * 2
def baseEnd_6361875 : Nat := 40329626405214837882775

theorem tailTrace_6361875 : CollatzResearch.WordTrace tailWord_6361875 prefixEnd_6361875 40329626405214837882775 := by
  unfold tailWord_6361875
  simp only [CollatzResearch.WordTrace]
  refine ⟨232036643827020871592695079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154691095884680581061796719 232036643827020871592695079)
  ·
    refine ⟨348054965740531307389042619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232036643827020871592695079 348054965740531307389042619)
    ·
      refine ⟨522082448610796961083563929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348054965740531307389042619 522082448610796961083563929)
      ·
        refine ⟨391561836458097720812672947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 522082448610796961083563929 391561836458097720812672947)
        ·
          refine ⟨587342754687146581219009421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 391561836458097720812672947 587342754687146581219009421)
          ·
            refine ⟨220253533007679967957128533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 587342754687146581219009421 220253533007679967957128533)
            ·
              refine ⟨40329626405214837882775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 14 220253533007679967957128533 40329626405214837882775)
              ·
                rfl

theorem cell23_6361875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 14].length) (baseStart_6361875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6361875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6361875 prefixEnd_6361875 := by exact prefixLift 6361875
  have htrace : WordTrace (prefixWord ++ tailWord_6361875) baseStart_6361875 baseEnd_6361875 := by
    simpa [prefixWord, tailWord_6361875, baseEnd_6361875] using wordTrace_append hprefix tailTrace_6361875
  have hstable : (prefixWord ++ tailWord_6361875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6361875).length < 2 ^ (prefixWord ++ tailWord_6361875).sum := by decide
  have hdescent : baseEnd_6361875 < baseStart_6361875 := by decide
  rcases family_descends (prefixWord ++ tailWord_6361875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6361882 : List Nat := [3, 1, 1, 3, 2, 1, 2, 2, 1, 1, 6]
def baseStart_6361882 : Nat := 118140960795 + 6361882 * 2 ^ 59
def prefixEnd_6361882 : Nat := 4983230072969 + 3 ^ 40 * 6361882 * 2
def baseEnd_6361882 : Nat := 3266703333186983341117243

theorem tailTrace_6361882 : CollatzResearch.WordTrace tailWord_6361882 prefixEnd_6361882 3266703333186983341117243 := by
  unfold tailWord_6361882
  simp only [CollatzResearch.WordTrace]
  refine ⟨58009224784498877947049975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154691266091997007858799933 58009224784498877947049975)
  ·
    refine ⟨87013837176748316920574963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58009224784498877947049975 87013837176748316920574963)
    ·
      refine ⟨130520755765122475380862445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87013837176748316920574963 130520755765122475380862445)
      ·
        refine ⟨48945283411920928267823417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130520755765122475380862445 48945283411920928267823417)
        ·
          refine ⟨36708962558940696200867563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48945283411920928267823417 36708962558940696200867563)
          ·
            refine ⟨55063443838411044301301345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36708962558940696200867563 55063443838411044301301345)
            ·
              refine ⟨41297582878808283225976009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55063443838411044301301345 41297582878808283225976009)
              ·
                refine ⟨30973187159106212419482007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41297582878808283225976009 30973187159106212419482007)
                ·
                  refine ⟨46459780738659318629223011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30973187159106212419482007 46459780738659318629223011)
                  ·
                    refine ⟨69689671107988977943834517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46459780738659318629223011 69689671107988977943834517)
                    ·
                      refine ⟨3266703333186983341117243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69689671107988977943834517 3266703333186983341117243)
                      ·
                        rfl

theorem cell23_6361882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 2, 1, 1, 6].length) (baseStart_6361882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6361882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6361882 prefixEnd_6361882 := by exact prefixLift 6361882
  have htrace : WordTrace (prefixWord ++ tailWord_6361882) baseStart_6361882 baseEnd_6361882 := by
    simpa [prefixWord, tailWord_6361882, baseEnd_6361882] using wordTrace_append hprefix tailTrace_6361882
  have hstable : (prefixWord ++ tailWord_6361882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6361882).length < 2 ^ (prefixWord ++ tailWord_6361882).sum := by decide
  have hdescent : baseEnd_6361882 < baseStart_6361882 := by decide
  rcases family_descends (prefixWord ++ tailWord_6361882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6361906 : List Nat := [3, 2, 1, 1, 3, 1, 4, 2, 1, 2, 3]
def baseStart_6361906 : Nat := 118140960795 + 6361906 * 2 ^ 59
def prefixEnd_6361906 : Nat := 4983230072969 + 3 ^ 40 * 6361906 * 2
def baseEnd_6361906 : Nat := 3266715656722691247217133

theorem tailTrace_6361906 : CollatzResearch.WordTrace tailWord_6361906 prefixEnd_6361906 3266715656722691247217133 := by
  unfold tailWord_6361906
  simp only [CollatzResearch.WordTrace]
  refine ⟨58009443622477140971768393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154691849659939042591382381 58009443622477140971768393)
  ·
    refine ⟨43507082716857855728826295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58009443622477140971768393 43507082716857855728826295)
    ·
      refine ⟨65260624075286783593239443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43507082716857855728826295 65260624075286783593239443)
      ·
        refine ⟨97890936112930175389859165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65260624075286783593239443 97890936112930175389859165)
        ·
          refine ⟨36709101042348815771197187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97890936112930175389859165 36709101042348815771197187)
          ·
            refine ⟨55063651563523223656795781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36709101042348815771197187 55063651563523223656795781)
            ·
              refine ⟨10324434668160604435649209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55063651563523223656795781 10324434668160604435649209)
              ·
                refine ⟨7743326001120453326736907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10324434668160604435649209 7743326001120453326736907)
                ·
                  refine ⟨11614989001680679990105361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7743326001120453326736907 11614989001680679990105361)
                  ·
                    refine ⟨8711241751260509992579021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11614989001680679990105361 8711241751260509992579021)
                    ·
                      refine ⟨3266715656722691247217133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8711241751260509992579021 3266715656722691247217133)
                      ·
                        rfl

theorem cell23_6361906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 2, 1, 2, 3].length) (baseStart_6361906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6361906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6361906 prefixEnd_6361906 := by exact prefixLift 6361906
  have htrace : WordTrace (prefixWord ++ tailWord_6361906) baseStart_6361906 baseEnd_6361906 := by
    simpa [prefixWord, tailWord_6361906, baseEnd_6361906] using wordTrace_append hprefix tailTrace_6361906
  have hstable : (prefixWord ++ tailWord_6361906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6361906).length < 2 ^ (prefixWord ++ tailWord_6361906).sum := by decide
  have hdescent : baseEnd_6361906 < baseStart_6361906 := by decide
  rcases family_descends (prefixWord ++ tailWord_6361906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6361909 : List Nat := [1, 3, 3, 1, 3, 1, 4, 7]
def baseStart_6361909 : Nat := 118140960795 + 6361909 * 2 ^ 59
def prefixEnd_6361909 : Nat := 4983230072969 + 3 ^ 40 * 6361909 * 2
def baseEnd_6361909 : Nat := 120989525820913138351097

theorem tailTrace_6361909 : CollatzResearch.WordTrace tailWord_6361909 prefixEnd_6361909 120989525820913138351097 := by
  unfold tailWord_6361909
  simp only [CollatzResearch.WordTrace]
  refine ⟨232037883908897695399432781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154691922605931796932955187 232037883908897695399432781)
  ·
    refine ⟨87014206465836635774787293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 232037883908897695399432781 87014206465836635774787293)
    ·
      refine ⟨32630327424688738415545235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87014206465836635774787293 32630327424688738415545235)
      ·
        refine ⟨48945491137033107623317853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32630327424688738415545235 48945491137033107623317853)
        ·
          refine ⟨18354559176387415358744195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48945491137033107623317853 18354559176387415358744195)
          ·
            refine ⟨27531838764581123038116293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18354559176387415358744195 27531838764581123038116293)
            ·
              refine ⟨5162219768358960569646805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27531838764581123038116293 5162219768358960569646805)
              ·
                refine ⟨120989525820913138351097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5162219768358960569646805 120989525820913138351097)
                ·
                  rfl

theorem cell23_6361909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 4, 7].length) (baseStart_6361909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6361909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6361909 prefixEnd_6361909 := by exact prefixLift 6361909
  have htrace : WordTrace (prefixWord ++ tailWord_6361909) baseStart_6361909 baseEnd_6361909 := by
    simpa [prefixWord, tailWord_6361909, baseEnd_6361909] using wordTrace_append hprefix tailTrace_6361909
  have hstable : (prefixWord ++ tailWord_6361909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6361909).length < 2 ^ (prefixWord ++ tailWord_6361909).sum := by decide
  have hdescent : baseEnd_6361909 < baseStart_6361909 := by decide
  rcases family_descends (prefixWord ++ tailWord_6361909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6361937 : List Nat := [1, 2, 2, 1, 6, 1, 3, 2, 1, 2, 2]
def baseStart_6361937 : Nat := 118140960795 + 6361937 * 2 ^ 59
def prefixEnd_6361937 : Nat := 4983230072969 + 3 ^ 40 * 6361937 * 2
def baseEnd_6361937 : Nat := 3266731574622980625929491

theorem tailTrace_6361937 : CollatzResearch.WordTrace tailWord_6361937 prefixEnd_6361937 3266731574622980625929491 := by
  unfold tailWord_6361937
  simp only [CollatzResearch.WordTrace]
  refine ⟨232038905152796256181452065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154692603435197504120968043 232038905152796256181452065)
  ·
    refine ⟨174029178864597192136089049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232038905152796256181452065 174029178864597192136089049)
    ·
      refine ⟨130521884148447894102066787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174029178864597192136089049 130521884148447894102066787)
      ·
        refine ⟨195782826222671841153100181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130521884148447894102066787 195782826222671841153100181)
        ·
          refine ⟨9177319979187742554051571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 195782826222671841153100181 9177319979187742554051571)
          ·
            refine ⟨13765979968781613831077357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9177319979187742554051571 13765979968781613831077357)
            ·
              refine ⟨5162242488293105186654009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13765979968781613831077357 5162242488293105186654009)
              ·
                refine ⟨3871681866219828889990507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5162242488293105186654009 3871681866219828889990507)
                ·
                  refine ⟨5807522799329743334985761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3871681866219828889990507 5807522799329743334985761)
                  ·
                    refine ⟨4355642099497307501239321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5807522799329743334985761 4355642099497307501239321)
                    ·
                      refine ⟨3266731574622980625929491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4355642099497307501239321 3266731574622980625929491)
                      ·
                        rfl

theorem cell23_6361937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 3, 2, 1, 2, 2].length) (baseStart_6361937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6361937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6361937 prefixEnd_6361937 := by exact prefixLift 6361937
  have htrace : WordTrace (prefixWord ++ tailWord_6361937) baseStart_6361937 baseEnd_6361937 := by
    simpa [prefixWord, tailWord_6361937, baseEnd_6361937] using wordTrace_append hprefix tailTrace_6361937
  have hstable : (prefixWord ++ tailWord_6361937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6361937).length < 2 ^ (prefixWord ++ tailWord_6361937).sum := by decide
  have hdescent : baseEnd_6361937 < baseStart_6361937 := by decide
  rcases family_descends (prefixWord ++ tailWord_6361937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6361952 : List Nat := [2, 1, 1, 3, 3, 1, 2, 1, 1, 8]
def baseStart_6361952 : Nat := 118140960795 + 6361952 * 2 ^ 59
def prefixEnd_6361952 : Nat := 4983230072969 + 3 ^ 40 * 6361952 * 2
def baseEnd_6361952 : Nat := 1088913092277599355747307

theorem tailTrace_6361952 : CollatzResearch.WordTrace tailWord_6361952 prefixEnd_6361952 1088913092277599355747307 := by
  unfold tailWord_6361952
  simp only [CollatzResearch.WordTrace]
  refine ⟨116019726123870956871624055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154692968165161275828832073 116019726123870956871624055)
  ·
    refine ⟨174029589185806435307436083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116019726123870956871624055 174029589185806435307436083)
    ·
      refine ⟨261044383778709652961154125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174029589185806435307436083 261044383778709652961154125)
      ·
        refine ⟨97891643917016119860432797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 261044383778709652961154125 97891643917016119860432797)
        ·
          refine ⟨36709366468881044947662299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97891643917016119860432797 36709366468881044947662299)
          ·
            refine ⟨55064049703321567421493449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36709366468881044947662299 55064049703321567421493449)
            ·
              refine ⟨41298037277491175566120087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55064049703321567421493449 41298037277491175566120087)
              ·
                refine ⟨61947055916236763349180131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41298037277491175566120087 61947055916236763349180131)
                ·
                  refine ⟨92920583874355145023770197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61947055916236763349180131 92920583874355145023770197)
                  ·
                    refine ⟨1088913092277599355747307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 92920583874355145023770197 1088913092277599355747307)
                    ·
                      rfl

theorem cell23_6361952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 1, 1, 8].length) (baseStart_6361952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6361952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6361952 prefixEnd_6361952 := by exact prefixLift 6361952
  have htrace : WordTrace (prefixWord ++ tailWord_6361952) baseStart_6361952 baseEnd_6361952 := by
    simpa [prefixWord, tailWord_6361952, baseEnd_6361952] using wordTrace_append hprefix tailTrace_6361952
  have hstable : (prefixWord ++ tailWord_6361952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6361952).length < 2 ^ (prefixWord ++ tailWord_6361952).sum := by decide
  have hdescent : baseEnd_6361952 < baseStart_6361952 := by decide
  rcases family_descends (prefixWord ++ tailWord_6361952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6361976 : List Nat := [2, 1, 2, 1, 1, 1, 1, 6, 4, 2, 2]
def baseStart_6361976 : Nat := 118140960795 + 6361976 * 2 ^ 59
def prefixEnd_6361976 : Nat := 4983230072969 + 3 ^ 40 * 6361976 * 2
def baseEnd_6361976 : Nat := 3266751600368505973341811

theorem tailTrace_6361976 : CollatzResearch.WordTrace tailWord_6361976 prefixEnd_6361976 3266751600368505973341811 := by
  unfold tailWord_6361976
  simp only [CollatzResearch.WordTrace]
  refine ⟨116020163799827482921060891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154693551733103310561414521 116020163799827482921060891)
  ·
    refine ⟨174030245699741224381591337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116020163799827482921060891 174030245699741224381591337)
    ·
      refine ⟨130522684274805918286193503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174030245699741224381591337 130522684274805918286193503)
      ·
        refine ⟨195784026412208877429290255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130522684274805918286193503 195784026412208877429290255)
        ·
          refine ⟨293676039618313316143935383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195784026412208877429290255 293676039618313316143935383)
          ·
            refine ⟨440514059427469974215903075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 293676039618313316143935383 440514059427469974215903075)
            ·
              refine ⟨660771089141204961323854613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 440514059427469974215903075 660771089141204961323854613)
              ·
                refine ⟨30973644803493982562055685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 660771089141204961323854613 30973644803493982562055685)
                ·
                  refine ⟨5807558400655121730385441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30973644803493982562055685 5807558400655121730385441)
                  ·
                    refine ⟨4355668800491341297789081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5807558400655121730385441 4355668800491341297789081)
                    ·
                      refine ⟨3266751600368505973341811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4355668800491341297789081 3266751600368505973341811)
                      ·
                        rfl

theorem cell23_6361976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 6, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 6, 4, 2, 2].length) (baseStart_6361976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6361976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6361976 prefixEnd_6361976 := by exact prefixLift 6361976
  have htrace : WordTrace (prefixWord ++ tailWord_6361976) baseStart_6361976 baseEnd_6361976 := by
    simpa [prefixWord, tailWord_6361976, baseEnd_6361976] using wordTrace_append hprefix tailTrace_6361976
  have hstable : (prefixWord ++ tailWord_6361976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6361976).length < 2 ^ (prefixWord ++ tailWord_6361976).sum := by decide
  have hdescent : baseEnd_6361976 < baseStart_6361976 := by decide
  rcases family_descends (prefixWord ++ tailWord_6361976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6361993 : List Nat := [1, 2, 1, 1, 5, 2, 1, 4, 2, 2, 2]
def baseStart_6361993 : Nat := 118140960795 + 6361993 * 2 ^ 59
def prefixEnd_6361993 : Nat := 4983230072969 + 3 ^ 40 * 6361993 * 2
def baseEnd_6361993 : Nat := 3266760329539632406829233

theorem tailTrace_6361993 : CollatzResearch.WordTrace tailWord_6361993 prefixEnd_6361993 3266760329539632406829233 := by
  unfold tailWord_6361993
  simp only [CollatzResearch.WordTrace]
  refine ⟨232040947640593377745490633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154693965093728918496993755 232040947640593377745490633)
  ·
    refine ⟨174030710730445033309117975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232040947640593377745490633 174030710730445033309117975)
    ·
      refine ⟨261046066095667549963676963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174030710730445033309117975 261046066095667549963676963)
      ·
        refine ⟨391569099143501324945515445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261046066095667549963676963 391569099143501324945515445)
        ·
          refine ⟨36709603044703249213642073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 391569099143501324945515445 36709603044703249213642073)
          ·
            refine ⟨27532202283527436910231555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36709603044703249213642073 27532202283527436910231555)
            ·
              refine ⟨41298303425291155365347333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27532202283527436910231555 41298303425291155365347333)
              ·
                refine ⟨7743431892242091631002625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41298303425291155365347333 7743431892242091631002625)
                ·
                  refine ⟨5807573919181568723251969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7743431892242091631002625 5807573919181568723251969)
                  ·
                    refine ⟨4355680439386176542438977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5807573919181568723251969 4355680439386176542438977)
                    ·
                      refine ⟨3266760329539632406829233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4355680439386176542438977 3266760329539632406829233)
                      ·
                        rfl

theorem cell23_6361993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 4, 2, 2, 2].length) (baseStart_6361993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6361993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6361993 prefixEnd_6361993 := by exact prefixLift 6361993
  have htrace : WordTrace (prefixWord ++ tailWord_6361993) baseStart_6361993 baseEnd_6361993 := by
    simpa [prefixWord, tailWord_6361993, baseEnd_6361993] using wordTrace_append hprefix tailTrace_6361993
  have hstable : (prefixWord ++ tailWord_6361993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6361993).length < 2 ^ (prefixWord ++ tailWord_6361993).sum := by decide
  have hdescent : baseEnd_6361993 < baseStart_6361993 := by decide
  rcases family_descends (prefixWord ++ tailWord_6361993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6362033 : List Nat := [1, 2, 2, 4, 3, 1, 2, 3, 5]
def baseStart_6362033 : Nat := 118140960795 + 6362033 * 2 ^ 59
def prefixEnd_6362033 : Nat := 4983230072969 + 3 ^ 40 * 6362033 * 2
def baseEnd_6362033 : Nat := 362975652085090250036561

theorem tailTrace_6362033 : CollatzResearch.WordTrace tailWord_6362033 prefixEnd_6362033 362975652085090250036561 := by
  unfold tailWord_6362033
  simp only [CollatzResearch.WordTrace]
  refine ⟨232042406560448464576946753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154694937706965643051297835 232042406560448464576946753)
  ·
    refine ⟨174031804920336348432710065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232042406560448464576946753 174031804920336348432710065)
    ·
      refine ⟨130523853690252261324532549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174031804920336348432710065 130523853690252261324532549)
      ·
        refine ⟨24473222566922298998349853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 130523853690252261324532549 24473222566922298998349853)
        ·
          refine ⟨9177458462595862124381195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24473222566922298998349853 9177458462595862124381195)
          ·
            refine ⟨13766187693893793186571793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9177458462595862124381195 13766187693893793186571793)
            ·
              refine ⟨10324640770420344889928845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13766187693893793186571793 10324640770420344889928845)
              ·
                refine ⟨3871740288907629333723317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10324640770420344889928845 3871740288907629333723317)
                ·
                  refine ⟨362975652085090250036561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3871740288907629333723317 362975652085090250036561)
                  ·
                    rfl

theorem cell23_6362033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 3, 5].length) (baseStart_6362033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6362033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6362033 prefixEnd_6362033 := by exact prefixLift 6362033
  have htrace : WordTrace (prefixWord ++ tailWord_6362033) baseStart_6362033 baseEnd_6362033 := by
    simpa [prefixWord, tailWord_6362033, baseEnd_6362033] using wordTrace_append hprefix tailTrace_6362033
  have hstable : (prefixWord ++ tailWord_6362033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6362033).length < 2 ^ (prefixWord ++ tailWord_6362033).sum := by decide
  have hdescent : baseEnd_6362033 < baseStart_6362033 := by decide
  rcases family_descends (prefixWord ++ tailWord_6362033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6362061 : List Nat := [1, 6, 3, 1, 2, 1, 1, 1, 1, 4, 2]
def baseStart_6362061 : Nat := 118140960795 + 6362061 * 2 ^ 59
def prefixEnd_6362061 : Nat := 4983230072969 + 3 ^ 40 * 6362061 * 2
def baseEnd_6362061 : Nat := 3266795246224138140778921

theorem tailTrace_6362061 : CollatzResearch.WordTrace tailWord_6362061 prefixEnd_6362061 3266795246224138140778921 := by
  unfold tailWord_6362061
  simp only [CollatzResearch.WordTrace]
  refine ⟨232043427804347025358966037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154695618536231350239310691 232043427804347025358966037)
  ·
    refine ⟨10877035678328766813701533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 232043427804347025358966037 10877035678328766813701533)
    ·
      refine ⟨4078888379373287555138075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10877035678328766813701533 4078888379373287555138075)
      ·
        refine ⟨6118332569059931332707113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4078888379373287555138075 6118332569059931332707113)
        ·
          refine ⟨4588749426794948499530335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6118332569059931332707113 4588749426794948499530335)
          ·
            refine ⟨6883124140192422749295503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4588749426794948499530335 6883124140192422749295503)
            ·
              refine ⟨10324686210288634123943255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6883124140192422749295503 10324686210288634123943255)
              ·
                refine ⟨15487029315432951185914883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10324686210288634123943255 15487029315432951185914883)
                ·
                  refine ⟨23230543973149426778872325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15487029315432951185914883 23230543973149426778872325)
                  ·
                    refine ⟨4355726994965517521038561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23230543973149426778872325 4355726994965517521038561)
                    ·
                      refine ⟨3266795246224138140778921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4355726994965517521038561 3266795246224138140778921)
                      ·
                        rfl

theorem cell23_6362061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_6362061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6362061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6362061 prefixEnd_6362061 := by exact prefixLift 6362061
  have htrace : WordTrace (prefixWord ++ tailWord_6362061) baseStart_6362061 baseEnd_6362061 := by
    simpa [prefixWord, tailWord_6362061, baseEnd_6362061] using wordTrace_append hprefix tailTrace_6362061
  have hstable : (prefixWord ++ tailWord_6362061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6362061).length < 2 ^ (prefixWord ++ tailWord_6362061).sum := by decide
  have hdescent : baseEnd_6362061 < baseStart_6362061 := by decide
  rcases family_descends (prefixWord ++ tailWord_6362061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6362066 : List Nat := [3, 2, 2, 3, 1, 1, 1, 2, 1, 3, 4]
def baseStart_6362066 : Nat := 118140960795 + 6362066 * 2 ^ 59
def prefixEnd_6362066 : Nat := 4983230072969 + 3 ^ 40 * 6362066 * 2
def baseEnd_6362066 : Nat := 3266797813627410621216397

theorem tailTrace_6362066 : CollatzResearch.WordTrace tailWord_6362066 prefixEnd_6362066 3266797813627410621216397 := by
  unfold tailWord_6362066
  simp only [CollatzResearch.WordTrace]
  refine ⟨58010902542332227803224513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154695740112885940808598701 58010902542332227803224513)
  ·
    refine ⟨43508176906749170852418385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58010902542332227803224513 43508176906749170852418385)
    ·
      refine ⟨32631132680061878139313789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43508176906749170852418385 32631132680061878139313789)
      ·
        refine ⟨12236674755023204302242671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32631132680061878139313789 12236674755023204302242671)
        ·
          refine ⟨18355012132534806453364007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12236674755023204302242671 18355012132534806453364007)
          ·
            refine ⟨27532518198802209680046011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18355012132534806453364007 27532518198802209680046011)
            ·
              refine ⟨41298777298203314520069017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27532518198802209680046011 41298777298203314520069017)
              ·
                refine ⟨30974082973652485890051763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41298777298203314520069017 30974082973652485890051763)
                ·
                  refine ⟨46461124460478728835077645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30974082973652485890051763 46461124460478728835077645)
                  ·
                    refine ⟨17422921672679523313154117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46461124460478728835077645 17422921672679523313154117)
                    ·
                      refine ⟨3266797813627410621216397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17422921672679523313154117 3266797813627410621216397)
                      ·
                        rfl

theorem cell23_6362066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_6362066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6362066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6362066 prefixEnd_6362066 := by exact prefixLift 6362066
  have htrace : WordTrace (prefixWord ++ tailWord_6362066) baseStart_6362066 baseEnd_6362066 := by
    simpa [prefixWord, tailWord_6362066, baseEnd_6362066] using wordTrace_append hprefix tailTrace_6362066
  have hstable : (prefixWord ++ tailWord_6362066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6362066).length < 2 ^ (prefixWord ++ tailWord_6362066).sum := by decide
  have hdescent : baseEnd_6362066 < baseStart_6362066 := by decide
  rcases family_descends (prefixWord ++ tailWord_6362066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6362123 : List Nat := [1, 1, 1, 1, 6, 4, 2, 1, 6]
def baseStart_6362123 : Nat := 118140960795 + 6362123 * 2 ^ 59
def prefixEnd_6362123 : Nat := 4983230072969 + 3 ^ 40 * 6362123 * 2
def baseEnd_6362123 : Nat := 362980786891635210911515

theorem tailTrace_6362123 : CollatzResearch.WordTrace tailWord_6362123 prefixEnd_6362123 362980786891635210911515 := by
  unfold tailWord_6362123
  simp only [CollatzResearch.WordTrace]
  refine ⟨232045689130122409947723023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154697126086748273298482015 232045689130122409947723023)
  ·
    refine ⟨348068533695183614921584535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232045689130122409947723023 348068533695183614921584535)
    ·
      refine ⟨522102800542775422382376803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348068533695183614921584535 522102800542775422382376803)
      ·
        refine ⟨783154200814163133573565205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 522102800542775422382376803 783154200814163133573565205)
        ·
          refine ⟨36710353163163896886260869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 783154200814163133573565205 36710353163163896886260869)
          ·
            refine ⟨6883191218093230666173913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36710353163163896886260869 6883191218093230666173913)
            ·
              refine ⟨5162393413569922999630435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6883191218093230666173913 5162393413569922999630435)
              ·
                refine ⟨7743590120354884499445653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5162393413569922999630435 7743590120354884499445653)
                ·
                  refine ⟨362980786891635210911515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7743590120354884499445653 362980786891635210911515)
                  ·
                    rfl

theorem cell23_6362123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 2, 1, 6].length) (baseStart_6362123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6362123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6362123 prefixEnd_6362123 := by exact prefixLift 6362123
  have htrace : WordTrace (prefixWord ++ tailWord_6362123) baseStart_6362123 baseEnd_6362123 := by
    simpa [prefixWord, tailWord_6362123, baseEnd_6362123] using wordTrace_append hprefix tailTrace_6362123
  have hstable : (prefixWord ++ tailWord_6362123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6362123).length < 2 ^ (prefixWord ++ tailWord_6362123).sum := by decide
  have hdescent : baseEnd_6362123 < baseStart_6362123 := by decide
  rcases family_descends (prefixWord ++ tailWord_6362123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6362136 : List Nat := [2, 1, 2, 3, 2, 3, 1, 1, 3, 5]
def baseStart_6362136 : Nat := 118140960795 + 6362136 * 2 ^ 59
def prefixEnd_6362136 : Nat := 4983230072969 + 3 ^ 40 * 6362136 * 2
def baseEnd_6362136 : Nat := 1088944585757741782447025

theorem tailTrace_6362136 : CollatzResearch.WordTrace tailWord_6362136 prefixEnd_6362136 1088944585757741782447025 := by
  unfold tailWord_6362136
  simp only [CollatzResearch.WordTrace]
  refine ⟨116023081639537656583973131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154697442186050208778630841 116023081639537656583973131)
  ·
    refine ⟨174034622459306484875959697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116023081639537656583973131 174034622459306484875959697)
    ·
      refine ⟨130525966844479863656969773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174034622459306484875959697 130525966844479863656969773)
      ·
        refine ⟨48947237566679948871363665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130525966844479863656969773 48947237566679948871363665)
        ·
          refine ⟨36710428175009961653522749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48947237566679948871363665 36710428175009961653522749)
          ·
            refine ⟨13766410565628735620071031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36710428175009961653522749 13766410565628735620071031)
            ·
              refine ⟨20649615848443103430106547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13766410565628735620071031 20649615848443103430106547)
              ·
                refine ⟨30974423772664655145159821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20649615848443103430106547 30974423772664655145159821)
                ·
                  refine ⟨11615408914749245679434933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30974423772664655145159821 11615408914749245679434933)
                  ·
                    refine ⟨1088944585757741782447025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11615408914749245679434933 1088944585757741782447025)
                    ·
                      rfl

theorem cell23_6362136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 1, 3, 5].length) (baseStart_6362136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6362136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6362136 prefixEnd_6362136 := by exact prefixLift 6362136
  have htrace : WordTrace (prefixWord ++ tailWord_6362136) baseStart_6362136 baseEnd_6362136 := by
    simpa [prefixWord, tailWord_6362136, baseEnd_6362136] using wordTrace_append hprefix tailTrace_6362136
  have hstable : (prefixWord ++ tailWord_6362136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6362136).length < 2 ^ (prefixWord ++ tailWord_6362136).sum := by decide
  have hdescent : baseEnd_6362136 < baseStart_6362136 := by decide
  rcases family_descends (prefixWord ++ tailWord_6362136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6362143 : List Nat := [1, 1, 2, 4, 1, 3, 1, 3, 2, 3, 2]
def baseStart_6362143 : Nat := 118140960795 + 6362143 * 2 ^ 59
def prefixEnd_6362143 : Nat := 4983230072969 + 3 ^ 40 * 6362143 * 2
def baseEnd_6362143 : Nat := 3266837351637806819953543

theorem tailTrace_6362143 : CollatzResearch.WordTrace tailWord_6362143 prefixEnd_6362143 3266837351637806819953543 := by
  unfold tailWord_6362143
  simp only [CollatzResearch.WordTrace]
  refine ⟨232046418590049953363451083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154697612393366635575634055 232046418590049953363451083)
  ·
    refine ⟨348069627885074930045176625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232046418590049953363451083 348069627885074930045176625)
    ·
      refine ⟨261052220913806197533882469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 348069627885074930045176625 261052220913806197533882469)
      ·
        refine ⟨48947291421338662037602963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 261052220913806197533882469 48947291421338662037602963)
        ·
          refine ⟨73420937132007993056404445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48947291421338662037602963 73420937132007993056404445)
          ·
            refine ⟨27532851424502997396151667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73420937132007993056404445 27532851424502997396151667)
            ·
              refine ⟨41299277136754496094227501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27532851424502997396151667 41299277136754496094227501)
              ·
                refine ⟨15487228926282936035335313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41299277136754496094227501 15487228926282936035335313)
                ·
                  refine ⟨11615421694712202026501485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15487228926282936035335313 11615421694712202026501485)
                  ·
                    refine ⟨4355783135517075759938057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11615421694712202026501485 4355783135517075759938057)
                    ·
                      refine ⟨3266837351637806819953543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4355783135517075759938057 3266837351637806819953543)
                      ·
                        rfl

theorem cell23_6362143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 3, 2, 3, 2].length) (baseStart_6362143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6362143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6362143 prefixEnd_6362143 := by exact prefixLift 6362143
  have htrace : WordTrace (prefixWord ++ tailWord_6362143) baseStart_6362143 baseEnd_6362143 := by
    simpa [prefixWord, tailWord_6362143, baseEnd_6362143] using wordTrace_append hprefix tailTrace_6362143
  have hstable : (prefixWord ++ tailWord_6362143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6362143).length < 2 ^ (prefixWord ++ tailWord_6362143).sum := by decide
  have hdescent : baseEnd_6362143 < baseStart_6362143 := by decide
  rcases family_descends (prefixWord ++ tailWord_6362143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6362176 : List Nat := [2, 1, 1, 2, 2, 3, 1, 1, 5, 2, 3]
def baseStart_6362176 : Nat := 118140960795 + 6362176 * 2 ^ 59
def prefixEnd_6362176 : Nat := 4983230072969 + 3 ^ 40 * 6362176 * 2
def baseEnd_6362176 : Nat := 3266854296499405190840891

theorem tailTrace_6362176 : CollatzResearch.WordTrace tailWord_6362176 prefixEnd_6362176 3266854296499405190840891 := by
  unfold tailWord_6362176
  simp only [CollatzResearch.WordTrace]
  refine ⟨116023811099465199999701191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154698414799286933332934921 116023811099465199999701191)
  ·
    refine ⟨174035716649197799999551787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116023811099465199999701191 174035716649197799999551787)
    ·
      refine ⟨261053574973796699999327681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174035716649197799999551787 261053574973796699999327681)
      ·
        refine ⟨195790181230347524999495761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 261053574973796699999327681 195790181230347524999495761)
        ·
          refine ⟨146842635922760643749621821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 195790181230347524999495761 146842635922760643749621821)
          ·
            refine ⟨55065988471035241406108183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 146842635922760643749621821 55065988471035241406108183)
            ·
              refine ⟨82598982706552862109162275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55065988471035241406108183 82598982706552862109162275)
              ·
                refine ⟨123898474059829293163743413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82598982706552862109162275 123898474059829293163743413)
                ·
                  refine ⟨11615481943108996234100945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 123898474059829293163743413 11615481943108996234100945)
                  ·
                    refine ⟨8711611457331747175575709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11615481943108996234100945 8711611457331747175575709)
                    ·
                      refine ⟨3266854296499405190840891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8711611457331747175575709 3266854296499405190840891)
                      ·
                        rfl

theorem cell23_6362176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 5, 2, 3].length) (baseStart_6362176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6362176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6362176 prefixEnd_6362176 := by exact prefixLift 6362176
  have htrace : WordTrace (prefixWord ++ tailWord_6362176) baseStart_6362176 baseEnd_6362176 := by
    simpa [prefixWord, tailWord_6362176, baseEnd_6362176] using wordTrace_append hprefix tailTrace_6362176
  have hstable : (prefixWord ++ tailWord_6362176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6362176).length < 2 ^ (prefixWord ++ tailWord_6362176).sum := by decide
  have hdescent : baseEnd_6362176 < baseStart_6362176 := by decide
  rcases family_descends (prefixWord ++ tailWord_6362176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6362183 : List Nat := [1, 1, 4, 1, 3, 2, 2, 3, 2, 4]
def baseStart_6362183 : Nat := 118140960795 + 6362183 * 2 ^ 59
def prefixEnd_6362183 : Nat := 4983230072969 + 3 ^ 40 * 6362183 * 2
def baseEnd_6362183 : Nat := 1088952630287995554484453

theorem tailTrace_6362183 : CollatzResearch.WordTrace tailWord_6362183 prefixEnd_6362183 1088952630287995554484453 := by
  unfold tailWord_6362183
  simp only [CollatzResearch.WordTrace]
  refine ⟨232047877509905040194907203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154698585006603360129938135 232047877509905040194907203)
  ·
    refine ⟨348071816264857560292360805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232047877509905040194907203 348071816264857560292360805)
    ·
      refine ⟨65263465549660792554817651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 348071816264857560292360805 65263465549660792554817651)
      ·
        refine ⟨97895198324491188832226477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65263465549660792554817651 97895198324491188832226477)
        ·
          refine ⟨36710699371684195812084929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97895198324491188832226477 36710699371684195812084929)
          ·
            refine ⟨27533024528763146859063697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36710699371684195812084929 27533024528763146859063697)
            ·
              refine ⟨20649768396572360144297773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27533024528763146859063697 20649768396572360144297773)
              ·
                refine ⟨7743663148714635054111665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20649768396572360144297773 7743663148714635054111665)
                ·
                  refine ⟨5807747361535976290583749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7743663148714635054111665 5807747361535976290583749)
                  ·
                    refine ⟨1088952630287995554484453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5807747361535976290583749 1088952630287995554484453)
                    ·
                      rfl

theorem cell23_6362183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 3, 2, 4].length) (baseStart_6362183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6362183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6362183 prefixEnd_6362183 := by exact prefixLift 6362183
  have htrace : WordTrace (prefixWord ++ tailWord_6362183) baseStart_6362183 baseEnd_6362183 := by
    simpa [prefixWord, tailWord_6362183, baseEnd_6362183] using wordTrace_append hprefix tailTrace_6362183
  have hstable : (prefixWord ++ tailWord_6362183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6362183).length < 2 ^ (prefixWord ++ tailWord_6362183).sum := by decide
  have hdescent : baseEnd_6362183 < baseStart_6362183 := by decide
  rcases family_descends (prefixWord ++ tailWord_6362183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6362186 : List Nat := [3, 1, 2, 1, 1, 2, 3, 3, 1, 2, 4]
def baseStart_6362186 : Nat := 118140960795 + 6362186 * 2 ^ 59
def prefixEnd_6362186 : Nat := 4983230072969 + 3 ^ 40 * 6362186 * 2
def baseEnd_6362186 : Nat := 3266859431305950151715845

theorem tailTrace_6362186 : CollatzResearch.WordTrace tailWord_6362186 prefixEnd_6362186 3266859431305950151715845 := by
  unfold tailWord_6362186
  simp only [CollatzResearch.WordTrace]
  refine ⟨58011996732223542926816603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154698657952596114471510941 58011996732223542926816603)
  ·
    refine ⟨87017995098335314390224905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58011996732223542926816603 87017995098335314390224905)
    ·
      refine ⟨65263496323751485792668679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87017995098335314390224905 65263496323751485792668679)
      ·
        refine ⟨97895244485627228689003019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65263496323751485792668679 97895244485627228689003019)
        ·
          refine ⟨146842866728440843033504529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97895244485627228689003019 146842866728440843033504529)
          ·
            refine ⟨110132150046330632275128397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146842866728440843033504529 110132150046330632275128397)
            ·
              refine ⟨41299556267373987103173149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110132150046330632275128397 41299556267373987103173149)
              ·
                refine ⟨15487333600265245163689931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41299556267373987103173149 15487333600265245163689931)
                ·
                  refine ⟨23231000400397867745534897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15487333600265245163689931 23231000400397867745534897)
                  ·
                    refine ⟨17423250300298400809151173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23231000400397867745534897 17423250300298400809151173)
                    ·
                      refine ⟨3266859431305950151715845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17423250300298400809151173 3266859431305950151715845)
                      ·
                        rfl

theorem cell23_6362186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 3, 1, 2, 4].length) (baseStart_6362186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6362186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6362186 prefixEnd_6362186 := by exact prefixLift 6362186
  have htrace : WordTrace (prefixWord ++ tailWord_6362186) baseStart_6362186 baseEnd_6362186 := by
    simpa [prefixWord, tailWord_6362186, baseEnd_6362186] using wordTrace_append hprefix tailTrace_6362186
  have hstable : (prefixWord ++ tailWord_6362186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6362186).length < 2 ^ (prefixWord ++ tailWord_6362186).sum := by decide
  have hdescent : baseEnd_6362186 < baseStart_6362186 := by decide
  rcases family_descends (prefixWord ++ tailWord_6362186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6362190 : List Nat := [4, 1, 1, 1, 1, 3, 3, 2, 3, 2, 2]
def baseStart_6362190 : Nat := 118140960795 + 6362190 * 2 ^ 59
def prefixEnd_6362190 : Nat := 4983230072969 + 3 ^ 40 * 6362190 * 2
def baseEnd_6362190 : Nat := 3266861485228568136065827

theorem tailTrace_6362190 : CollatzResearch.WordTrace tailWord_6362190 prefixEnd_6362190 3266861485228568136065827 := by
  unfold tailWord_6362190
  simp only [CollatzResearch.WordTrace]
  refine ⟨29006016602609960048801503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154698755213919786926941349 29006016602609960048801503)
  ·
    refine ⟨43509024903914940073202255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29006016602609960048801503 43509024903914940073202255)
    ·
      refine ⟨65263537355872410109803383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43509024903914940073202255 65263537355872410109803383)
      ·
        refine ⟨97895306033808615164705075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65263537355872410109803383 97895306033808615164705075)
        ·
          refine ⟨146842959050712922747057613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97895306033808615164705075 146842959050712922747057613)
          ·
            refine ⟨55066109644017346030146605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 146842959050712922747057613 55066109644017346030146605)
            ·
              refine ⟨20649791116506504761304977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55066109644017346030146605 20649791116506504761304977)
              ·
                refine ⟨15487343337379878570978733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20649791116506504761304977 15487343337379878570978733)
                ·
                  refine ⟨5807753751517454464117025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15487343337379878570978733 5807753751517454464117025)
                  ·
                    refine ⟨4355815313638090848087769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5807753751517454464117025 4355815313638090848087769)
                    ·
                      refine ⟨3266861485228568136065827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4355815313638090848087769 3266861485228568136065827)
                      ·
                        rfl

theorem cell23_6362190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 2, 3, 2, 2].length) (baseStart_6362190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6362190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6362190 prefixEnd_6362190 := by exact prefixLift 6362190
  have htrace : WordTrace (prefixWord ++ tailWord_6362190) baseStart_6362190 baseEnd_6362190 := by
    simpa [prefixWord, tailWord_6362190, baseEnd_6362190] using wordTrace_append hprefix tailTrace_6362190
  have hstable : (prefixWord ++ tailWord_6362190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6362190).length < 2 ^ (prefixWord ++ tailWord_6362190).sum := by decide
  have hdescent : baseEnd_6362190 < baseStart_6362190 := by decide
  rcases family_descends (prefixWord ++ tailWord_6362190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6362207 : List Nat := [1, 1, 2, 3, 1, 1, 6, 3, 1, 2, 2]
def baseStart_6362207 : Nat := 118140960795 + 6362207 * 2 ^ 59
def prefixEnd_6362207 : Nat := 4983230072969 + 3 ^ 40 * 6362207 * 2
def baseEnd_6362207 : Nat := 3266870214399694569553249

theorem tailTrace_6362207 : CollatzResearch.WordTrace tailWord_6362207 prefixEnd_6362207 3266870214399694569553249 := by
  unfold tailWord_6362207
  simp only [CollatzResearch.WordTrace]
  refine ⟨232048752861818092293780875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154699168574545394862520583 232048752861818092293780875)
  ·
    refine ⟨348073129292727138440671313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232048752861818092293780875 348073129292727138440671313)
    ·
      refine ⟨261054846969545353830503485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 348073129292727138440671313 261054846969545353830503485)
      ·
        refine ⟨97895567613579507686438807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 261054846969545353830503485 97895567613579507686438807)
        ·
          refine ⟨146843351420369261529658211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97895567613579507686438807 146843351420369261529658211)
          ·
            refine ⟨220265027130553892294487317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146843351420369261529658211 220265027130553892294487317)
            ·
              refine ⟨10324923146744713701304093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 220265027130553892294487317 10324923146744713701304093)
              ·
                refine ⟨3871846180029267637989035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10324923146744713701304093 3871846180029267637989035)
                ·
                  refine ⟨5807769270043901456983553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3871846180029267637989035 5807769270043901456983553)
                  ·
                    refine ⟨4355826952532926092737665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5807769270043901456983553 4355826952532926092737665)
                    ·
                      refine ⟨3266870214399694569553249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4355826952532926092737665 3266870214399694569553249)
                      ·
                        rfl

theorem cell23_6362207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 3, 1, 2, 2].length) (baseStart_6362207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6362207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6362207 prefixEnd_6362207 := by exact prefixLift 6362207
  have htrace : WordTrace (prefixWord ++ tailWord_6362207) baseStart_6362207 baseEnd_6362207 := by
    simpa [prefixWord, tailWord_6362207, baseEnd_6362207] using wordTrace_append hprefix tailTrace_6362207
  have hstable : (prefixWord ++ tailWord_6362207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6362207).length < 2 ^ (prefixWord ++ tailWord_6362207).sum := by decide
  have hdescent : baseEnd_6362207 < baseStart_6362207 := by decide
  rcases family_descends (prefixWord ++ tailWord_6362207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6362223 : List Nat := [1, 1, 2, 1, 3, 3, 3, 1, 4, 1, 3]
def baseStart_6362223 : Nat := 118140960795 + 6362223 * 2 ^ 59
def prefixEnd_6362223 : Nat := 4983230072969 + 3 ^ 40 * 6362223 * 2
def baseEnd_6362223 : Nat := 3266878430090166506953175

theorem tailTrace_6362223 : CollatzResearch.WordTrace tailWord_6362223 prefixEnd_6362223 3266878430090166506953175 := by
  unfold tailWord_6362223
  simp only [CollatzResearch.WordTrace]
  refine ⟨232049336429760127026363323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154699557619840084684242215 232049336429760127026363323)
  ·
    refine ⟨348074004644640190539544985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232049336429760127026363323 348074004644640190539544985)
    ·
      refine ⟨261055503483480142904658739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 348074004644640190539544985 261055503483480142904658739)
      ·
        refine ⟨391583255225220214356988109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261055503483480142904658739 391583255225220214356988109)
        ·
          refine ⟨146843720709457580383870541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 391583255225220214356988109 146843720709457580383870541)
          ·
            refine ⟨55066395266046592643951453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 146843720709457580383870541 55066395266046592643951453)
            ·
              refine ⟨20649898224767472241481795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55066395266046592643951453 20649898224767472241481795)
              ·
                refine ⟨30974847337151208362222693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20649898224767472241481795 30974847337151208362222693)
                ·
                  refine ⟨5807783875715851567916755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30974847337151208362222693 5807783875715851567916755)
                  ·
                    refine ⟨8711675813573777351875133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5807783875715851567916755 8711675813573777351875133)
                    ·
                      refine ⟨3266878430090166506953175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8711675813573777351875133 3266878430090166506953175)
                      ·
                        rfl

theorem cell23_6362223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 1, 4, 1, 3].length) (baseStart_6362223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6362223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6362223 prefixEnd_6362223 := by exact prefixLift 6362223
  have htrace : WordTrace (prefixWord ++ tailWord_6362223) baseStart_6362223 baseEnd_6362223 := by
    simpa [prefixWord, tailWord_6362223, baseEnd_6362223] using wordTrace_append hprefix tailTrace_6362223
  have hstable : (prefixWord ++ tailWord_6362223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6362223).length < 2 ^ (prefixWord ++ tailWord_6362223).sum := by decide
  have hdescent : baseEnd_6362223 < baseStart_6362223 := by decide
  rcases family_descends (prefixWord ++ tailWord_6362223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6362297 : List Nat := [1, 2, 1, 4, 1, 4, 1, 3, 2, 2, 2]
def baseStart_6362297 : Nat := 118140960795 + 6362297 * 2 ^ 59
def prefixEnd_6362297 : Nat := 4983230072969 + 3 ^ 40 * 6362297 * 2
def baseEnd_6362297 : Nat := 3266916427658599217427835

theorem tailTrace_6362297 : CollatzResearch.WordTrace tailWord_6362297 prefixEnd_6362297 3266916427658599217427835 := by
  unfold tailWord_6362297
  simp only [CollatzResearch.WordTrace]
  refine ⟨232052035431492037664557145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154701356954328025109704763 232052035431492037664557145)
  ·
    refine ⟨174039026573619028248417859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232052035431492037664557145 174039026573619028248417859)
    ·
      refine ⟨261058539860428542372626789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174039026573619028248417859 261058539860428542372626789)
      ·
        refine ⟨48948476223830351694867523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 261058539860428542372626789 48948476223830351694867523)
        ·
          refine ⟨73422714335745527542301285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48948476223830351694867523 73422714335745527542301285)
          ·
            refine ⟨13766758937952286414181491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73422714335745527542301285 13766758937952286414181491)
            ·
              refine ⟨20650138406928429621272237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13766758937952286414181491 20650138406928429621272237)
              ·
                refine ⟨7743801902598161107977089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20650138406928429621272237 7743801902598161107977089)
                ·
                  refine ⟨5807851426948620830982817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7743801902598161107977089 5807851426948620830982817)
                  ·
                    refine ⟨4355888570211465623237113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5807851426948620830982817 4355888570211465623237113)
                    ·
                      refine ⟨3266916427658599217427835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4355888570211465623237113 3266916427658599217427835)
                      ·
                        rfl

theorem cell23_6362297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 3, 2, 2, 2].length) (baseStart_6362297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6362297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6362297 prefixEnd_6362297 := by exact prefixLift 6362297
  have htrace : WordTrace (prefixWord ++ tailWord_6362297) baseStart_6362297 baseEnd_6362297 := by
    simpa [prefixWord, tailWord_6362297, baseEnd_6362297] using wordTrace_append hprefix tailTrace_6362297
  have hstable : (prefixWord ++ tailWord_6362297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6362297).length < 2 ^ (prefixWord ++ tailWord_6362297).sum := by decide
  have hdescent : baseEnd_6362297 < baseStart_6362297 := by decide
  rcases family_descends (prefixWord ++ tailWord_6362297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6362337 : List Nat := [1, 2, 3, 1, 3, 4, 2, 2, 5]
def baseStart_6362337 : Nat := 118140960795 + 6362337 * 2 ^ 59
def prefixEnd_6362337 : Nat := 4983230072969 + 3 ^ 40 * 6362337 * 2
def baseEnd_6362337 : Nat := 362992996320531006769739

theorem tailTrace_6362337 : CollatzResearch.WordTrace tailWord_6362337 prefixEnd_6362337 362992996320531006769739 := by
  unfold tailWord_6362337
  simp only [CollatzResearch.WordTrace]
  refine ⟨232053494351347124496013265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154702329567564749664008843 232053494351347124496013265)
  ·
    refine ⟨174040120763510343372009949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232053494351347124496013265 174040120763510343372009949)
    ·
      refine ⟨65265045286316378764503731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174040120763510343372009949 65265045286316378764503731)
      ·
        refine ⟨97897567929474568146755597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65265045286316378764503731 97897567929474568146755597)
        ·
          refine ⟨36711587973552963055033349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97897567929474568146755597 36711587973552963055033349)
          ·
            refine ⟨6883422745041180572818753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36711587973552963055033349 6883422745041180572818753)
            ·
              refine ⟨5162567058780885429614065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6883422745041180572818753 5162567058780885429614065)
              ·
                refine ⟨3871925294085664072210549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5162567058780885429614065 3871925294085664072210549)
                ·
                  refine ⟨362992996320531006769739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3871925294085664072210549 362992996320531006769739)
                  ·
                    rfl

theorem cell23_6362337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 2, 2, 5].length) (baseStart_6362337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6362337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6362337 prefixEnd_6362337 := by exact prefixLift 6362337
  have htrace : WordTrace (prefixWord ++ tailWord_6362337) baseStart_6362337 baseEnd_6362337 := by
    simpa [prefixWord, tailWord_6362337, baseEnd_6362337] using wordTrace_append hprefix tailTrace_6362337
  have hstable : (prefixWord ++ tailWord_6362337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6362337).length < 2 ^ (prefixWord ++ tailWord_6362337).sum := by decide
  have hdescent : baseEnd_6362337 < baseStart_6362337 := by decide
  rcases family_descends (prefixWord ++ tailWord_6362337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6362373 : List Nat := [1, 3, 1, 1, 2, 1, 5, 1, 1, 4, 3]
def baseStart_6362373 : Nat := 118140960795 + 6362373 * 2 ^ 59
def prefixEnd_6362373 : Nat := 4983230072969 + 3 ^ 40 * 6362373 * 2
def baseEnd_6362373 : Nat := 3266955452188340920077485

theorem tailTrace_6362373 : CollatzResearch.WordTrace tailWord_6362373 prefixEnd_6362373 3266955452188340920077485 := by
  unfold tailWord_6362373
  simp only [CollatzResearch.WordTrace]
  refine ⟨232054807379216702644323773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154703204919477801762882515 232054807379216702644323773)
  ·
    refine ⟨87020552767206263491621415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 232054807379216702644323773 87020552767206263491621415)
    ·
      refine ⟨130530829150809395237432123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87020552767206263491621415 130530829150809395237432123)
      ·
        refine ⟨195796243726214092856148185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130530829150809395237432123 195796243726214092856148185)
        ·
          refine ⟨146847182794660569642111139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 195796243726214092856148185 146847182794660569642111139)
          ·
            refine ⟨220270774191990854463166709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146847182794660569642111139 220270774191990854463166709)
            ·
              refine ⟨20650385080499142605921879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 220270774191990854463166709 20650385080499142605921879)
              ·
                refine ⟨30975577620748713908882819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20650385080499142605921879 30975577620748713908882819)
                ·
                  refine ⟨46463366431123070863324229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30975577620748713908882819 46463366431123070863324229)
                  ·
                    refine ⟨8711881205835575786873293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46463366431123070863324229 8711881205835575786873293)
                    ·
                      refine ⟨3266955452188340920077485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8711881205835575786873293 3266955452188340920077485)
                      ·
                        rfl

theorem cell23_6362373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 1, 1, 4, 3].length) (baseStart_6362373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6362373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6362373 prefixEnd_6362373 := by exact prefixLift 6362373
  have htrace : WordTrace (prefixWord ++ tailWord_6362373) baseStart_6362373 baseEnd_6362373 := by
    simpa [prefixWord, tailWord_6362373, baseEnd_6362373] using wordTrace_append hprefix tailTrace_6362373
  have hstable : (prefixWord ++ tailWord_6362373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6362373).length < 2 ^ (prefixWord ++ tailWord_6362373).sum := by decide
  have hdescent : baseEnd_6362373 < baseStart_6362373 := by decide
  rcases family_descends (prefixWord ++ tailWord_6362373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6362397 : List Nat := [1, 4, 2, 3, 1, 2, 2, 1, 3, 4]
def baseStart_6362397 : Nat := 118140960795 + 6362397 * 2 ^ 59
def prefixEnd_6362397 : Nat := 4983230072969 + 3 ^ 40 * 6362397 * 2
def baseEnd_6362397 : Nat := 1088989258574682942059125

theorem tailTrace_6362397 : CollatzResearch.WordTrace tailWord_6362397 prefixEnd_6362397 1088989258574682942059125 := by
  unfold tailWord_6362397
  simp only [CollatzResearch.WordTrace]
  refine ⟨232055682731129754743197445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154703788487419836495464963 232055682731129754743197445)
  ·
    refine ⟨43510440512086829014349521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 232055682731129754743197445 43510440512086829014349521)
    ·
      refine ⟨32632830384065121760762141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43510440512086829014349521 32632830384065121760762141)
      ·
        refine ⟨12237311394024420660285803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32632830384065121760762141 12237311394024420660285803)
        ·
          refine ⟨18355967091036630990428705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12237311394024420660285803 18355967091036630990428705)
          ·
            refine ⟨13766975318277473242821529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18355967091036630990428705 13766975318277473242821529)
            ·
              refine ⟨10325231488708104932116147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13766975318277473242821529 10325231488708104932116147)
              ·
                refine ⟨15487847233062157398174221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10325231488708104932116147 15487847233062157398174221)
                ·
                  refine ⟨5807942712398309024315333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15487847233062157398174221 5807942712398309024315333)
                  ·
                    refine ⟨1088989258574682942059125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5807942712398309024315333 1088989258574682942059125)
                    ·
                      rfl

theorem cell23_6362397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 1, 3, 4].length) (baseStart_6362397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6362397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6362397 prefixEnd_6362397 := by exact prefixLift 6362397
  have htrace : WordTrace (prefixWord ++ tailWord_6362397) baseStart_6362397 baseEnd_6362397 := by
    simpa [prefixWord, tailWord_6362397, baseEnd_6362397] using wordTrace_append hprefix tailTrace_6362397
  have hstable : (prefixWord ++ tailWord_6362397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6362397).length < 2 ^ (prefixWord ++ tailWord_6362397).sum := by decide
  have hdescent : baseEnd_6362397 < baseStart_6362397 := by decide
  rcases family_descends (prefixWord ++ tailWord_6362397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6362420 : List Nat := [2, 5, 1, 1, 1, 1, 1, 1, 2, 5, 3]
def baseStart_6362420 : Nat := 118140960795 + 6362420 * 2 ^ 59
def prefixEnd_6362420 : Nat := 4983230072969 + 3 ^ 40 * 6362420 * 2
def baseEnd_6362420 : Nat := 3266979585779102236189769

theorem tailTrace_6362420 : CollatzResearch.WordTrace tailWord_6362420 prefixEnd_6362420 3266979585779102236189769 := by
  unfold tailWord_6362420
  simp only [CollatzResearch.WordTrace]
  refine ⟨116028260805023214835642357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154704347740030953114189809 116028260805023214835642357)
  ·
    refine ⟨10877649450470926390841471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 116028260805023214835642357 10877649450470926390841471)
    ·
      refine ⟨16316474175706389586262207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10877649450470926390841471 16316474175706389586262207)
      ·
        refine ⟨24474711263559584379393311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16316474175706389586262207 24474711263559584379393311)
        ·
          refine ⟨36712066895339376569089967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24474711263559584379393311 36712066895339376569089967)
          ·
            refine ⟨55068100343009064853634951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36712066895339376569089967 55068100343009064853634951)
            ·
              refine ⟨82602150514513597280452427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55068100343009064853634951 82602150514513597280452427)
              ·
                refine ⟨123903225771770395920678641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82602150514513597280452427 123903225771770395920678641)
                ·
                  refine ⟨92927419328827796940508981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 123903225771770395920678641 92927419328827796940508981)
                  ·
                    refine ⟨8711945562077605963172717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 92927419328827796940508981 8711945562077605963172717)
                    ·
                      refine ⟨3266979585779102236189769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8711945562077605963172717 3266979585779102236189769)
                      ·
                        rfl

theorem cell23_6362420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 2, 5, 3].length) (baseStart_6362420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6362420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6362420 prefixEnd_6362420 := by exact prefixLift 6362420
  have htrace : WordTrace (prefixWord ++ tailWord_6362420) baseStart_6362420 baseEnd_6362420 := by
    simpa [prefixWord, tailWord_6362420, baseEnd_6362420] using wordTrace_append hprefix tailTrace_6362420
  have hstable : (prefixWord ++ tailWord_6362420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6362420).length < 2 ^ (prefixWord ++ tailWord_6362420).sum := by decide
  have hdescent : baseEnd_6362420 < baseStart_6362420 := by decide
  rcases family_descends (prefixWord ++ tailWord_6362420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6362463 : List Nat := [1, 1, 2, 3, 1, 2, 1, 1, 2, 6, 3]
def baseStart_6362463 : Nat := 118140960795 + 6362463 * 2 ^ 59
def prefixEnd_6362463 : Nat := 4983230072969 + 3 ^ 40 * 6362463 * 2
def baseEnd_6362463 : Nat := 3267001665447245567952071

theorem tailTrace_6362463 : CollatzResearch.WordTrace tailWord_6362463 prefixEnd_6362463 3267001665447245567952071 := by
  unfold tailWord_6362463
  simp only [CollatzResearch.WordTrace]
  refine ⟨232058089948890648015100043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154705393299260432010066695 232058089948890648015100043)
  ·
    refine ⟨348087134923335972022650065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232058089948890648015100043 348087134923335972022650065)
    ·
      refine ⟨261065351192501979016987549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 348087134923335972022650065 261065351192501979016987549)
      ·
        refine ⟨97899506697188242131370331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 261065351192501979016987549 97899506697188242131370331)
        ·
          refine ⟨146849260045782363197055497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97899506697188242131370331 146849260045782363197055497)
          ·
            refine ⟨110136945034336772397791623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146849260045782363197055497 110136945034336772397791623)
            ·
              refine ⟨165205417551505158596687435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110136945034336772397791623 165205417551505158596687435)
              ·
                refine ⟨247808126327257737895031153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 165205417551505158596687435 247808126327257737895031153)
                ·
                  refine ⟨185856094745443303421273365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 247808126327257737895031153 185856094745443303421273365)
                  ·
                    refine ⟨8712004441192654847872189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 185856094745443303421273365 8712004441192654847872189)
                    ·
                      refine ⟨3267001665447245567952071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8712004441192654847872189 3267001665447245567952071)
                      ·
                        rfl

theorem cell23_6362463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 6, 3].length) (baseStart_6362463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6362463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6362463 prefixEnd_6362463 := by exact prefixLift 6362463
  have htrace : WordTrace (prefixWord ++ tailWord_6362463) baseStart_6362463 baseEnd_6362463 := by
    simpa [prefixWord, tailWord_6362463, baseEnd_6362463] using wordTrace_append hprefix tailTrace_6362463
  have hstable : (prefixWord ++ tailWord_6362463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6362463).length < 2 ^ (prefixWord ++ tailWord_6362463).sum := by decide
  have hdescent : baseEnd_6362463 < baseStart_6362463 := by decide
  rcases family_descends (prefixWord ++ tailWord_6362463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6362474 : List Nat := [3, 1, 3, 3, 2, 2, 1, 2, 1, 5]
def baseStart_6362474 : Nat := 118140960795 + 6362474 * 2 ^ 59
def prefixEnd_6362474 : Nat := 4983230072969 + 3 ^ 40 * 6362474 * 2
def baseEnd_6362474 : Nat := 1089002437911481674971507

theorem tailTrace_6362474 : CollatzResearch.WordTrace tailWord_6362474 prefixEnd_6362474 1089002437911481674971507 := by
  unfold tailWord_6362474
  simp only [CollatzResearch.WordTrace]
  refine ⟨58014622787962699223437619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154705660767900531262500317 58014622787962699223437619)
  ·
    refine ⟨87021934181944048835156429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58014622787962699223437619 87021934181944048835156429)
    ·
      refine ⟨32633225318229018313183661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87021934181944048835156429 32633225318229018313183661)
      ·
        refine ⟨12237459494335881867443873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32633225318229018313183661 12237459494335881867443873)
        ·
          refine ⟨9178094620751911400582905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12237459494335881867443873 9178094620751911400582905)
          ·
            refine ⟨6883570965563933550437179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9178094620751911400582905 6883570965563933550437179)
            ·
              refine ⟨10325356448345900325655769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6883570965563933550437179 10325356448345900325655769)
              ·
                refine ⟨7744017336259425244241827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10325356448345900325655769 7744017336259425244241827)
                ·
                  refine ⟨11616026004389137866362741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7744017336259425244241827 11616026004389137866362741)
                  ·
                    refine ⟨1089002437911481674971507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11616026004389137866362741 1089002437911481674971507)
                    ·
                      rfl

theorem cell23_6362474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 2, 1, 5].length) (baseStart_6362474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6362474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6362474 prefixEnd_6362474 := by exact prefixLift 6362474
  have htrace : WordTrace (prefixWord ++ tailWord_6362474) baseStart_6362474 baseEnd_6362474 := by
    simpa [prefixWord, tailWord_6362474, baseEnd_6362474] using wordTrace_append hprefix tailTrace_6362474
  have hstable : (prefixWord ++ tailWord_6362474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6362474).length < 2 ^ (prefixWord ++ tailWord_6362474).sum := by decide
  have hdescent : baseEnd_6362474 < baseStart_6362474 := by decide
  rcases family_descends (prefixWord ++ tailWord_6362474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6362477 : List Nat := [1, 5, 1, 1, 1, 3, 3, 2, 1, 1, 4]
def baseStart_6362477 : Nat := 118140960795 + 6362477 * 2 ^ 59
def prefixEnd_6362477 : Nat := 4983230072969 + 3 ^ 40 * 6362477 * 2
def baseEnd_6362477 : Nat := 3267008854176408513177007

theorem tailTrace_6362477 : CollatzResearch.WordTrace tailWord_6362477 prefixEnd_6362477 3267008854176408513177007 := by
  unfold tailWord_6362477
  simp only [CollatzResearch.WordTrace]
  refine ⟨232058600570839928406109685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154705733713893285604073123 232058600570839928406109685)
  ·
    refine ⟨21755493803516243288072783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 232058600570839928406109685 21755493803516243288072783)
    ·
      refine ⟨32633240705274364932109175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21755493803516243288072783 32633240705274364932109175)
      ·
        refine ⟨48949861057911547398163763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32633240705274364932109175 48949861057911547398163763)
        ·
          refine ⟨73424791586867321097245645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48949861057911547398163763 73424791586867321097245645)
          ·
            refine ⟨27534296845075245411467117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73424791586867321097245645 27534296845075245411467117)
            ·
              refine ⟨10325361316903217029300169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27534296845075245411467117 10325361316903217029300169)
              ·
                refine ⟨7744020987677412771975127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10325361316903217029300169 7744020987677412771975127)
                ·
                  refine ⟨11616031481516119157962691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7744020987677412771975127 11616031481516119157962691)
                  ·
                    refine ⟨17424047222274178736944037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11616031481516119157962691 17424047222274178736944037)
                    ·
                      refine ⟨3267008854176408513177007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17424047222274178736944037 3267008854176408513177007)
                      ·
                        rfl

theorem cell23_6362477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 2, 1, 1, 4].length) (baseStart_6362477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6362477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6362477 prefixEnd_6362477 := by exact prefixLift 6362477
  have htrace : WordTrace (prefixWord ++ tailWord_6362477) baseStart_6362477 baseEnd_6362477 := by
    simpa [prefixWord, tailWord_6362477, baseEnd_6362477] using wordTrace_append hprefix tailTrace_6362477
  have hstable : (prefixWord ++ tailWord_6362477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6362477).length < 2 ^ (prefixWord ++ tailWord_6362477).sum := by decide
  have hdescent : baseEnd_6362477 < baseStart_6362477 := by decide
  rcases family_descends (prefixWord ++ tailWord_6362477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6362480 : List Nat := [2, 1, 1, 1, 4, 2, 3, 1, 3, 2, 3]
def baseStart_6362480 : Nat := 118140960795 + 6362480 * 2 ^ 59
def prefixEnd_6362480 : Nat := 4983230072969 + 3 ^ 40 * 6362480 * 2
def baseEnd_6362480 : Nat := 3267010394618372001439493

theorem tailTrace_6362480 : CollatzResearch.WordTrace tailWord_6362480 prefixEnd_6362480 3267010394618372001439493 := by
  unfold tailWord_6362480
  simp only [CollatzResearch.WordTrace]
  refine ⟨116029354994914529959234447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154705806659886039945645929 116029354994914529959234447)
  ·
    refine ⟨174044032492371794938851671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116029354994914529959234447 174044032492371794938851671)
    ·
      refine ⟨261066048738557692408277507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174044032492371794938851671 261066048738557692408277507)
      ·
        refine ⟨391599073107836538612416261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261066048738557692408277507 391599073107836538612416261)
        ·
          refine ⟨73424826207719350989828049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 391599073107836538612416261 73424826207719350989828049)
          ·
            refine ⟨55068619655789513242371037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73424826207719350989828049 55068619655789513242371037)
            ·
              refine ⟨20650732370921067465889139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55068619655789513242371037 20650732370921067465889139)
              ·
                refine ⟨30976098556381601198833709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20650732370921067465889139 30976098556381601198833709)
                ·
                  refine ⟨11616036958643100449562641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30976098556381601198833709 11616036958643100449562641)
                  ·
                    refine ⟨8712027718982325337171981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11616036958643100449562641 8712027718982325337171981)
                    ·
                      refine ⟨3267010394618372001439493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8712027718982325337171981 3267010394618372001439493)
                      ·
                        rfl

theorem cell23_6362480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 1, 3, 2, 3].length) (baseStart_6362480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6362480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6362480 prefixEnd_6362480 := by exact prefixLift 6362480
  have htrace : WordTrace (prefixWord ++ tailWord_6362480) baseStart_6362480 baseEnd_6362480 := by
    simpa [prefixWord, tailWord_6362480, baseEnd_6362480] using wordTrace_append hprefix tailTrace_6362480
  have hstable : (prefixWord ++ tailWord_6362480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6362480).length < 2 ^ (prefixWord ++ tailWord_6362480).sum := by decide
  have hdescent : baseEnd_6362480 < baseStart_6362480 := by decide
  rcases family_descends (prefixWord ++ tailWord_6362480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6362524 : List Nat := [2, 2, 3, 4, 1, 1, 2, 1, 1, 2, 4]
def baseStart_6362524 : Nat := 118140960795 + 6362524 * 2 ^ 59
def prefixEnd_6362524 : Nat := 4983230072969 + 3 ^ 40 * 6362524 * 2
def baseEnd_6362524 : Nat := 3267032987767169829289291

theorem tailTrace_6362524 : CollatzResearch.WordTrace tailWord_6362524 prefixEnd_6362524 3267032987767169829289291 := by
  unfold tailWord_6362524
  simp only [CollatzResearch.WordTrace]
  refine ⟨116030157400834827716535313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154706876534446436955380417 116030157400834827716535313)
  ·
    refine ⟨87022618050626120787401485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116030157400834827716535313 87022618050626120787401485)
    ·
      refine ⟨32633481768984795295275557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87022618050626120787401485 32633481768984795295275557)
      ·
        refine ⟨6118777831684649117864167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32633481768984795295275557 6118777831684649117864167)
        ·
          refine ⟨9178166747526973676796251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6118777831684649117864167 9178166747526973676796251)
          ·
            refine ⟨13767250121290460515194377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9178166747526973676796251 13767250121290460515194377)
            ·
              refine ⟨10325437590967845386395783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13767250121290460515194377 10325437590967845386395783)
              ·
                refine ⟨15488156386451768079593675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10325437590967845386395783 15488156386451768079593675)
                ·
                  refine ⟨23232234579677652119390513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15488156386451768079593675 23232234579677652119390513)
                  ·
                    refine ⟨17424175934758239089542885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23232234579677652119390513 17424175934758239089542885)
                    ·
                      refine ⟨3267032987767169829289291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17424175934758239089542885 3267032987767169829289291)
                      ·
                        rfl

theorem cell23_6362524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_6362524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6362524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6362524 prefixEnd_6362524 := by exact prefixLift 6362524
  have htrace : WordTrace (prefixWord ++ tailWord_6362524) baseStart_6362524 baseEnd_6362524 := by
    simpa [prefixWord, tailWord_6362524, baseEnd_6362524] using wordTrace_append hprefix tailTrace_6362524
  have hstable : (prefixWord ++ tailWord_6362524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6362524).length < 2 ^ (prefixWord ++ tailWord_6362524).sum := by decide
  have hdescent : baseEnd_6362524 < baseStart_6362524 := by decide
  rcases family_descends (prefixWord ++ tailWord_6362524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6362527 : List Nat := [1, 1, 2, 5, 1, 3, 2, 1, 1, 3, 3]
def baseStart_6362527 : Nat := 118140960795 + 6362527 * 2 ^ 59
def prefixEnd_6362527 : Nat := 4983230072969 + 3 ^ 40 * 6362527 * 2
def baseEnd_6362527 : Nat := 3267034528209133317551777

theorem tailTrace_6362527 : CollatzResearch.WordTrace tailWord_6362527 prefixEnd_6362527 3267034528209133317551777 := by
  unfold tailWord_6362527
  simp only [CollatzResearch.WordTrace]
  refine ⟨232060424220658786945429835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154706949480439191296953223 232060424220658786945429835)
  ·
    refine ⟨348090636330988180418144753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232060424220658786945429835 348090636330988180418144753)
    ·
      refine ⟨261067977248241135313608565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 348090636330988180418144753 261067977248241135313608565)
      ·
        refine ⟨24475122867022606435650803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 261067977248241135313608565 24475122867022606435650803)
        ·
          refine ⟨36712684300533909653476205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24475122867022606435650803 36712684300533909653476205)
          ·
            refine ⟨13767256612700216120053577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36712684300533909653476205 13767256612700216120053577)
            ·
              refine ⟨10325442459525162090040183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13767256612700216120053577 10325442459525162090040183)
              ·
                refine ⟨15488163689287743135060275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10325442459525162090040183 15488163689287743135060275)
                ·
                  refine ⟨23232245533931614702590413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15488163689287743135060275 23232245533931614702590413)
                  ·
                    refine ⟨8712092075224355513471405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23232245533931614702590413 8712092075224355513471405)
                    ·
                      refine ⟨3267034528209133317551777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8712092075224355513471405 3267034528209133317551777)
                      ·
                        rfl

theorem cell23_6362527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 1, 1, 3, 3].length) (baseStart_6362527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6362527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6362527 prefixEnd_6362527 := by exact prefixLift 6362527
  have htrace : WordTrace (prefixWord ++ tailWord_6362527) baseStart_6362527 baseEnd_6362527 := by
    simpa [prefixWord, tailWord_6362527, baseEnd_6362527] using wordTrace_append hprefix tailTrace_6362527
  have hstable : (prefixWord ++ tailWord_6362527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6362527).length < 2 ^ (prefixWord ++ tailWord_6362527).sum := by decide
  have hdescent : baseEnd_6362527 < baseStart_6362527 := by decide
  rcases family_descends (prefixWord ++ tailWord_6362527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6362562 : List Nat := [3, 5, 2, 1, 1, 1, 2, 1, 3, 2, 2]
def baseStart_6362562 : Nat := 118140960795 + 6362562 * 2 ^ 59
def prefixEnd_6362562 : Nat := 4983230072969 + 3 ^ 40 * 6362562 * 2
def baseEnd_6362562 : Nat := 3267052500032040680614117

theorem tailTrace_6362562 : CollatzResearch.WordTrace tailWord_6362562 prefixEnd_6362562 3267052500032040680614117 := by
  unfold tailWord_6362562
  simp only [CollatzResearch.WordTrace]
  refine ⟨58015425193882996980738485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154707800517021325281969293 58015425193882996980738485)
  ·
    refine ⟨5438946111926530966944233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58015425193882996980738485 5438946111926530966944233)
    ·
      refine ⟨4079209583944898225208175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5438946111926530966944233 4079209583944898225208175)
      ·
        refine ⟨6118814375917347337812263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4079209583944898225208175 6118814375917347337812263)
        ·
          refine ⟨9178221563876021006718395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6118814375917347337812263 9178221563876021006718395)
          ·
            refine ⟨13767332345814031510077593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9178221563876021006718395 13767332345814031510077593)
            ·
              refine ⟨10325499259360523632558195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13767332345814031510077593 10325499259360523632558195)
              ·
                refine ⟨15488248889040785448837293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10325499259360523632558195 15488248889040785448837293)
                ·
                  refine ⟨5808093333390294543313985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15488248889040785448837293 5808093333390294543313985)
                  ·
                    refine ⟨4356070000042720907485489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5808093333390294543313985 4356070000042720907485489)
                    ·
                      refine ⟨3267052500032040680614117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4356070000042720907485489 3267052500032040680614117)
                      ·
                        rfl

theorem cell23_6362562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_6362562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6362562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6362562 prefixEnd_6362562 := by exact prefixLift 6362562
  have htrace : WordTrace (prefixWord ++ tailWord_6362562) baseStart_6362562 baseEnd_6362562 := by
    simpa [prefixWord, tailWord_6362562, baseEnd_6362562] using wordTrace_append hprefix tailTrace_6362562
  have hstable : (prefixWord ++ tailWord_6362562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6362562).length < 2 ^ (prefixWord ++ tailWord_6362562).sum := by decide
  have hdescent : baseEnd_6362562 < baseStart_6362562 := by decide
  rcases family_descends (prefixWord ++ tailWord_6362562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6362583 : List Nat := [1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 9]
def baseStart_6362583 : Nat := 118140960795 + 6362583 * 2 ^ 59
def prefixEnd_6362583 : Nat := 4983230072969 + 3 ^ 40 * 6362583 * 2
def baseEnd_6362583 : Nat := 3267063283125785098451519

theorem tailTrace_6362583 : CollatzResearch.WordTrace tailWord_6362583 prefixEnd_6362583 3267063283125785098451519 := by
  unfold tailWord_6362583
  simp only [CollatzResearch.WordTrace]
  refine ⟨232062466708455908509468403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154708311138970605672978935 232062466708455908509468403)
  ·
    refine ⟨348093700062683862764202605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232062466708455908509468403 348093700062683862764202605)
    ·
      refine ⟨130535137523506448536575977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 348093700062683862764202605 130535137523506448536575977)
      ·
        refine ⟨97901353142629836402431983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130535137523506448536575977 97901353142629836402431983)
        ·
          refine ⟨146852029713944754603647975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97901353142629836402431983 146852029713944754603647975)
          ·
            refine ⟨220278044570917131905471963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146852029713944754603647975 220278044570917131905471963)
            ·
              refine ⟨330417066856375697858207945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 220278044570917131905471963 330417066856375697858207945)
              ·
                refine ⟨247812800142281773393655959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 330417066856375697858207945 247812800142281773393655959)
                ·
                  refine ⟨371719200213422660090483939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 247812800142281773393655959 371719200213422660090483939)
                  ·
                    refine ⟨557578800320133990135725909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 371719200213422660090483939 557578800320133990135725909)
                    ·
                      refine ⟨3267063283125785098451519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 557578800320133990135725909 3267063283125785098451519)
                      ·
                        rfl

theorem cell23_6362583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 9].length) (baseStart_6362583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6362583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6362583 prefixEnd_6362583 := by exact prefixLift 6362583
  have htrace : WordTrace (prefixWord ++ tailWord_6362583) baseStart_6362583 baseEnd_6362583 := by
    simpa [prefixWord, tailWord_6362583, baseEnd_6362583] using wordTrace_append hprefix tailTrace_6362583
  have hstable : (prefixWord ++ tailWord_6362583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6362583).length < 2 ^ (prefixWord ++ tailWord_6362583).sum := by decide
  have hdescent : baseEnd_6362583 < baseStart_6362583 := by decide
  rcases family_descends (prefixWord ++ tailWord_6362583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6362584 : List Nat := [2, 1, 2, 2, 2, 1, 2, 5, 2, 2, 2]
def baseStart_6362584 : Nat := 118140960795 + 6362584 * 2 ^ 59
def prefixEnd_6362584 : Nat := 4983230072969 + 3 ^ 40 * 6362584 * 2
def baseEnd_6362584 : Nat := 3267063796606439594539015

theorem tailTrace_6362584 : CollatzResearch.WordTrace tailWord_6362584 prefixEnd_6362584 3267063796606439594539015 := by
  unfold tailWord_6362584
  simp only [CollatzResearch.WordTrace]
  refine ⟨116031251590726142840127403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154708335454301523786836537 116031251590726142840127403)
  ·
    refine ⟨174046877386089214260191105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116031251590726142840127403 174046877386089214260191105)
    ·
      refine ⟨130535158039566910695143329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174046877386089214260191105 130535158039566910695143329)
      ·
        refine ⟨97901368529675183021357497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130535158039566910695143329 97901368529675183021357497)
        ·
          refine ⟨73426026397256387266018123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97901368529675183021357497 73426026397256387266018123)
          ·
            refine ⟨110139039595884580899027185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73426026397256387266018123 110139039595884580899027185)
            ·
              refine ⟨82604279696913435674270389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110139039595884580899027185 82604279696913435674270389)
              ·
                refine ⟨7744151221585634594462849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 82604279696913435674270389 7744151221585634594462849)
                ·
                  refine ⟨5808113416189225945847137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7744151221585634594462849 5808113416189225945847137)
                  ·
                    refine ⟨4356085062141919459385353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5808113416189225945847137 4356085062141919459385353)
                    ·
                      refine ⟨3267063796606439594539015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4356085062141919459385353 3267063796606439594539015)
                      ·
                        rfl

theorem cell23_6362584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 5, 2, 2, 2].length) (baseStart_6362584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6362584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6362584 prefixEnd_6362584 := by exact prefixLift 6362584
  have htrace : WordTrace (prefixWord ++ tailWord_6362584) baseStart_6362584 baseEnd_6362584 := by
    simpa [prefixWord, tailWord_6362584, baseEnd_6362584] using wordTrace_append hprefix tailTrace_6362584
  have hstable : (prefixWord ++ tailWord_6362584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6362584).length < 2 ^ (prefixWord ++ tailWord_6362584).sum := by decide
  have hdescent : baseEnd_6362584 < baseStart_6362584 := by decide
  rcases family_descends (prefixWord ++ tailWord_6362584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6362607 : List Nat := [1, 1, 2, 1, 4, 1, 5, 3, 5]
def baseStart_6362607 : Nat := 118140960795 + 6362607 * 2 ^ 59
def prefixEnd_6362607 : Nat := 4983230072969 + 3 ^ 40 * 6362607 * 2
def baseEnd_6362607 : Nat := 363008400740165889394601

theorem tailTrace_6362607 : CollatzResearch.WordTrace tailWord_6362607 prefixEnd_6362607 363008400740165889394601 := by
  unfold tailWord_6362607
  simp only [CollatzResearch.WordTrace]
  refine ⟨232063342060368960608342075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154708894706912640405561383 232063342060368960608342075)
  ·
    refine ⟨348095013090553440912513113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232063342060368960608342075 348095013090553440912513113)
    ·
      refine ⟨261071259817915080684384835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 348095013090553440912513113 261071259817915080684384835)
      ·
        refine ⟨391606889726872621026577253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261071259817915080684384835 391606889726872621026577253)
        ·
          refine ⟨73426291823788616442483235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 391606889726872621026577253 73426291823788616442483235)
          ·
            refine ⟨110139437735682924663724853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73426291823788616442483235 110139437735682924663724853)
            ·
              refine ⟨10325572287720274187224205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 110139437735682924663724853 10325572287720274187224205)
              ·
                refine ⟨3872089607895102820209077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10325572287720274187224205 3872089607895102820209077)
                ·
                  refine ⟨363008400740165889394601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3872089607895102820209077 363008400740165889394601)
                  ·
                    rfl

theorem cell23_6362607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 3, 5].length) (baseStart_6362607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6362607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6362607 prefixEnd_6362607 := by exact prefixLift 6362607
  have htrace : WordTrace (prefixWord ++ tailWord_6362607) baseStart_6362607 baseEnd_6362607 := by
    simpa [prefixWord, tailWord_6362607, baseEnd_6362607] using wordTrace_append hprefix tailTrace_6362607
  have hstable : (prefixWord ++ tailWord_6362607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6362607).length < 2 ^ (prefixWord ++ tailWord_6362607).sum := by decide
  have hdescent : baseEnd_6362607 < baseStart_6362607 := by decide
  rcases family_descends (prefixWord ++ tailWord_6362607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6362620 : List Nat := [2, 2, 2, 1, 2, 1, 3, 1, 4, 5]
def baseStart_6362620 : Nat := 118140960795 + 6362620 * 2 ^ 59
def prefixEnd_6362620 : Nat := 4983230072969 + 3 ^ 40 * 6362620 * 2
def baseEnd_6362620 : Nat := 1089027427303333817896283

theorem tailTrace_6362620 : CollatzResearch.WordTrace tailWord_6362620 prefixEnd_6362620 1089027427303333817896283 := by
  unfold tailWord_6362620
  simp only [CollatzResearch.WordTrace]
  refine ⟨116031908104660931914282657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154709210806214575885710209 116031908104660931914282657)
  ·
    refine ⟨87023931078495698935711993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116031908104660931914282657 87023931078495698935711993)
    ·
      refine ⟨65267948308871774201783995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87023931078495698935711993 65267948308871774201783995)
      ·
        refine ⟨97901922463307661302675993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65267948308871774201783995 97901922463307661302675993)
        ·
          refine ⟨73426441847480745977006995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97901922463307661302675993 73426441847480745977006995)
          ·
            refine ⟨110139662771221118965510493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73426441847480745977006995 110139662771221118965510493)
            ·
              refine ⟨41302373539207919612066435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110139662771221118965510493 41302373539207919612066435)
              ·
                refine ⟨61953560308811879418099653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41302373539207919612066435 61953560308811879418099653)
                ·
                  refine ⟨11616292557902227390893685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61953560308811879418099653 11616292557902227390893685)
                  ·
                    refine ⟨1089027427303333817896283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11616292557902227390893685 1089027427303333817896283)
                    ·
                      rfl

theorem cell23_6362620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 1, 4, 5].length) (baseStart_6362620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6362620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6362620 prefixEnd_6362620 := by exact prefixLift 6362620
  have htrace : WordTrace (prefixWord ++ tailWord_6362620) baseStart_6362620 baseEnd_6362620 := by
    simpa [prefixWord, tailWord_6362620, baseEnd_6362620] using wordTrace_append hprefix tailTrace_6362620
  have hstable : (prefixWord ++ tailWord_6362620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6362620).length < 2 ^ (prefixWord ++ tailWord_6362620).sum := by decide
  have hdescent : baseEnd_6362620 < baseStart_6362620 := by decide
  rcases family_descends (prefixWord ++ tailWord_6362620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6362635 : List Nat := [1, 1, 1, 1, 9, 1, 2, 1, 2, 2, 2]
def baseStart_6362635 : Nat := 118140960795 + 6362635 * 2 ^ 59
def prefixEnd_6362635 : Nat := 4983230072969 + 3 ^ 40 * 6362635 * 2
def baseEnd_6362635 : Nat := 3267089984119818895001281

theorem tailTrace_6362635 : CollatzResearch.WordTrace tailWord_6362635 prefixEnd_6362635 3267089984119818895001281 := by
  unfold tailWord_6362635
  simp only [CollatzResearch.WordTrace]
  refine ⟨232064363304267521390361359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154709575536178347593574239 232064363304267521390361359)
  ·
    refine ⟨348096544956401282085542039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232064363304267521390361359 348096544956401282085542039)
    ·
      refine ⟨522144817434601923128313059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348096544956401282085542039 522144817434601923128313059)
      ·
        refine ⟨783217226151902884692469589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 522144817434601923128313059 783217226151902884692469589)
        ·
          refine ⟨4589163434483805964994939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 783217226151902884692469589 4589163434483805964994939)
          ·
            refine ⟨6883745151725708947492409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4589163434483805964994939 6883745151725708947492409)
            ·
              refine ⟨5162808863794281710619307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6883745151725708947492409 5162808863794281710619307)
              ·
                refine ⟨7744213295691422565928961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5162808863794281710619307 7744213295691422565928961)
                ·
                  refine ⟨5808159971768566924446721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7744213295691422565928961 5808159971768566924446721)
                  ·
                    refine ⟨4356119978826425193335041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5808159971768566924446721 4356119978826425193335041)
                    ·
                      refine ⟨3267089984119818895001281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4356119978826425193335041 3267089984119818895001281)
                      ·
                        rfl

theorem cell23_6362635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 2, 1, 2, 2, 2].length) (baseStart_6362635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6362635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6362635 prefixEnd_6362635 := by exact prefixLift 6362635
  have htrace : WordTrace (prefixWord ++ tailWord_6362635) baseStart_6362635 baseEnd_6362635 := by
    simpa [prefixWord, tailWord_6362635, baseEnd_6362635] using wordTrace_append hprefix tailTrace_6362635
  have hstable : (prefixWord ++ tailWord_6362635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6362635).length < 2 ^ (prefixWord ++ tailWord_6362635).sum := by decide
  have hdescent : baseEnd_6362635 < baseStart_6362635 := by decide
  rcases family_descends (prefixWord ++ tailWord_6362635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6362657 : List Nat := [1, 2, 3, 2, 2, 2, 1, 3, 2, 1, 4]
def baseStart_6362657 : Nat := 118140960795 + 6362657 * 2 ^ 59
def prefixEnd_6362657 : Nat := 4983230072969 + 3 ^ 40 * 6362657 * 2
def baseEnd_6362657 : Nat := 3267101280694217808926179

theorem tailTrace_6362657 : CollatzResearch.WordTrace tailWord_6362657 prefixEnd_6362657 3267101280694217808926179 := by
  unfold tailWord_6362657
  simp only [CollatzResearch.WordTrace]
  refine ⟨232065165710187819147662225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154710110473458546098441483 232065165710187819147662225)
  ·
    refine ⟨174048874282640864360746669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232065165710187819147662225 174048874282640864360746669)
    ·
      refine ⟨65268327855990324135280001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174048874282640864360746669 65268327855990324135280001)
      ·
        refine ⟨48951245891992743101460001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65268327855990324135280001 48951245891992743101460001)
        ·
          refine ⟨36713434418994557326095001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48951245891992743101460001 36713434418994557326095001)
          ·
            refine ⟨27535075814245917994571251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36713434418994557326095001 27535075814245917994571251)
            ·
              refine ⟨41302613721368876991856877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27535075814245917994571251 41302613721368876991856877)
              ·
                refine ⟨15488480145513328871946329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41302613721368876991856877 15488480145513328871946329)
                ·
                  refine ⟨11616360109134996653959747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15488480145513328871946329 11616360109134996653959747)
                  ·
                    refine ⟨17424540163702494980939621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11616360109134996653959747 17424540163702494980939621)
                    ·
                      refine ⟨3267101280694217808926179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17424540163702494980939621 3267101280694217808926179)
                      ·
                        rfl

theorem cell23_6362657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 3, 2, 1, 4].length) (baseStart_6362657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6362657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6362657 prefixEnd_6362657 := by exact prefixLift 6362657
  have htrace : WordTrace (prefixWord ++ tailWord_6362657) baseStart_6362657 baseEnd_6362657 := by
    simpa [prefixWord, tailWord_6362657, baseEnd_6362657] using wordTrace_append hprefix tailTrace_6362657
  have hstable : (prefixWord ++ tailWord_6362657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6362657).length < 2 ^ (prefixWord ++ tailWord_6362657).sum := by decide
  have hdescent : baseEnd_6362657 < baseStart_6362657 := by decide
  rcases family_descends (prefixWord ++ tailWord_6362657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6362701 : List Nat := [1, 6, 1, 1, 3, 1, 1, 2, 3, 4]
def baseStart_6362701 : Nat := 118140960795 + 6362701 * 2 ^ 59
def prefixEnd_6362701 : Nat := 4983230072969 + 3 ^ 40 * 6362701 * 2
def baseEnd_6362701 : Nat := 1089041291281005212258659

theorem tailTrace_6362701 : CollatzResearch.WordTrace tailWord_6362701 prefixEnd_6362701 1089041291281005212258659 := by
  unfold tailWord_6362701
  simp only [CollatzResearch.WordTrace]
  refine ⟨232066770522028414662263957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154711180348018943108175971 232066770522028414662263957)
  ·
    refine ⟨10878129868220081937293623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 232066770522028414662263957 10878129868220081937293623)
    ·
      refine ⟨16317194802330122905940435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10878129868220081937293623 16317194802330122905940435)
      ·
        refine ⟨24475792203495184358910653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16317194802330122905940435 24475792203495184358910653)
        ·
          refine ⟨9178422076310694134591495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24475792203495184358910653 9178422076310694134591495)
          ·
            refine ⟨13767633114466041201887243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9178422076310694134591495 13767633114466041201887243)
            ·
              refine ⟨20651449671699061802830865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13767633114466041201887243 20651449671699061802830865)
              ·
                refine ⟨15488587253774296352123149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20651449671699061802830865 15488587253774296352123149)
                ·
                  refine ⟨5808220220165361132046181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15488587253774296352123149 5808220220165361132046181)
                  ·
                    refine ⟨1089041291281005212258659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5808220220165361132046181 1089041291281005212258659)
                    ·
                      rfl

theorem cell23_6362701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 2, 3, 4].length) (baseStart_6362701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6362701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6362701 prefixEnd_6362701 := by exact prefixLift 6362701
  have htrace : WordTrace (prefixWord ++ tailWord_6362701) baseStart_6362701 baseEnd_6362701 := by
    simpa [prefixWord, tailWord_6362701, baseEnd_6362701] using wordTrace_append hprefix tailTrace_6362701
  have hstable : (prefixWord ++ tailWord_6362701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6362701).length < 2 ^ (prefixWord ++ tailWord_6362701).sum := by decide
  have hdescent : baseEnd_6362701 < baseStart_6362701 := by decide
  rcases family_descends (prefixWord ++ tailWord_6362701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6362720 : List Nat := [2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 5]
def baseStart_6362720 : Nat := 118140960795 + 6362720 * 2 ^ 59
def prefixEnd_6362720 : Nat := 4983230072969 + 3 ^ 40 * 6362720 * 2
def baseEnd_6362720 : Nat := 3267133629975451062438389

theorem tailTrace_6362720 : CollatzResearch.WordTrace tailWord_6362720 prefixEnd_6362720 3267133629975451062438389 := by
  unfold tailWord_6362720
  simp only [CollatzResearch.WordTrace]
  refine ⟨116033731754479790453602807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154711642339306387271470409 116033731754479790453602807)
  ·
    refine ⟨174050597631719685680404211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116033731754479790453602807 174050597631719685680404211)
    ·
      refine ⟨261075896447579528520606317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174050597631719685680404211 261075896447579528520606317)
      ·
        refine ⟨97903461167842323195227369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 261075896447579528520606317 97903461167842323195227369)
        ·
          refine ⟨73427595875881742396420527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97903461167842323195227369 73427595875881742396420527)
          ·
            refine ⟨110141393813822613594630791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73427595875881742396420527 110141393813822613594630791)
            ·
              refine ⟨165212090720733920391946187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110141393813822613594630791 165212090720733920391946187)
              ·
                refine ⟨247818136081100880587919281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 165212090720733920391946187 247818136081100880587919281)
                ·
                  refine ⟨185863602060825660440939461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 247818136081100880587919281 185863602060825660440939461)
                  ·
                    refine ⟨34849425386404811332676149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 185863602060825660440939461 34849425386404811332676149)
                    ·
                      refine ⟨3267133629975451062438389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34849425386404811332676149 3267133629975451062438389)
                      ·
                        rfl

theorem cell23_6362720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 5].length) (baseStart_6362720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6362720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6362720 prefixEnd_6362720 := by exact prefixLift 6362720
  have htrace : WordTrace (prefixWord ++ tailWord_6362720) baseStart_6362720 baseEnd_6362720 := by
    simpa [prefixWord, tailWord_6362720, baseEnd_6362720] using wordTrace_append hprefix tailTrace_6362720
  have hstable : (prefixWord ++ tailWord_6362720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6362720).length < 2 ^ (prefixWord ++ tailWord_6362720).sum := by decide
  have hdescent : baseEnd_6362720 < baseStart_6362720 := by decide
  rcases family_descends (prefixWord ++ tailWord_6362720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6362741 : List Nat := [1, 3, 4, 2, 1, 1, 1, 3, 3, 1, 3]
def baseStart_6362741 : Nat := 118140960795 + 6362741 * 2 ^ 59
def prefixEnd_6362741 : Nat := 4983230072969 + 3 ^ 40 * 6362741 * 2
def baseEnd_6362741 : Nat := 3267144413069195480275793

theorem tailTrace_6362741 : CollatzResearch.WordTrace tailWord_6362741 prefixEnd_6362741 3267144413069195480275793 := by
  unfold tailWord_6362741
  simp only [CollatzResearch.WordTrace]
  refine ⟨232068229441883501493720077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154712152961255667662480051 232068229441883501493720077)
  ·
    refine ⟨87025586040706313060145029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 232068229441883501493720077 87025586040706313060145029)
    ·
      refine ⟨16317297382632433698777193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87025586040706313060145029 16317297382632433698777193)
      ·
        refine ⟨12237973036974325274082895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16317297382632433698777193 12237973036974325274082895)
        ·
          refine ⟨18356959555461487911124343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12237973036974325274082895 18356959555461487911124343)
          ·
            refine ⟨27535439333192231866686515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18356959555461487911124343 27535439333192231866686515)
            ·
              refine ⟨41303158999788347800029773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27535439333192231866686515 41303158999788347800029773)
              ·
                refine ⟨15488684624920630425011165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41303158999788347800029773 15488684624920630425011165)
                ·
                  refine ⟨5808256734345236409379187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15488684624920630425011165 5808256734345236409379187)
                  ·
                    refine ⟨8712385101517854614068781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5808256734345236409379187 8712385101517854614068781)
                    ·
                      refine ⟨3267144413069195480275793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8712385101517854614068781 3267144413069195480275793)
                      ·
                        rfl

theorem cell23_6362741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_6362741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6362741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6362741 prefixEnd_6362741 := by exact prefixLift 6362741
  have htrace : WordTrace (prefixWord ++ tailWord_6362741) baseStart_6362741 baseEnd_6362741 := by
    simpa [prefixWord, tailWord_6362741, baseEnd_6362741] using wordTrace_append hprefix tailTrace_6362741
  have hstable : (prefixWord ++ tailWord_6362741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6362741).length < 2 ^ (prefixWord ++ tailWord_6362741).sum := by decide
  have hdescent : baseEnd_6362741 < baseStart_6362741 := by decide
  rcases family_descends (prefixWord ++ tailWord_6362741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6362764 : List Nat := [2, 2, 1, 2, 1, 1, 6, 2, 1, 1, 4]
def baseStart_6362764 : Nat := 118140960795 + 6362764 * 2 ^ 59
def prefixEnd_6362764 : Nat := 4983230072969 + 3 ^ 40 * 6362764 * 2
def baseEnd_6362764 : Nat := 3267156223124248890288187

theorem tailTrace_6362764 : CollatzResearch.WordTrace tailWord_6362764 prefixEnd_6362764 3267156223124248890288187 := by
  unfold tailWord_6362764
  simp only [CollatzResearch.WordTrace]
  refine ⟨116034534160400088210903673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154712712213866784281204897 116034534160400088210903673)
  ·
    refine ⟨87025900620300066158177755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116034534160400088210903673 87025900620300066158177755)
    ·
      refine ⟨130538850930450099237266633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87025900620300066158177755 130538850930450099237266633)
      ·
        refine ⟨97904138197837574427949975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130538850930450099237266633 97904138197837574427949975)
        ·
          refine ⟨146856207296756361641924963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97904138197837574427949975 146856207296756361641924963)
          ·
            refine ⟨220284310945134542462887445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146856207296756361641924963 220284310945134542462887445)
            ·
              refine ⟨10325827075553181677947849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 220284310945134542462887445 10325827075553181677947849)
              ·
                refine ⟨7744370306664886258460887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10325827075553181677947849 7744370306664886258460887)
                ·
                  refine ⟨11616555459997329387691331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7744370306664886258460887 11616555459997329387691331)
                  ·
                    refine ⟨17424833189995994081536997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11616555459997329387691331 17424833189995994081536997)
                    ·
                      refine ⟨3267156223124248890288187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17424833189995994081536997 3267156223124248890288187)
                      ·
                        rfl

theorem cell23_6362764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 2, 1, 1, 4].length) (baseStart_6362764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6362764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6362764 prefixEnd_6362764 := by exact prefixLift 6362764
  have htrace : WordTrace (prefixWord ++ tailWord_6362764) baseStart_6362764 baseEnd_6362764 := by
    simpa [prefixWord, tailWord_6362764, baseEnd_6362764] using wordTrace_append hprefix tailTrace_6362764
  have hstable : (prefixWord ++ tailWord_6362764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6362764).length < 2 ^ (prefixWord ++ tailWord_6362764).sum := by decide
  have hdescent : baseEnd_6362764 < baseStart_6362764 := by decide
  rcases family_descends (prefixWord ++ tailWord_6362764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6362784 : List Nat := [2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 5]
def baseStart_6362784 : Nat := 118140960795 + 6362784 * 2 ^ 59
def prefixEnd_6362784 : Nat := 4983230072969 + 3 ^ 40 * 6362784 * 2
def baseEnd_6362784 : Nat := 3267166492737338812038095

theorem tailTrace_6362784 : CollatzResearch.WordTrace tailWord_6362784 prefixEnd_6362784 3267166492737338812038095 := by
  unfold tailWord_6362784
  simp only [CollatzResearch.WordTrace]
  refine ⟨116034898890363859918767703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154713198520485146558356937 116034898890363859918767703)
  ·
    refine ⟨174052348335545789878151555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116034898890363859918767703 174052348335545789878151555)
    ·
      refine ⟨261078522503318684817227333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174052348335545789878151555 261078522503318684817227333)
      ·
        refine ⟨48952222969372253403230125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 261078522503318684817227333 48952222969372253403230125)
        ·
          refine ⟨18357083613514595026211297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48952222969372253403230125 18357083613514595026211297)
          ·
            refine ⟨13767812710135946269658473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18357083613514595026211297 13767812710135946269658473)
            ·
              refine ⟨10325859532601959702243855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13767812710135946269658473 10325859532601959702243855)
              ·
                refine ⟨15488789298902939553365783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10325859532601959702243855 15488789298902939553365783)
                ·
                  refine ⟨23233183948354409330048675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15488789298902939553365783 23233183948354409330048675)
                  ·
                    refine ⟨34849775922531613995073013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23233183948354409330048675 34849775922531613995073013)
                    ·
                      refine ⟨3267166492737338812038095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34849775922531613995073013 3267166492737338812038095)
                      ·
                        rfl

theorem cell23_6362784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 5].length) (baseStart_6362784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6362784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6362784 prefixEnd_6362784 := by exact prefixLift 6362784
  have htrace : WordTrace (prefixWord ++ tailWord_6362784) baseStart_6362784 baseEnd_6362784 := by
    simpa [prefixWord, tailWord_6362784, baseEnd_6362784] using wordTrace_append hprefix tailTrace_6362784
  have hstable : (prefixWord ++ tailWord_6362784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6362784).length < 2 ^ (prefixWord ++ tailWord_6362784).sum := by decide
  have hdescent : baseEnd_6362784 < baseStart_6362784 := by decide
  rcases family_descends (prefixWord ++ tailWord_6362784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6362792 : List Nat := [2, 1, 7, 1, 1, 2, 1, 1, 3, 1, 3]
def baseStart_6362792 : Nat := 118140960795 + 6362792 * 2 ^ 59
def prefixEnd_6362792 : Nat := 4983230072969 + 3 ^ 40 * 6362792 * 2
def baseEnd_6362792 : Nat := 3267170600582574780738059

theorem tailTrace_6362792 : CollatzResearch.WordTrace tailWord_6362792 prefixEnd_6362792 3267170600582574780738059 := by
  unfold tailWord_6362792
  simp only [CollatzResearch.WordTrace]
  refine ⟨116035044782349368601913315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154713393043132491469217753 116035044782349368601913315)
  ·
    refine ⟨174052567173524052902869973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116035044782349368601913315 174052567173524052902869973)
    ·
      refine ⟨4079357043129469989911015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 174052567173524052902869973 4079357043129469989911015)
      ·
        refine ⟨6119035564694204984866523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4079357043129469989911015 6119035564694204984866523)
        ·
          refine ⟨9178553347041307477299785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6119035564694204984866523 9178553347041307477299785)
          ·
            refine ⟨6883915010280980607974839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9178553347041307477299785 6883915010280980607974839)
            ·
              refine ⟨10325872515421470911962259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6883915010280980607974839 10325872515421470911962259)
              ·
                refine ⟨15488808773132206367943389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10325872515421470911962259 15488808773132206367943389)
                ·
                  refine ⟨5808303289924577387978771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15488808773132206367943389 5808303289924577387978771)
                  ·
                    refine ⟨8712454934886866081968157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5808303289924577387978771 8712454934886866081968157)
                    ·
                      refine ⟨3267170600582574780738059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8712454934886866081968157 3267170600582574780738059)
                      ·
                        rfl

theorem cell23_6362792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_6362792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6362792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6362792 prefixEnd_6362792 := by exact prefixLift 6362792
  have htrace : WordTrace (prefixWord ++ tailWord_6362792) baseStart_6362792 baseEnd_6362792 := by
    simpa [prefixWord, tailWord_6362792, baseEnd_6362792] using wordTrace_append hprefix tailTrace_6362792
  have hstable : (prefixWord ++ tailWord_6362792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6362792).length < 2 ^ (prefixWord ++ tailWord_6362792).sum := by decide
  have hdescent : baseEnd_6362792 < baseStart_6362792 := by decide
  rcases family_descends (prefixWord ++ tailWord_6362792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6362847 : List Nat := [1, 1, 2, 3, 2, 2, 2, 2, 2, 6]
def baseStart_6362847 : Nat := 118140960795 + 6362847 * 2 ^ 59
def prefixEnd_6362847 : Nat := 4983230072969 + 3 ^ 40 * 6362847 * 2
def baseEnd_6362847 : Nat := 1089066280672857355183435

theorem tailTrace_6362847 : CollatzResearch.WordTrace tailWord_6362847 prefixEnd_6362847 1089066280672857355183435 := by
  unfold tailWord_6362847
  simp only [CollatzResearch.WordTrace]
  refine ⟨232072095579499481597078795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154714730386332987731385863 232072095579499481597078795)
  ·
    refine ⟨348108143369249222395618193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232072095579499481597078795 348108143369249222395618193)
    ·
      refine ⟨261081107526936916796713645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 348108143369249222395618193 261081107526936916796713645)
      ·
        refine ⟨97905415322601343798767617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 261081107526936916796713645 97905415322601343798767617)
        ·
          refine ⟨73429061491951007849075713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97905415322601343798767617 73429061491951007849075713)
          ·
            refine ⟨55071796118963255886806785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73429061491951007849075713 55071796118963255886806785)
            ·
              refine ⟨41303847089222441915105089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55071796118963255886806785 41303847089222441915105089)
              ·
                refine ⟨30977885316916831436328817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41303847089222441915105089 30977885316916831436328817)
                ·
                  refine ⟨23233413987687623577246613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30977885316916831436328817 23233413987687623577246613)
                  ·
                    refine ⟨1089066280672857355183435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23233413987687623577246613 1089066280672857355183435)
                    ·
                      rfl

theorem cell23_6362847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 2, 2, 6].length) (baseStart_6362847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6362847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6362847 prefixEnd_6362847 := by exact prefixLift 6362847
  have htrace : WordTrace (prefixWord ++ tailWord_6362847) baseStart_6362847 baseEnd_6362847 := by
    simpa [prefixWord, tailWord_6362847, baseEnd_6362847] using wordTrace_append hprefix tailTrace_6362847
  have hstable : (prefixWord ++ tailWord_6362847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6362847).length < 2 ^ (prefixWord ++ tailWord_6362847).sum := by decide
  have hdescent : baseEnd_6362847 < baseStart_6362847 := by decide
  rcases family_descends (prefixWord ++ tailWord_6362847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6362849 : List Nat := [1, 2, 3, 1, 6, 1, 2, 2, 1, 2, 2]
def baseStart_6362849 : Nat := 118140960795 + 6362849 * 2 ^ 59
def prefixEnd_6362849 : Nat := 4983230072969 + 3 ^ 40 * 6362849 * 2
def baseEnd_6362849 : Nat := 3267199868979881057725297

theorem tailTrace_6362849 : CollatzResearch.WordTrace tailWord_6362849 prefixEnd_6362849 3267199868979881057725297 := by
  unfold tailWord_6362849
  simp only [CollatzResearch.WordTrace]
  refine ⟨232072168525492235938651601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154714779016994823959101067 232072168525492235938651601)
  ·
    refine ⟨174054126394119176953988701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232072168525492235938651601 174054126394119176953988701)
    ·
      refine ⟨65270297397794691357745763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174054126394119176953988701 65270297397794691357745763)
      ·
        refine ⟨97905446096692037036618645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65270297397794691357745763 97905446096692037036618645)
        ·
          refine ⟨4589317785782439236091499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 97905446096692037036618645 4589317785782439236091499)
          ·
            refine ⟨6883976678673658854137249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4589317785782439236091499 6883976678673658854137249)
            ·
              refine ⟨5162982509005244140602937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6883976678673658854137249 5162982509005244140602937)
              ·
                refine ⟨3872236881753933105452203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5162982509005244140602937 3872236881753933105452203)
                ·
                  refine ⟨5808355322630899658178305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3872236881753933105452203 5808355322630899658178305)
                  ·
                    refine ⟨4356266491973174743633729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5808355322630899658178305 4356266491973174743633729)
                    ·
                      refine ⟨3267199868979881057725297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4356266491973174743633729 3267199868979881057725297)
                      ·
                        rfl

theorem cell23_6362849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 2, 2, 1, 2, 2].length) (baseStart_6362849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6362849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6362849 prefixEnd_6362849 := by exact prefixLift 6362849
  have htrace : WordTrace (prefixWord ++ tailWord_6362849) baseStart_6362849 baseEnd_6362849 := by
    simpa [prefixWord, tailWord_6362849, baseEnd_6362849] using wordTrace_append hprefix tailTrace_6362849
  have hstable : (prefixWord ++ tailWord_6362849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6362849).length < 2 ^ (prefixWord ++ tailWord_6362849).sum := by decide
  have hdescent : baseEnd_6362849 < baseStart_6362849 := by decide
  rcases family_descends (prefixWord ++ tailWord_6362849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6362867 : List Nat := [1, 1, 1, 2, 2, 3, 3, 1, 1, 4, 4]
def baseStart_6362867 : Nat := 118140960795 + 6362867 * 2 ^ 59
def prefixEnd_6362867 : Nat := 4983230072969 + 3 ^ 40 * 6362867 * 2
def baseEnd_6362867 : Nat := 3267209111631661987300213

theorem tailTrace_6362867 : CollatzResearch.WordTrace tailWord_6362867 prefixEnd_6362867 3267209111631661987300213 := by
  unfold tailWord_6362867
  simp only [CollatzResearch.WordTrace]
  refine ⟨232072825039427025012806855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154715216692951350008537903 232072825039427025012806855)
  ·
    refine ⟨348109237559140537519210283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232072825039427025012806855 348109237559140537519210283)
    ·
      refine ⟨522163856338710806278815425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348109237559140537519210283 522163856338710806278815425)
      ·
        refine ⟨391622892254033104709111569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 522163856338710806278815425 391622892254033104709111569)
        ·
          refine ⟨293717169190524828531833677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 391622892254033104709111569 293717169190524828531833677)
          ·
            refine ⟨110143938446446810699437629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 293717169190524828531833677 110143938446446810699437629)
            ·
              refine ⟨41303976917417554012289111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110143938446446810699437629 41303976917417554012289111)
              ·
                refine ⟨61955965376126331018433667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41303976917417554012289111 61955965376126331018433667)
                ·
                  refine ⟨92933948064189496527650501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61955965376126331018433667 92933948064189496527650501)
                  ·
                    refine ⟨17425115262035530598934469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 92933948064189496527650501 17425115262035530598934469)
                    ·
                      refine ⟨3267209111631661987300213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17425115262035530598934469 3267209111631661987300213)
                      ·
                        rfl

theorem cell23_6362867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 1, 1, 4, 4].length) (baseStart_6362867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6362867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6362867 prefixEnd_6362867 := by exact prefixLift 6362867
  have htrace : WordTrace (prefixWord ++ tailWord_6362867) baseStart_6362867 baseEnd_6362867 := by
    simpa [prefixWord, tailWord_6362867, baseEnd_6362867] using wordTrace_append hprefix tailTrace_6362867
  have hstable : (prefixWord ++ tailWord_6362867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6362867).length < 2 ^ (prefixWord ++ tailWord_6362867).sum := by decide
  have hdescent : baseEnd_6362867 < baseStart_6362867 := by decide
  rcases family_descends (prefixWord ++ tailWord_6362867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6362904 : List Nat := [2, 1, 2, 3, 1, 1, 3, 2, 2, 3, 3]
def baseStart_6362904 : Nat := 118140960795 + 6362904 * 2 ^ 59
def prefixEnd_6362904 : Nat := 4983230072969 + 3 ^ 40 * 6362904 * 2
def baseEnd_6362904 : Nat := 3267228110415878342537543

theorem tailTrace_6362904 : CollatzResearch.WordTrace tailWord_6362904 prefixEnd_6362904 3267228110415878342537543 := by
  unfold tailWord_6362904
  simp only [CollatzResearch.WordTrace]
  refine ⟨116037087270146490165951883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154716116360195320221269177 116037087270146490165951883)
  ·
    refine ⟨174055630905219735248927825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116037087270146490165951883 174055630905219735248927825)
    ·
      refine ⟨130541723178914801436695869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174055630905219735248927825 130541723178914801436695869)
      ·
        refine ⟨48953146192093050538760951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130541723178914801436695869 48953146192093050538760951)
        ·
          refine ⟨73429719288139575808141427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48953146192093050538760951 73429719288139575808141427)
          ·
            refine ⟨110144578932209363712212141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73429719288139575808141427 110144578932209363712212141)
            ·
              refine ⟨41304217099578511392079553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110144578932209363712212141 41304217099578511392079553)
              ·
                refine ⟨30978162824683883544059665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41304217099578511392079553 30978162824683883544059665)
                ·
                  refine ⟨23233622118512912658044749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30978162824683883544059665 23233622118512912658044749)
                  ·
                    refine ⟨8712608294442342246766781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23233622118512912658044749 8712608294442342246766781)
                    ·
                      refine ⟨3267228110415878342537543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8712608294442342246766781 3267228110415878342537543)
                      ·
                        rfl

theorem cell23_6362904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 2, 2, 3, 3].length) (baseStart_6362904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6362904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6362904 prefixEnd_6362904 := by exact prefixLift 6362904
  have htrace : WordTrace (prefixWord ++ tailWord_6362904) baseStart_6362904 baseEnd_6362904 := by
    simpa [prefixWord, tailWord_6362904, baseEnd_6362904] using wordTrace_append hprefix tailTrace_6362904
  have hstable : (prefixWord ++ tailWord_6362904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6362904).length < 2 ^ (prefixWord ++ tailWord_6362904).sum := by decide
  have hdescent : baseEnd_6362904 < baseStart_6362904 := by decide
  rcases family_descends (prefixWord ++ tailWord_6362904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6362961 : List Nat := [1, 2, 2, 1, 5, 2, 1, 2, 2, 1, 4]
def baseStart_6362961 : Nat := 118140960795 + 6362961 * 2 ^ 59
def prefixEnd_6362961 : Nat := 4983230072969 + 3 ^ 40 * 6362961 * 2
def baseEnd_6362961 : Nat := 3267257378813184619524781

theorem tailTrace_6362961 : CollatzResearch.WordTrace tailWord_6362961 prefixEnd_6362961 3267257378813184619524781 := by
  unfold tailWord_6362961
  simp only [CollatzResearch.WordTrace]
  refine ⟨232076253501086479066728737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154717502334057652711152491 232076253501086479066728737)
  ·
    refine ⟨174057190125814859300046553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232076253501086479066728737 174057190125814859300046553)
    ·
      refine ⟨130542892594361144475034915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174057190125814859300046553 130542892594361144475034915)
      ·
        refine ⟨195814338891541716712552373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130542892594361144475034915 195814338891541716712552373)
        ·
          refine ⟨18357594271082035941801785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 195814338891541716712552373 18357594271082035941801785)
          ·
            refine ⟨13768195703311526956351339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18357594271082035941801785 13768195703311526956351339)
            ·
              refine ⟨20652293554967290434527009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13768195703311526956351339 20652293554967290434527009)
              ·
                refine ⟨15489220166225467825895257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20652293554967290434527009 15489220166225467825895257)
                ·
                  refine ⟨11616915124669100869421443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15489220166225467825895257 11616915124669100869421443)
                  ·
                    refine ⟨17425372687003651304132165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11616915124669100869421443 17425372687003651304132165)
                    ·
                      refine ⟨3267257378813184619524781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17425372687003651304132165 3267257378813184619524781)
                      ·
                        rfl

theorem cell23_6362961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 2, 2, 1, 4].length) (baseStart_6362961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6362961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6362961 prefixEnd_6362961 := by exact prefixLift 6362961
  have htrace : WordTrace (prefixWord ++ tailWord_6362961) baseStart_6362961 baseEnd_6362961 := by
    simpa [prefixWord, tailWord_6362961, baseEnd_6362961] using wordTrace_append hprefix tailTrace_6362961
  have hstable : (prefixWord ++ tailWord_6362961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6362961).length < 2 ^ (prefixWord ++ tailWord_6362961).sum := by decide
  have hdescent : baseEnd_6362961 < baseStart_6362961 := by decide
  rcases family_descends (prefixWord ++ tailWord_6362961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6363018 : List Nat := [3, 1, 2, 4, 2, 1, 2, 2, 6]
def baseStart_6363018 : Nat := 118140960795 + 6363018 * 2 ^ 59
def prefixEnd_6363018 : Nat := 4983230072969 + 3 ^ 40 * 6363018 * 2
def baseEnd_6363018 : Nat := 363031849690054544056891

theorem tailTrace_6363018 : CollatzResearch.WordTrace tailWord_6363018 prefixEnd_6363018 363031849690054544056891 := by
  unfold tailWord_6363018
  simp only [CollatzResearch.WordTrace]
  refine ⟨58019583115469994450388427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154718888307919985201035805 58019583115469994450388427)
  ·
    refine ⟨87029374673204991675582641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58019583115469994450388427 87029374673204991675582641)
    ·
      refine ⟨65272031004903743756686981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87029374673204991675582641 65272031004903743756686981)
      ·
        refine ⟨12238505813419451954378809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65272031004903743756686981 12238505813419451954378809)
        ·
          refine ⟨9178879360064588965784107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12238505813419451954378809 9178879360064588965784107)
          ·
            refine ⟨13768319040096883448676161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9178879360064588965784107 13768319040096883448676161)
            ·
              refine ⟨10326239280072662586507121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13768319040096883448676161 10326239280072662586507121)
              ·
                refine ⟨7744679460054496939880341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10326239280072662586507121 7744679460054496939880341)
                ·
                  refine ⟨363031849690054544056891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7744679460054496939880341 363031849690054544056891)
                  ·
                    rfl

theorem cell23_6363018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 2, 6].length) (baseStart_6363018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6363018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6363018 prefixEnd_6363018 := by exact prefixLift 6363018
  have htrace : WordTrace (prefixWord ++ tailWord_6363018) baseStart_6363018 baseEnd_6363018 := by
    simpa [prefixWord, tailWord_6363018, baseEnd_6363018] using wordTrace_append hprefix tailTrace_6363018
  have hstable : (prefixWord ++ tailWord_6363018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6363018).length < 2 ^ (prefixWord ++ tailWord_6363018).sum := by decide
  have hdescent : baseEnd_6363018 < baseStart_6363018 := by decide
  rcases family_descends (prefixWord ++ tailWord_6363018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6363022 : List Nat := [4, 1, 1, 5, 1, 1, 1, 4, 1, 4]
def baseStart_6363022 : Nat := 118140960795 + 6363022 * 2 ^ 59
def prefixEnd_6363022 : Nat := 4983230072969 + 3 ^ 40 * 6363022 * 2
def baseEnd_6363022 : Nat := 1089096233711036293620667

theorem tailTrace_6363022 : CollatzResearch.WordTrace tailWord_6363022 prefixEnd_6363022 1089096233711036293620667 := by
  unfold tailWord_6363022
  simp only [CollatzResearch.WordTrace]
  refine ⟨29009809794233185810587415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154718985569243657656466213 29009809794233185810587415)
  ·
    refine ⟨43514714691349778715881123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29009809794233185810587415 43514714691349778715881123)
    ·
      refine ⟨65272072037024668073821685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43514714691349778715881123 65272072037024668073821685)
      ·
        refine ⟨6119256753471062631920783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 65272072037024668073821685 6119256753471062631920783)
        ·
          refine ⟨9178885130206593947881175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6119256753471062631920783 9178885130206593947881175)
          ·
            refine ⟨13768327695309890921821763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9178885130206593947881175 13768327695309890921821763)
            ·
              refine ⟨20652491542964836382732645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13768327695309890921821763 20652491542964836382732645)
              ·
                refine ⟨3872342164305906821762371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20652491542964836382732645 3872342164305906821762371)
                ·
                  refine ⟨5808513246458860232643557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3872342164305906821762371 5808513246458860232643557)
                  ·
                    refine ⟨1089096233711036293620667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5808513246458860232643557 1089096233711036293620667)
                    ·
                      rfl

theorem cell23_6363022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 4, 1, 4].length) (baseStart_6363022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6363022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6363022 prefixEnd_6363022 := by exact prefixLift 6363022
  have htrace : WordTrace (prefixWord ++ tailWord_6363022) baseStart_6363022 baseEnd_6363022 := by
    simpa [prefixWord, tailWord_6363022, baseEnd_6363022] using wordTrace_append hprefix tailTrace_6363022
  have hstable : (prefixWord ++ tailWord_6363022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6363022).length < 2 ^ (prefixWord ++ tailWord_6363022).sum := by decide
  have hdescent : baseEnd_6363022 < baseStart_6363022 := by decide
  rcases family_descends (prefixWord ++ tailWord_6363022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6363061 : List Nat := [1, 3, 3, 2, 1, 2, 2, 2, 1, 6]
def baseStart_6363061 : Nat := 118140960795 + 6363061 * 2 ^ 59
def prefixEnd_6363061 : Nat := 4983230072969 + 3 ^ 40 * 6363061 * 2
def baseEnd_6363061 : Nat := 1089102908959544742758107

theorem tailTrace_6363061 : CollatzResearch.WordTrace tailWord_6363061 prefixEnd_6363061 1089102908959544742758107 := by
  unfold tailWord_6363061
  simp only [CollatzResearch.WordTrace]
  refine ⟨232079900800724196145369037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154719933867149464096912691 232079900800724196145369037)
  ·
    refine ⟨87029962800271573554513389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 232079900800724196145369037 87029962800271573554513389)
    ·
      refine ⟨32636236050101840082942521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87029962800271573554513389 32636236050101840082942521)
      ·
        refine ⟨24477177037576380062206891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32636236050101840082942521 24477177037576380062206891)
        ·
          refine ⟨36715765556364570093310337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24477177037576380062206891 36715765556364570093310337)
          ·
            refine ⟨27536824167273427569982753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36715765556364570093310337 27536824167273427569982753)
            ·
              refine ⟨20652618125455070677487065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27536824167273427569982753 20652618125455070677487065)
              ·
                refine ⟨15489463594091303008115299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20652618125455070677487065 15489463594091303008115299)
                ·
                  refine ⟨23234195391136954512172949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15489463594091303008115299 23234195391136954512172949)
                  ·
                    refine ⟨1089102908959544742758107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23234195391136954512172949 1089102908959544742758107)
                    ·
                      rfl

theorem cell23_6363061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 2, 1, 6].length) (baseStart_6363061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6363061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6363061 prefixEnd_6363061 := by exact prefixLift 6363061
  have htrace : WordTrace (prefixWord ++ tailWord_6363061) baseStart_6363061 baseEnd_6363061 := by
    simpa [prefixWord, tailWord_6363061, baseEnd_6363061] using wordTrace_append hprefix tailTrace_6363061
  have hstable : (prefixWord ++ tailWord_6363061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6363061).length < 2 ^ (prefixWord ++ tailWord_6363061).sum := by decide
  have hdescent : baseEnd_6363061 < baseStart_6363061 := by decide
  rcases family_descends (prefixWord ++ tailWord_6363061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6363104 : List Nat := [2, 1, 1, 3, 1, 1, 1, 4, 2, 7]
def baseStart_6363104 : Nat := 118140960795 + 6363104 * 2 ^ 59
def prefixEnd_6363104 : Nat := 4983230072969 + 3 ^ 40 * 6363104 * 2
def baseEnd_6363104 : Nat := 1089110268848925853345541

theorem tailTrace_6363104 : CollatzResearch.WordTrace tailWord_6363104 prefixEnd_6363104 1089110268848925853345541 := by
  unfold tailWord_6363104
  simp only [CollatzResearch.WordTrace]
  refine ⟨116040734569784207244592183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154720979426378942992789577 116040734569784207244592183)
  ·
    refine ⟨174061101854676310866888275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116040734569784207244592183 174061101854676310866888275)
    ·
      refine ⟨261091652782014466300332413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174061101854676310866888275 261091652782014466300332413)
      ·
        refine ⟨97909369793255424862624655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 261091652782014466300332413 97909369793255424862624655)
        ·
          refine ⟨146864054689883137293936983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97909369793255424862624655 146864054689883137293936983)
          ·
            refine ⟨220296082034824705940905475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146864054689883137293936983 220296082034824705940905475)
            ·
              refine ⟨330444123052237058911358213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 220296082034824705940905475 330444123052237058911358213)
              ·
                refine ⟨61958273072294448545879665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 330444123052237058911358213 61958273072294448545879665)
                ·
                  refine ⟨46468704804220836409409749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61958273072294448545879665 46468704804220836409409749)
                  ·
                    refine ⟨1089110268848925853345541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46468704804220836409409749 1089110268848925853345541)
                    ·
                      rfl

theorem cell23_6363104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 4, 2, 7].length) (baseStart_6363104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6363104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6363104 prefixEnd_6363104 := by exact prefixLift 6363104
  have htrace : WordTrace (prefixWord ++ tailWord_6363104) baseStart_6363104 baseEnd_6363104 := by
    simpa [prefixWord, tailWord_6363104, baseEnd_6363104] using wordTrace_append hprefix tailTrace_6363104
  have hstable : (prefixWord ++ tailWord_6363104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6363104).length < 2 ^ (prefixWord ++ tailWord_6363104).sum := by decide
  have hdescent : baseEnd_6363104 < baseStart_6363104 := by decide
  rcases family_descends (prefixWord ++ tailWord_6363104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6363156 : List Nat := [2, 4, 3, 2, 2, 1, 1, 2, 1, 2, 3]
def baseStart_6363156 : Nat := 118140960795 + 6363156 * 2 ^ 59
def prefixEnd_6363156 : Nat := 4983230072969 + 3 ^ 40 * 6363156 * 2
def baseEnd_6363156 : Nat := 3267357507540811356586385

theorem tailTrace_6363156 : CollatzResearch.WordTrace tailWord_6363156 prefixEnd_6363156 3267357507540811356586385 := by
  unfold tailWord_6363156
  simp only [CollatzResearch.WordTrace]
  refine ⟨116041682867690013685038661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154722243823586684913384881 116041682867690013685038661)
  ·
    refine ⟨21757815537691877565944749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116041682867690013685038661 21757815537691877565944749)
    ·
      refine ⟨8159180826634454087229281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21757815537691877565944749 8159180826634454087229281)
      ·
        refine ⟨6119385619975840565421961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8159180826634454087229281 6119385619975840565421961)
        ·
          refine ⟨4589539214981880424066471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6119385619975840565421961 4589539214981880424066471)
          ·
            refine ⟨6884308822472820636099707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4589539214981880424066471 6884308822472820636099707)
            ·
              refine ⟨10326463233709230954149561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6884308822472820636099707 10326463233709230954149561)
              ·
                refine ⟨7744847425281923215612171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10326463233709230954149561 7744847425281923215612171)
                ·
                  refine ⟨11617271137922884823418257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7744847425281923215612171 11617271137922884823418257)
                  ·
                    refine ⟨8712953353442163617563693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11617271137922884823418257 8712953353442163617563693)
                    ·
                      refine ⟨3267357507540811356586385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8712953353442163617563693 3267357507540811356586385)
                      ·
                        rfl

theorem cell23_6363156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_6363156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6363156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6363156 prefixEnd_6363156 := by exact prefixLift 6363156
  have htrace : WordTrace (prefixWord ++ tailWord_6363156) baseStart_6363156 baseEnd_6363156 := by
    simpa [prefixWord, tailWord_6363156, baseEnd_6363156] using wordTrace_append hprefix tailTrace_6363156
  have hstable : (prefixWord ++ tailWord_6363156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6363156).length < 2 ^ (prefixWord ++ tailWord_6363156).sum := by decide
  have hdescent : baseEnd_6363156 < baseStart_6363156 := by decide
  rcases family_descends (prefixWord ++ tailWord_6363156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6363162 : List Nat := [3, 1, 1, 3, 1, 5, 1, 2, 1, 3, 2]
def baseStart_6363162 : Nat := 118140960795 + 6363162 * 2 ^ 59
def prefixEnd_6363162 : Nat := 4983230072969 + 3 ^ 40 * 6363162 * 2
def baseEnd_6363162 : Nat := 3267360588424738333111357

theorem tailTrace_6363162 : CollatzResearch.WordTrace tailWord_6363162 prefixEnd_6363162 3267360588424738333111357 := by
  unfold tailWord_6363162
  simp only [CollatzResearch.WordTrace]
  refine ⟨58020896143339572598698935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154722389715572193596530493 58020896143339572598698935)
  ·
    refine ⟨87031344215009358898048403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58020896143339572598698935 87031344215009358898048403)
    ·
      refine ⟨130547016322514038347072605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87031344215009358898048403 130547016322514038347072605)
      ·
        refine ⟨48955131120942764380152227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130547016322514038347072605 48955131120942764380152227)
        ·
          refine ⟨73432696681414146570228341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48955131120942764380152227 73432696681414146570228341)
          ·
            refine ⟨6884315313882576240958907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 73432696681414146570228341 6884315313882576240958907)
            ·
              refine ⟨10326472970823864361438361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6884315313882576240958907 10326472970823864361438361)
              ·
                refine ⟨7744854728117898271078771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10326472970823864361438361 7744854728117898271078771)
                ·
                  refine ⟨11617282092176847406618157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7744854728117898271078771 11617282092176847406618157)
                  ·
                    refine ⟨4356480784566317777481809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11617282092176847406618157 4356480784566317777481809)
                    ·
                      refine ⟨3267360588424738333111357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4356480784566317777481809 3267360588424738333111357)
                      ·
                        rfl

theorem cell23_6363162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 2, 1, 3, 2].length) (baseStart_6363162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6363162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6363162 prefixEnd_6363162 := by exact prefixLift 6363162
  have htrace : WordTrace (prefixWord ++ tailWord_6363162) baseStart_6363162 baseEnd_6363162 := by
    simpa [prefixWord, tailWord_6363162, baseEnd_6363162] using wordTrace_append hprefix tailTrace_6363162
  have hstable : (prefixWord ++ tailWord_6363162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6363162).length < 2 ^ (prefixWord ++ tailWord_6363162).sum := by decide
  have hdescent : baseEnd_6363162 < baseStart_6363162 := by decide
  rcases family_descends (prefixWord ++ tailWord_6363162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6363178 : List Nat := [3, 1, 4, 1, 2, 1, 2, 1, 2, 1, 5]
def baseStart_6363178 : Nat := 118140960795 + 6363178 * 2 ^ 59
def prefixEnd_6363178 : Nat := 4983230072969 + 3 ^ 40 * 6363178 * 2
def baseEnd_6363178 : Nat := 3267368804115210270511283

theorem tailTrace_6363178 : CollatzResearch.WordTrace tailWord_6363178 prefixEnd_6363178 3267368804115210270511283 := by
  unfold tailWord_6363178
  simp only [CollatzResearch.WordTrace]
  refine ⟨58021042035325081281844547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154722778760866883418252125 58021042035325081281844547)
  ·
    refine ⟨87031563052987621922766821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58021042035325081281844547 87031563052987621922766821)
    ·
      refine ⟨16318418072435179110518779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87031563052987621922766821 16318418072435179110518779)
      ·
        refine ⟨24477627108652768665778169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16318418072435179110518779 24477627108652768665778169)
        ·
          refine ⟨18358220331489576499333627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24477627108652768665778169 18358220331489576499333627)
          ·
            refine ⟨27537330497234364749000441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18358220331489576499333627 27537330497234364749000441)
            ·
              refine ⟨20652997872925773561750331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27537330497234364749000441 20652997872925773561750331)
              ·
                refine ⟨30979496809388660342625497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20652997872925773561750331 30979496809388660342625497)
                ·
                  refine ⟨23234622607041495256969123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30979496809388660342625497 23234622607041495256969123)
                  ·
                    refine ⟨34851933910562242885453685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23234622607041495256969123 34851933910562242885453685)
                    ·
                      refine ⟨3267368804115210270511283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34851933910562242885453685 3267368804115210270511283)
                      ·
                        rfl

theorem cell23_6363178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_6363178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6363178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6363178 prefixEnd_6363178 := by exact prefixLift 6363178
  have htrace : WordTrace (prefixWord ++ tailWord_6363178) baseStart_6363178 baseEnd_6363178 := by
    simpa [prefixWord, tailWord_6363178, baseEnd_6363178] using wordTrace_append hprefix tailTrace_6363178
  have hstable : (prefixWord ++ tailWord_6363178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6363178).length < 2 ^ (prefixWord ++ tailWord_6363178).sum := by decide
  have hdescent : baseEnd_6363178 < baseStart_6363178 := by decide
  rcases family_descends (prefixWord ++ tailWord_6363178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6363228 : List Nat := [2, 2, 4, 1, 1, 3, 1, 1, 1, 7]
def baseStart_6363228 : Nat := 118140960795 + 6363228 * 2 ^ 59
def prefixEnd_6363228 : Nat := 4983230072969 + 3 ^ 40 * 6363228 * 2
def baseEnd_6363228 : Nat := 1089131492715978358295351

theorem tailTrace_6363228 : CollatzResearch.WordTrace tailWord_6363228 prefixEnd_6363228 1089131492715978358295351 := by
  unfold tailWord_6363228
  simp only [CollatzResearch.WordTrace]
  refine ⟨116042995895559591833349169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154723994527412789111132225 116042995895559591833349169)
  ·
    refine ⟨87032246921669693875011877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116042995895559591833349169 87032246921669693875011877)
    ·
      refine ⟨16318546297813067601564727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87032246921669693875011877 16318546297813067601564727)
      ·
        refine ⟨24477819446719601402347091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16318546297813067601564727 24477819446719601402347091)
        ·
          refine ⟨36716729170079402103520637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24477819446719601402347091 36716729170079402103520637)
          ·
            refine ⟨13768773438779775788820239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36716729170079402103520637 13768773438779775788820239)
            ·
              refine ⟨20653160158169663683230359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13768773438779775788820239 20653160158169663683230359)
              ·
                refine ⟨30979740237254495524845539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20653160158169663683230359 30979740237254495524845539)
                ·
                  refine ⟨46469610355881743287268309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30979740237254495524845539 46469610355881743287268309)
                  ·
                    refine ⟨1089131492715978358295351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46469610355881743287268309 1089131492715978358295351)
                    ·
                      rfl

theorem cell23_6363228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_6363228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6363228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6363228 prefixEnd_6363228 := by exact prefixLift 6363228
  have htrace : WordTrace (prefixWord ++ tailWord_6363228) baseStart_6363228 baseEnd_6363228 := by
    simpa [prefixWord, tailWord_6363228, baseEnd_6363228] using wordTrace_append hprefix tailTrace_6363228
  have hstable : (prefixWord ++ tailWord_6363228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6363228).length < 2 ^ (prefixWord ++ tailWord_6363228).sum := by decide
  have hdescent : baseEnd_6363228 < baseStart_6363228 := by decide
  rcases family_descends (prefixWord ++ tailWord_6363228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6363230 : List Nat := [4, 4, 1, 1, 3, 1, 2, 1, 1, 3, 2]
def baseStart_6363230 : Nat := 118140960795 + 6363230 * 2 ^ 59
def prefixEnd_6363230 : Nat := 4983230072969 + 3 ^ 40 * 6363230 * 2
def baseEnd_6363230 : Nat := 3267395505109244067061045

theorem tailTrace_6363230 : CollatzResearch.WordTrace tailWord_6363230 prefixEnd_6363230 3267395505109244067061045 := by
  unfold tailWord_6363230
  simp only [CollatzResearch.WordTrace]
  refine ⟨29010758092138992251033893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154724043158074625338847429 29010758092138992251033893)
  ·
    refine ⟨5439517142276061047068855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29010758092138992251033893 5439517142276061047068855)
    ·
      refine ⟨8159275713414091570603283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5439517142276061047068855 8159275713414091570603283)
      ·
        refine ⟨12238913570121137355904925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8159275713414091570603283 12238913570121137355904925)
        ·
          refine ⟨4589592588795426508464347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12238913570121137355904925 4589592588795426508464347)
          ·
            refine ⟨6884388883193139762696521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4589592588795426508464347 6884388883193139762696521)
            ·
              refine ⟨5163291662394854822022391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6884388883193139762696521 5163291662394854822022391)
              ·
                refine ⟨7744937493592282233033587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5163291662394854822022391 7744937493592282233033587)
                ·
                  refine ⟨11617406240388423349550381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7744937493592282233033587 11617406240388423349550381)
                  ·
                    refine ⟨4356527340145658756081393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11617406240388423349550381 4356527340145658756081393)
                    ·
                      refine ⟨3267395505109244067061045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4356527340145658756081393 3267395505109244067061045)
                      ·
                        rfl

theorem cell23_6363230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 2, 1, 1, 3, 2].length) (baseStart_6363230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6363230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6363230 prefixEnd_6363230 := by exact prefixLift 6363230
  have htrace : WordTrace (prefixWord ++ tailWord_6363230) baseStart_6363230 baseEnd_6363230 := by
    simpa [prefixWord, tailWord_6363230, baseEnd_6363230] using wordTrace_append hprefix tailTrace_6363230
  have hstable : (prefixWord ++ tailWord_6363230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6363230).length < 2 ^ (prefixWord ++ tailWord_6363230).sum := by decide
  have hdescent : baseEnd_6363230 < baseStart_6363230 := by decide
  rcases family_descends (prefixWord ++ tailWord_6363230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6363268 : List Nat := [2, 3, 2, 1, 2, 1, 1, 1, 3, 4, 3]
def baseStart_6363268 : Nat := 118140960795 + 6363268 * 2 ^ 59
def prefixEnd_6363268 : Nat := 4983230072969 + 3 ^ 40 * 6363268 * 2
def baseEnd_6363268 : Nat := 3267415017374114918385869

theorem tailTrace_6363268 : CollatzResearch.WordTrace tailWord_6363268 prefixEnd_6363268 3267415017374114918385869 := by
  unfold tailWord_6363268
  simp only [CollatzResearch.WordTrace]
  refine ⟨116043725355487135249077229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154724967140649513665436305 116043725355487135249077229)
  ·
    refine ⟨43516397008307675718403961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116043725355487135249077229 43516397008307675718403961)
    ·
      refine ⟨32637297756230756788802971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43516397008307675718403961 32637297756230756788802971)
      ·
        refine ⟨48955946634346135183204457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32637297756230756788802971 48955946634346135183204457)
        ·
          refine ⟨36716959975759601387403343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48955946634346135183204457 36716959975759601387403343)
          ·
            refine ⟨55075439963639402081105015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36716959975759601387403343 55075439963639402081105015)
            ·
              refine ⟨82613159945459103121657523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55075439963639402081105015 82613159945459103121657523)
              ·
                refine ⟨123919739918188654682486285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82613159945459103121657523 123919739918188654682486285)
                ·
                  refine ⟨46469902469320745505932357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 123919739918188654682486285 46469902469320745505932357)
                  ·
                    refine ⟨8713106712997639782362317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46469902469320745505932357 8713106712997639782362317)
                    ·
                      refine ⟨3267415017374114918385869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8713106712997639782362317 3267415017374114918385869)
                      ·
                        rfl

theorem cell23_6363268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 3, 4, 3].length) (baseStart_6363268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6363268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6363268 prefixEnd_6363268 := by exact prefixLift 6363268
  have htrace : WordTrace (prefixWord ++ tailWord_6363268) baseStart_6363268 baseEnd_6363268 := by
    simpa [prefixWord, tailWord_6363268, baseEnd_6363268] using wordTrace_append hprefix tailTrace_6363268
  have hstable : (prefixWord ++ tailWord_6363268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6363268).length < 2 ^ (prefixWord ++ tailWord_6363268).sum := by decide
  have hdescent : baseEnd_6363268 < baseStart_6363268 := by decide
  rcases family_descends (prefixWord ++ tailWord_6363268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6363311 : List Nat := [1, 1, 2, 1, 2, 3, 1, 2, 2, 1, 7]
def baseStart_6363311 : Nat := 118140960795 + 6363311 * 2 ^ 59
def prefixEnd_6363311 : Nat := 4983230072969 + 3 ^ 40 * 6363311 * 2
def baseEnd_6363311 : Nat := 3267437097042258250148171

theorem tailTrace_6363311 : CollatzResearch.WordTrace tailWord_6363311 prefixEnd_6363311 3267437097042258250148171 := by
  unfold tailWord_6363311
  simp only [CollatzResearch.WordTrace]
  refine ⟨232089019049818488841969787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154726012699878992561313191 232089019049818488841969787)
  ·
    refine ⟨348133528574727733262954681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232089019049818488841969787 348133528574727733262954681)
    ·
      refine ⟨261100146431045799947216011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 348133528574727733262954681 261100146431045799947216011)
      ·
        refine ⟨391650219646568699920824017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261100146431045799947216011 391650219646568699920824017)
        ·
          refine ⟨293737664734926524940618013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 391650219646568699920824017 293737664734926524940618013)
          ·
            refine ⟨110151624275597446852731755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 293737664734926524940618013 110151624275597446852731755)
            ·
              refine ⟨165227436413396170279097633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110151624275597446852731755 165227436413396170279097633)
              ·
                refine ⟨123920577310047127709323225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 165227436413396170279097633 123920577310047127709323225)
                ·
                  refine ⟨92940432982535345781992419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 123920577310047127709323225 92940432982535345781992419)
                  ·
                    refine ⟨139410649473803018672988629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 92940432982535345781992419 139410649473803018672988629)
                    ·
                      refine ⟨3267437097042258250148171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 139410649473803018672988629 3267437097042258250148171)
                      ·
                        rfl

theorem cell23_6363311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 2, 1, 7].length) (baseStart_6363311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6363311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6363311 prefixEnd_6363311 := by exact prefixLift 6363311
  have htrace : WordTrace (prefixWord ++ tailWord_6363311) baseStart_6363311 baseEnd_6363311 := by
    simpa [prefixWord, tailWord_6363311, baseEnd_6363311] using wordTrace_append hprefix tailTrace_6363311
  have hstable : (prefixWord ++ tailWord_6363311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6363311).length < 2 ^ (prefixWord ++ tailWord_6363311).sum := by decide
  have hdescent : baseEnd_6363311 < baseStart_6363311 := by decide
  rcases family_descends (prefixWord ++ tailWord_6363311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6363325 : List Nat := [1, 4, 1, 2, 1, 1, 1, 1, 6, 3, 2]
def baseStart_6363325 : Nat := 118140960795 + 6363325 * 2 ^ 59
def prefixEnd_6363325 : Nat := 4983230072969 + 3 ^ 40 * 6363325 * 2
def baseEnd_6363325 : Nat := 3267444285771421195373107

theorem tailTrace_6363325 : CollatzResearch.WordTrace tailWord_6363325 prefixEnd_6363325 3267444285771421195373107 := by
  unfold tailWord_6363325
  simp only [CollatzResearch.WordTrace]
  refine ⟨232089529671767769232979429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154726353114511846155319619 232089529671767769232979429)
  ·
    refine ⟨43516786813456456731183643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 232089529671767769232979429 43516786813456456731183643)
    ·
      refine ⟨65275180220184685096775465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43516786813456456731183643 65275180220184685096775465)
      ·
        refine ⟨48956385165138513822581599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65275180220184685096775465 48956385165138513822581599)
        ·
          refine ⟨73434577747707770733872399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48956385165138513822581599 73434577747707770733872399)
          ·
            refine ⟨110151866621561656100808599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73434577747707770733872399 110151866621561656100808599)
            ·
              refine ⟨165227799932342484151212899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110151866621561656100808599 165227799932342484151212899)
              ·
                refine ⟨247841699898513726226819349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 165227799932342484151212899 247841699898513726226819349)
                ·
                  refine ⟨11617579682742830916882157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 247841699898513726226819349 11617579682742830916882157)
                  ·
                    refine ⟨4356592381028561593830809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11617579682742830916882157 4356592381028561593830809)
                    ·
                      refine ⟨3267444285771421195373107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4356592381028561593830809 3267444285771421195373107)
                      ·
                        rfl

theorem cell23_6363325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 6, 3, 2].length) (baseStart_6363325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6363325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6363325 prefixEnd_6363325 := by exact prefixLift 6363325
  have htrace : WordTrace (prefixWord ++ tailWord_6363325) baseStart_6363325 baseEnd_6363325 := by
    simpa [prefixWord, tailWord_6363325, baseEnd_6363325] using wordTrace_append hprefix tailTrace_6363325
  have hstable : (prefixWord ++ tailWord_6363325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6363325).length < 2 ^ (prefixWord ++ tailWord_6363325).sum := by decide
  have hdescent : baseEnd_6363325 < baseStart_6363325 := by decide
  rcases family_descends (prefixWord ++ tailWord_6363325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6363342 : List Nat := [4, 1, 1, 1, 4, 1, 1, 3, 2, 3, 2]
def baseStart_6363342 : Nat := 118140960795 + 6363342 * 2 ^ 59
def prefixEnd_6363342 : Nat := 4983230072969 + 3 ^ 40 * 6363342 * 2
def baseEnd_6363342 : Nat := 3267453014942547628860529

theorem tailTrace_6363342 : CollatzResearch.WordTrace tailWord_6363342 prefixEnd_6363342 3267453014942547628860529 := by
  unfold tailWord_6363342
  simp only [CollatzResearch.WordTrace]
  refine ⟨29011268714088272642043535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154726766475137454090898853 29011268714088272642043535)
  ·
    refine ⟨43516903071132408963065303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29011268714088272642043535 43516903071132408963065303)
    ·
      refine ⟨65275354606698613444597955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43516903071132408963065303 65275354606698613444597955)
      ·
        refine ⟨97913031910047920166896933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65275354606698613444597955 97913031910047920166896933)
        ·
          refine ⟨18358693483133985031293175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97913031910047920166896933 18358693483133985031293175)
          ·
            refine ⟨27538040224700977546939763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18358693483133985031293175 27538040224700977546939763)
            ·
              refine ⟨41307060337051466320409645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27538040224700977546939763 41307060337051466320409645)
              ·
                refine ⟨15490147626394299870153617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41307060337051466320409645 15490147626394299870153617)
                ·
                  refine ⟨11617610719795724902615213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15490147626394299870153617 11617610719795724902615213)
                  ·
                    refine ⟨4356604019923396838480705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11617610719795724902615213 4356604019923396838480705)
                    ·
                      refine ⟨3267453014942547628860529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4356604019923396838480705 3267453014942547628860529)
                      ·
                        rfl

theorem cell23_6363342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 3, 2, 3, 2].length) (baseStart_6363342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6363342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6363342 prefixEnd_6363342 := by exact prefixLift 6363342
  have htrace : WordTrace (prefixWord ++ tailWord_6363342) baseStart_6363342 baseEnd_6363342 := by
    simpa [prefixWord, tailWord_6363342, baseEnd_6363342] using wordTrace_append hprefix tailTrace_6363342
  have hstable : (prefixWord ++ tailWord_6363342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6363342).length < 2 ^ (prefixWord ++ tailWord_6363342).sum := by decide
  have hdescent : baseEnd_6363342 < baseStart_6363342 := by decide
  rcases family_descends (prefixWord ++ tailWord_6363342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6363352 : List Nat := [2, 1, 2, 2, 4, 2, 3, 1, 1, 5]
def baseStart_6363352 : Nat := 118140960795 + 6363352 * 2 ^ 59
def prefixEnd_6363352 : Nat := 4983230072969 + 3 ^ 40 * 6363352 * 2
def baseEnd_6363352 : Nat := 1089152716583030863245161

theorem tailTrace_6363352 : CollatzResearch.WordTrace tailWord_6363352 prefixEnd_6363352 1089152716583030863245161 := by
  unfold tailWord_6363352
  simp only [CollatzResearch.WordTrace]
  refine ⟨116045257221334976422106155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154727009628446635229474873 116045257221334976422106155)
  ·
    refine ⟨174067885832002464633159233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116045257221334976422106155 174067885832002464633159233)
    ·
      refine ⟨130550914374001848474869425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174067885832002464633159233 130550914374001848474869425)
      ·
        refine ⟨97913185780501386356152069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130550914374001848474869425 97913185780501386356152069)
        ·
          refine ⟨18358722333844009941778513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97913185780501386356152069 18358722333844009941778513)
          ·
            refine ⟨13769041750383007456333885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18358722333844009941778513 13769041750383007456333885)
            ·
              refine ⟨5163390656393627796125207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13769041750383007456333885 5163390656393627796125207)
              ·
                refine ⟨7745085984590441694187811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5163390656393627796125207 7745085984590441694187811)
                ·
                  refine ⟨11617628976885662541281717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7745085984590441694187811 11617628976885662541281717)
                  ·
                    refine ⟨1089152716583030863245161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11617628976885662541281717 1089152716583030863245161)
                    ·
                      rfl

theorem cell23_6363352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 3, 1, 1, 5].length) (baseStart_6363352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6363352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6363352 prefixEnd_6363352 := by exact prefixLift 6363352
  have htrace : WordTrace (prefixWord ++ tailWord_6363352) baseStart_6363352 baseEnd_6363352 := by
    simpa [prefixWord, tailWord_6363352, baseEnd_6363352] using wordTrace_append hprefix tailTrace_6363352
  have hstable : (prefixWord ++ tailWord_6363352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6363352).length < 2 ^ (prefixWord ++ tailWord_6363352).sum := by decide
  have hdescent : baseEnd_6363352 < baseStart_6363352 := by decide
  rcases family_descends (prefixWord ++ tailWord_6363352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6363372 : List Nat := [2, 2, 1, 1, 2, 3, 2, 3, 3, 2, 2]
def baseStart_6363372 : Nat := 118140960795 + 6363372 * 2 ^ 59
def prefixEnd_6363372 : Nat := 4983230072969 + 3 ^ 40 * 6363372 * 2
def baseEnd_6363372 : Nat := 3267468419362182511485391

theorem tailTrace_6363372 : CollatzResearch.WordTrace tailWord_6363372 prefixEnd_6363372 3267468419362182511485391 := by
  unfold tailWord_6363372
  simp only [CollatzResearch.WordTrace]
  refine ⟨116045621951298748129970185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154727495935064997506626913 116045621951298748129970185)
  ·
    refine ⟨87034216463474061097477639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116045621951298748129970185 87034216463474061097477639)
    ·
      refine ⟨130551324695211091646216459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87034216463474061097477639 130551324695211091646216459)
      ·
        refine ⟨195826987042816637469324689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130551324695211091646216459 195826987042816637469324689)
        ·
          refine ⟨146870240282112478101993517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 195826987042816637469324689 146870240282112478101993517)
          ·
            refine ⟨55076340105792179288247569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 146870240282112478101993517 55076340105792179288247569)
            ·
              refine ⟨41307255079344134466185677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55076340105792179288247569 41307255079344134466185677)
              ·
                refine ⟨15490220654754050424819629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41307255079344134466185677 15490220654754050424819629)
                ·
                  refine ⟨5808832745532768909307361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15490220654754050424819629 5808832745532768909307361)
                  ·
                    refine ⟨4356624559149576681980521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5808832745532768909307361 4356624559149576681980521)
                    ·
                      refine ⟨3267468419362182511485391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4356624559149576681980521 3267468419362182511485391)
                      ·
                        rfl

theorem cell23_6363372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 2, 2].length) (baseStart_6363372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6363372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6363372 prefixEnd_6363372 := by exact prefixLift 6363372
  have htrace : WordTrace (prefixWord ++ tailWord_6363372) baseStart_6363372 baseEnd_6363372 := by
    simpa [prefixWord, tailWord_6363372, baseEnd_6363372] using wordTrace_append hprefix tailTrace_6363372
  have hstable : (prefixWord ++ tailWord_6363372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6363372).length < 2 ^ (prefixWord ++ tailWord_6363372).sum := by decide
  have hdescent : baseEnd_6363372 < baseStart_6363372 := by decide
  rcases family_descends (prefixWord ++ tailWord_6363372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6363375 : List Nat := [1, 1, 2, 1, 6, 1, 1, 2, 3, 2, 3]
def baseStart_6363375 : Nat := 118140960795 + 6363375 * 2 ^ 59
def prefixEnd_6363375 : Nat := 4983230072969 + 3 ^ 40 * 6363375 * 2
def baseEnd_6363375 : Nat := 3267469959804145999747877

theorem tailTrace_6363375 : CollatzResearch.WordTrace tailWord_6363375 prefixEnd_6363375 3267469959804145999747877 := by
  unfold tailWord_6363375
  simp only [CollatzResearch.WordTrace]
  refine ⟨232091353321586627772299579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154727568881057751848199719 232091353321586627772299579)
  ·
    refine ⟨348137029982379941658449369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232091353321586627772299579 348137029982379941658449369)
    ·
      refine ⟨261102772486784956243837027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 348137029982379941658449369 261102772486784956243837027)
      ·
        refine ⟨391654158730177434365755541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261102772486784956243837027 391654158730177434365755541)
        ·
          refine ⟨18358788690477067235894791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 391654158730177434365755541 18358788690477067235894791)
          ·
            refine ⟨27538183035715600853842187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18358788690477067235894791 27538183035715600853842187)
            ·
              refine ⟨41307274553573401280763281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27538183035715600853842187 41307274553573401280763281)
              ·
                refine ⟨30980455915180050960572461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41307274553573401280763281 30980455915180050960572461)
                ·
                  refine ⟨11617670968192519110214673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30980455915180050960572461 11617670968192519110214673)
                  ·
                    refine ⟨8713253226144389332661005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11617670968192519110214673 8713253226144389332661005)
                    ·
                      refine ⟨3267469959804145999747877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8713253226144389332661005 3267469959804145999747877)
                      ·
                        rfl

theorem cell23_6363375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 2, 3, 2, 3].length) (baseStart_6363375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6363375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6363375 prefixEnd_6363375 := by exact prefixLift 6363375
  have htrace : WordTrace (prefixWord ++ tailWord_6363375) baseStart_6363375 baseEnd_6363375 := by
    simpa [prefixWord, tailWord_6363375, baseEnd_6363375] using wordTrace_append hprefix tailTrace_6363375
  have hstable : (prefixWord ++ tailWord_6363375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6363375).length < 2 ^ (prefixWord ++ tailWord_6363375).sum := by decide
  have hdescent : baseEnd_6363375 < baseStart_6363375 := by decide
  rcases family_descends (prefixWord ++ tailWord_6363375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6363382 : List Nat := [5, 1, 1, 1, 1, 1, 4, 3, 2, 4]
def baseStart_6363382 : Nat := 118140960795 + 6363382 * 2 ^ 59
def prefixEnd_6363382 : Nat := 4983230072969 + 3 ^ 40 * 6363382 * 2
def baseEnd_6363382 : Nat := 1089157851389575824120115

theorem tailTrace_6363382 : CollatzResearch.WordTrace tailWord_6363382 prefixEnd_6363382 1089157851389575824120115 := by
  unfold tailWord_6363382
  simp only [CollatzResearch.WordTrace]
  refine ⟨14505725539535079247987775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 154727739088374178645202933 14505725539535079247987775)
  ·
    refine ⟨21758588309302618871981663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14505725539535079247987775 21758588309302618871981663)
    ·
      refine ⟨32637882463953928307972495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21758588309302618871981663 32637882463953928307972495)
      ·
        refine ⟨48956823695930892461958743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32637882463953928307972495 48956823695930892461958743)
        ·
          refine ⟨73435235543896338692938115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48956823695930892461958743 73435235543896338692938115)
          ·
            refine ⟨110152853315844508039407173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73435235543896338692938115 110152853315844508039407173)
            ·
              refine ⟨20653659996720845257388845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 110152853315844508039407173 20653659996720845257388845)
              ·
                refine ⟨7745122498770316971520817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20653659996720845257388845 7745122498770316971520817)
                ·
                  refine ⟨5808841874077737728640613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7745122498770316971520817 5808841874077737728640613)
                  ·
                    refine ⟨1089157851389575824120115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5808841874077737728640613 1089157851389575824120115)
                    ·
                      rfl

theorem cell23_6363382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 3, 2, 4].length) (baseStart_6363382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6363382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6363382 prefixEnd_6363382 := by exact prefixLift 6363382
  have htrace : WordTrace (prefixWord ++ tailWord_6363382) baseStart_6363382 baseEnd_6363382 := by
    simpa [prefixWord, tailWord_6363382, baseEnd_6363382] using wordTrace_append hprefix tailTrace_6363382
  have hstable : (prefixWord ++ tailWord_6363382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6363382).length < 2 ^ (prefixWord ++ tailWord_6363382).sum := by decide
  have hdescent : baseEnd_6363382 < baseStart_6363382 := by decide
  rcases family_descends (prefixWord ++ tailWord_6363382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6363406 : List Nat := [4, 1, 1, 2, 1, 2, 4, 3, 1, 2, 2]
def baseStart_6363406 : Nat := 118140960795 + 6363406 * 2 ^ 59
def prefixEnd_6363406 : Nat := 4983230072969 + 3 ^ 40 * 6363406 * 2
def baseEnd_6363406 : Nat := 3267485877704435378460235

theorem tailTrace_6363406 : CollatzResearch.WordTrace tailWord_6363406 prefixEnd_6363406 3267485877704435378460235 := by
  unfold tailWord_6363406
  simp only [CollatzResearch.WordTrace]
  refine ⟨29011560498059290008334759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154728322656316213377785381 29011560498059290008334759)
  ·
    refine ⟨43517340747088935012502139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29011560498059290008334759 43517340747088935012502139)
    ·
      refine ⟨65276011120633402518753209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43517340747088935012502139 65276011120633402518753209)
      ·
        refine ⟨48957008340475051889064907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65276011120633402518753209 48957008340475051889064907)
        ·
          refine ⟨73435512510712577833597361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48957008340475051889064907 73435512510712577833597361)
          ·
            refine ⟨55076634383034433375198021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73435512510712577833597361 55076634383034433375198021)
            ·
              refine ⟨10326868946818956257849629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55076634383034433375198021 10326868946818956257849629)
              ·
                refine ⟨3872575855057108596693611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10326868946818956257849629 3872575855057108596693611)
                ·
                  refine ⟨5808863782585662895040417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3872575855057108596693611 5808863782585662895040417)
                  ·
                    refine ⟨4356647836939247171280313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5808863782585662895040417 4356647836939247171280313)
                    ·
                      refine ⟨3267485877704435378460235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4356647836939247171280313 3267485877704435378460235)
                      ·
                        rfl

theorem cell23_6363406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 3, 1, 2, 2].length) (baseStart_6363406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6363406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6363406 prefixEnd_6363406 := by exact prefixLift 6363406
  have htrace : WordTrace (prefixWord ++ tailWord_6363406) baseStart_6363406 baseEnd_6363406 := by
    simpa [prefixWord, tailWord_6363406, baseEnd_6363406] using wordTrace_append hprefix tailTrace_6363406
  have hstable : (prefixWord ++ tailWord_6363406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6363406).length < 2 ^ (prefixWord ++ tailWord_6363406).sum := by decide
  have hdescent : baseEnd_6363406 < baseStart_6363406 := by decide
  rcases family_descends (prefixWord ++ tailWord_6363406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6363409 : List Nat := [1, 2, 2, 1, 1, 7, 2, 1, 1, 2, 3]
def baseStart_6363409 : Nat := 118140960795 + 6363409 * 2 ^ 59
def prefixEnd_6363409 : Nat := 4983230072969 + 3 ^ 40 * 6363409 * 2
def baseEnd_6363409 : Nat := 3267487418146398866722721

theorem tailTrace_6363409 : CollatzResearch.WordTrace tailWord_6363409 prefixEnd_6363409 3267487418146398866722721 := by
  unfold tailWord_6363409
  simp only [CollatzResearch.WordTrace]
  refine ⟨232092593403463451579037281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154728395602308967719358187 232092593403463451579037281)
  ·
    refine ⟨174069445052597588684277961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232092593403463451579037281 174069445052597588684277961)
    ·
      refine ⟨130552083789448191513208471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174069445052597588684277961 130552083789448191513208471)
      ·
        refine ⟨195828125684172287269812707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130552083789448191513208471 195828125684172287269812707)
        ·
          refine ⟨293742188526258430904719061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195828125684172287269812707 293742188526258430904719061)
          ·
            refine ⟨6884582543584181974329353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 293742188526258430904719061 6884582543584181974329353)
            ·
              refine ⟨5163436907688136480747015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6884582543584181974329353 5163436907688136480747015)
              ·
                refine ⟨7745155361532204721120523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5163436907688136480747015 7745155361532204721120523)
                ·
                  refine ⟨11617733042298307081680785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7745155361532204721120523 11617733042298307081680785)
                  ·
                    refine ⟨8713299781723730311260589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11617733042298307081680785 8713299781723730311260589)
                    ·
                      refine ⟨3267487418146398866722721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8713299781723730311260589 3267487418146398866722721)
                      ·
                        rfl

theorem cell23_6363409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 2, 1, 1, 2, 3].length) (baseStart_6363409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6363409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6363409 prefixEnd_6363409 := by exact prefixLift 6363409
  have htrace : WordTrace (prefixWord ++ tailWord_6363409) baseStart_6363409 baseEnd_6363409 := by
    simpa [prefixWord, tailWord_6363409, baseEnd_6363409] using wordTrace_append hprefix tailTrace_6363409
  have hstable : (prefixWord ++ tailWord_6363409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6363409).length < 2 ^ (prefixWord ++ tailWord_6363409).sum := by decide
  have hdescent : baseEnd_6363409 < baseStart_6363409 := by decide
  rcases family_descends (prefixWord ++ tailWord_6363409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6363449 : List Nat := [1, 2, 1, 6, 1, 1, 1, 4, 1, 3, 2]
def baseStart_6363449 : Nat := 118140960795 + 6363449 * 2 ^ 59
def prefixEnd_6363449 : Nat := 4983230072969 + 3 ^ 40 * 6363449 * 2
def baseEnd_6363449 : Nat := 3267507957372578710222537

theorem tailTrace_6363449 : CollatzResearch.WordTrace tailWord_6363449 prefixEnd_6363449 3267507957372578710222537 := by
  unfold tailWord_6363449
  simp only [CollatzResearch.WordTrace]
  refine ⟨232094052323318538410493401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154729368215545692273662267 232094052323318538410493401)
  ·
    refine ⟨174070539242488903807870051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232094052323318538410493401 174070539242488903807870051)
    ·
      refine ⟨261105808863733355711805077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174070539242488903807870051 261105808863733355711805077)
      ·
        refine ⟨12239334790487501048990863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 261105808863733355711805077 12239334790487501048990863)
        ·
          refine ⟨18359002185731251573486295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12239334790487501048990863 18359002185731251573486295)
          ·
            refine ⟨27538503278596877360229443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18359002185731251573486295 27538503278596877360229443)
            ·
              refine ⟨41307754917895316040344165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27538503278596877360229443 41307754917895316040344165)
              ·
                refine ⟨7745204047105371757564531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41307754917895316040344165 7745204047105371757564531)
                ·
                  refine ⟨11617806070658057636346797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7745204047105371757564531 11617806070658057636346797)
                  ·
                    refine ⟨4356677276496771613630049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11617806070658057636346797 4356677276496771613630049)
                    ·
                      refine ⟨3267507957372578710222537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4356677276496771613630049 3267507957372578710222537)
                      ·
                        rfl

theorem cell23_6363449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 4, 1, 3, 2].length) (baseStart_6363449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6363449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6363449 prefixEnd_6363449 := by exact prefixLift 6363449
  have htrace : WordTrace (prefixWord ++ tailWord_6363449) baseStart_6363449 baseEnd_6363449 := by
    simpa [prefixWord, tailWord_6363449, baseEnd_6363449] using wordTrace_append hprefix tailTrace_6363449
  have hstable : (prefixWord ++ tailWord_6363449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6363449).length < 2 ^ (prefixWord ++ tailWord_6363449).sum := by decide
  have hdescent : baseEnd_6363449 < baseStart_6363449 := by decide
  rcases family_descends (prefixWord ++ tailWord_6363449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6363479 : List Nat := [1, 1, 3, 2, 3, 1, 2, 4, 2, 2, 2]
def baseStart_6363479 : Nat := 118140960795 + 6363479 * 2 ^ 59
def prefixEnd_6363479 : Nat := 4983230072969 + 3 ^ 40 * 6363479 * 2
def baseEnd_6363479 : Nat := 3267523361792213592847399

theorem tailTrace_6363479 : CollatzResearch.WordTrace tailWord_6363479 prefixEnd_6363479 3267523361792213592847399 := by
  unfold tailWord_6363479
  simp only [CollatzResearch.WordTrace]
  refine ⟨232095146513209853534085491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154730097675473235689390327 232095146513209853534085491)
  ·
    refine ⟨348142719769814780301128237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232095146513209853534085491 348142719769814780301128237)
    ·
      refine ⟨130553519913680542612923089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 348142719769814780301128237 130553519913680542612923089)
      ·
        refine ⟨97915139935260406959692317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130553519913680542612923089 97915139935260406959692317)
        ·
          refine ⟨36718177475722652609884619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97915139935260406959692317 36718177475722652609884619)
          ·
            refine ⟨55077266213583978914826929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36718177475722652609884619 55077266213583978914826929)
            ·
              refine ⟨41307949660187984186120197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55077266213583978914826929 41307949660187984186120197)
              ·
                refine ⟨7745240561285247034897537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41307949660187984186120197 7745240561285247034897537)
                ·
                  refine ⟨5808930420963935276173153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7745240561285247034897537 5808930420963935276173153)
                  ·
                    refine ⟨4356697815722951457129865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5808930420963935276173153 4356697815722951457129865)
                    ·
                      refine ⟨3267523361792213592847399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4356697815722951457129865 3267523361792213592847399)
                      ·
                        rfl

theorem cell23_6363479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 4, 2, 2, 2].length) (baseStart_6363479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6363479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6363479 prefixEnd_6363479 := by exact prefixLift 6363479
  have htrace : WordTrace (prefixWord ++ tailWord_6363479) baseStart_6363479 baseEnd_6363479 := by
    simpa [prefixWord, tailWord_6363479, baseEnd_6363479] using wordTrace_append hprefix tailTrace_6363479
  have hstable : (prefixWord ++ tailWord_6363479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6363479).length < 2 ^ (prefixWord ++ tailWord_6363479).sum := by decide
  have hdescent : baseEnd_6363479 < baseStart_6363479 := by decide
  rcases family_descends (prefixWord ++ tailWord_6363479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6363496 : List Nat := [2, 1, 4, 2, 2, 2, 1, 3, 2, 2, 2]
def baseStart_6363496 : Nat := 118140960795 + 6363496 * 2 ^ 59
def prefixEnd_6363496 : Nat := 4983230072969 + 3 ^ 40 * 6363496 * 2
def baseEnd_6363496 : Nat := 3267532090963340026334821

theorem tailTrace_6363496 : CollatzResearch.WordTrace tailWord_6363496 prefixEnd_6363496 3267532090963340026334821 := by
  unfold tailWord_6363496
  simp only [CollatzResearch.WordTrace]
  refine ⟨116047883277074132718727171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154730511036098843624969561 116047883277074132718727171)
  ·
    refine ⟨174071824915611199078090757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116047883277074132718727171 174071824915611199078090757)
    ·
      refine ⟨32638467171677099827142017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 174071824915611199078090757 32638467171677099827142017)
      ·
        refine ⟨24478850378757824870356513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32638467171677099827142017 24478850378757824870356513)
        ·
          refine ⟨18359137784068368652767385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24478850378757824870356513 18359137784068368652767385)
          ·
            refine ⟨13769353338051276489575539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18359137784068368652767385 13769353338051276489575539)
            ·
              refine ⟨20654030007076914734363309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13769353338051276489575539 20654030007076914734363309)
              ·
                refine ⟨7745261252653843025386241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20654030007076914734363309 7745261252653843025386241)
                ·
                  refine ⟨5808945939490382269039681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7745261252653843025386241 5808945939490382269039681)
                  ·
                    refine ⟨4356709454617786701779761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5808945939490382269039681 4356709454617786701779761)
                    ·
                      refine ⟨3267532090963340026334821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4356709454617786701779761 3267532090963340026334821)
                      ·
                        rfl

theorem cell23_6363496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 3, 2, 2, 2].length) (baseStart_6363496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6363496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6363496 prefixEnd_6363496 := by exact prefixLift 6363496
  have htrace : WordTrace (prefixWord ++ tailWord_6363496) baseStart_6363496 baseEnd_6363496 := by
    simpa [prefixWord, tailWord_6363496, baseEnd_6363496] using wordTrace_append hprefix tailTrace_6363496
  have hstable : (prefixWord ++ tailWord_6363496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6363496).length < 2 ^ (prefixWord ++ tailWord_6363496).sum := by decide
  have hdescent : baseEnd_6363496 < baseStart_6363496 := by decide
  rcases family_descends (prefixWord ++ tailWord_6363496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6363515 : List Nat := [1, 1, 1, 1, 1, 7, 1, 3, 2, 5]
def baseStart_6363515 : Nat := 118140960795 + 6363515 * 2 ^ 59
def prefixEnd_6363515 : Nat := 4983230072969 + 3 ^ 40 * 6363515 * 2
def baseEnd_6363515 : Nat := 1089180615698591817332411

theorem tailTrace_6363515 : CollatzResearch.WordTrace tailWord_6363515 prefixEnd_6363515 1089180615698591817332411 := by
  unfold tailWord_6363515
  simp only [CollatzResearch.WordTrace]
  refine ⟨232096459541079431682395999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154730973027386287788263999 232096459541079431682395999)
  ·
    refine ⟨348144689311619147523593999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232096459541079431682395999 348144689311619147523593999)
    ·
      refine ⟨522217033967428721285390999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348144689311619147523593999 522217033967428721285390999)
      ·
        refine ⟨783325550951143081928086499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 522217033967428721285390999 783325550951143081928086499)
        ·
          refine ⟨1174988326426714622892129749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 783325550951143081928086499 1174988326426714622892129749)
          ·
            refine ⟨27538788900626123974034291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 1174988326426714622892129749 27538788900626123974034291)
            ·
              refine ⟨41308183350939185961051437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27538788900626123974034291 41308183350939185961051437)
              ·
                refine ⟨15490568756602194735394289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41308183350939185961051437 15490568756602194735394289)
                ·
                  refine ⟨11617926567451646051545717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15490568756602194735394289 11617926567451646051545717)
                  ·
                    refine ⟨1089180615698591817332411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11617926567451646051545717 1089180615698591817332411)
                    ·
                      rfl

theorem cell23_6363515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 3, 2, 5].length) (baseStart_6363515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6363515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6363515 prefixEnd_6363515 := by exact prefixLift 6363515
  have htrace : WordTrace (prefixWord ++ tailWord_6363515) baseStart_6363515 baseEnd_6363515 := by
    simpa [prefixWord, tailWord_6363515, baseEnd_6363515] using wordTrace_append hprefix tailTrace_6363515
  have hstable : (prefixWord ++ tailWord_6363515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6363515).length < 2 ^ (prefixWord ++ tailWord_6363515).sum := by decide
  have hdescent : baseEnd_6363515 < baseStart_6363515 := by decide
  rcases family_descends (prefixWord ++ tailWord_6363515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6363552 : List Nat := [2, 1, 1, 4, 1, 3, 1, 1, 1, 6, 2]
def baseStart_6363552 : Nat := 118140960795 + 6363552 * 2 ^ 59
def prefixEnd_6363552 : Nat := 4983230072969 + 3 ^ 40 * 6363552 * 2
def baseEnd_6363552 : Nat := 3267560845879991807234563

theorem tailTrace_6363552 : CollatzResearch.WordTrace tailWord_6363552 prefixEnd_6363552 3267560845879991807234563 := by
  unfold tailWord_6363552
  simp only [CollatzResearch.WordTrace]
  refine ⟨116048904520972693500746455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154731872694630258000995273 116048904520972693500746455)
  ·
    refine ⟨174073356781459040251119683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116048904520972693500746455 174073356781459040251119683)
    ·
      refine ⟨261110035172188560376679525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174073356781459040251119683 261110035172188560376679525)
      ·
        refine ⟨48958131594785355070627411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 261110035172188560376679525 48958131594785355070627411)
        ·
          refine ⟨73437197392178032605941117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48958131594785355070627411 73437197392178032605941117)
          ·
            refine ⟨27538949022066762227227919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73437197392178032605941117 27538949022066762227227919)
            ·
              refine ⟨41308423533100143340841879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27538949022066762227227919 41308423533100143340841879)
              ·
                refine ⟨61962635299650215011262819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41308423533100143340841879 61962635299650215011262819)
                ·
                  refine ⟨92943952949475322516894229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61962635299650215011262819 92943952949475322516894229)
                  ·
                    refine ⟨4356747794506655742979417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 92943952949475322516894229 4356747794506655742979417)
                    ·
                      refine ⟨3267560845879991807234563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4356747794506655742979417 3267560845879991807234563)
                      ·
                        rfl

theorem cell23_6363552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 1, 1, 6, 2].length) (baseStart_6363552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6363552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6363552 prefixEnd_6363552 := by exact prefixLift 6363552
  have htrace : WordTrace (prefixWord ++ tailWord_6363552) baseStart_6363552 baseEnd_6363552 := by
    simpa [prefixWord, tailWord_6363552, baseEnd_6363552] using wordTrace_append hprefix tailTrace_6363552
  have hstable : (prefixWord ++ tailWord_6363552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6363552).length < 2 ^ (prefixWord ++ tailWord_6363552).sum := by decide
  have hdescent : baseEnd_6363552 < baseStart_6363552 := by decide
  rcases family_descends (prefixWord ++ tailWord_6363552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6363569 : List Nat := [1, 2, 2, 4, 1, 4, 1, 1, 2, 1, 4]
def baseStart_6363569 : Nat := 118140960795 + 6363569 * 2 ^ 59
def prefixEnd_6363569 : Nat := 4983230072969 + 3 ^ 40 * 6363569 * 2
def baseEnd_6363569 : Nat := 3267569575051118240721985

theorem tailTrace_6363569 : CollatzResearch.WordTrace tailWord_6363569 prefixEnd_6363569 3267569575051118240721985 := by
  unfold tailWord_6363569
  simp only [CollatzResearch.WordTrace]
  refine ⟨232098429082883798904861761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154732286055255865936574507 232098429082883798904861761)
  ·
    refine ⟨174073821812162849178646321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232098429082883798904861761 174073821812162849178646321)
    ·
      refine ⟨130555366359122136883984741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174073821812162849178646321 130555366359122136883984741)
      ·
        refine ⟨24479131192335400665747139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 130555366359122136883984741 24479131192335400665747139)
        ·
          refine ⟨36718696788503100998620709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24479131192335400665747139 36718696788503100998620709)
          ·
            refine ⟨6884755647844331437241383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36718696788503100998620709 6884755647844331437241383)
            ·
              refine ⟨10327133471766497155862075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6884755647844331437241383 10327133471766497155862075)
              ·
                refine ⟨15490700207649745733793113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10327133471766497155862075 15490700207649745733793113)
                ·
                  refine ⟨11618025155737309300344835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15490700207649745733793113 11618025155737309300344835)
                  ·
                    refine ⟨17427037733605963950517253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11618025155737309300344835 17427037733605963950517253)
                    ·
                      refine ⟨3267569575051118240721985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17427037733605963950517253 3267569575051118240721985)
                      ·
                        rfl

theorem cell23_6363569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 1, 2, 1, 4].length) (baseStart_6363569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6363569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6363569 prefixEnd_6363569 := by exact prefixLift 6363569
  have htrace : WordTrace (prefixWord ++ tailWord_6363569) baseStart_6363569 baseEnd_6363569 := by
    simpa [prefixWord, tailWord_6363569, baseEnd_6363569] using wordTrace_append hprefix tailTrace_6363569
  have hstable : (prefixWord ++ tailWord_6363569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6363569).length < 2 ^ (prefixWord ++ tailWord_6363569).sum := by decide
  have hdescent : baseEnd_6363569 < baseStart_6363569 := by decide
  rcases family_descends (prefixWord ++ tailWord_6363569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6363592 : List Nat := [2, 1, 3, 1, 3, 2, 3, 2, 6]
def baseStart_6363592 : Nat := 118140960795 + 6363592 * 2 ^ 59
def prefixEnd_6363592 : Nat := 4983230072969 + 3 ^ 40 * 6363592 * 2
def baseEnd_6363592 : Nat := 363064598345130183414931

theorem tailTrace_6363592 : CollatzResearch.WordTrace tailWord_6363592 prefixEnd_6363592 363064598345130183414931 := by
  unfold tailWord_6363592
  simp only [CollatzResearch.WordTrace]
  refine ⟨116049633980900236916474515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154732845307866982555299353 116049633980900236916474515)
  ·
    refine ⟨174074450971350355374711773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116049633980900236916474515 174074450971350355374711773)
    ·
      refine ⟨65277919114256383265516915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174074450971350355374711773 65277919114256383265516915)
      ·
        refine ⟨97916878671384574898275373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65277919114256383265516915 97916878671384574898275373)
        ·
          refine ⟨36718829501769215586853265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97916878671384574898275373 36718829501769215586853265)
          ·
            refine ⟨27539122126326911690139949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36718829501769215586853265 27539122126326911690139949)
            ·
              refine ⟨10327170797372591883802481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27539122126326911690139949 10327170797372591883802481)
              ·
                refine ⟨7745378098029443912851861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10327170797372591883802481 7745378098029443912851861)
                ·
                  refine ⟨363064598345130183414931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7745378098029443912851861 363064598345130183414931)
                  ·
                    rfl

theorem cell23_6363592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 2, 6].length) (baseStart_6363592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6363592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6363592 prefixEnd_6363592 := by exact prefixLift 6363592
  have htrace : WordTrace (prefixWord ++ tailWord_6363592) baseStart_6363592 baseEnd_6363592 := by
    simpa [prefixWord, tailWord_6363592, baseEnd_6363592] using wordTrace_append hprefix tailTrace_6363592
  have hstable : (prefixWord ++ tailWord_6363592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6363592).length < 2 ^ (prefixWord ++ tailWord_6363592).sum := by decide
  have hdescent : baseEnd_6363592 < baseStart_6363592 := by decide
  rcases family_descends (prefixWord ++ tailWord_6363592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6363635 : List Nat := [1, 1, 1, 2, 2, 2, 4, 1, 3, 6]
def baseStart_6363635 : Nat := 118140960795 + 6363635 * 2 ^ 59
def prefixEnd_6363635 : Nat := 4983230072969 + 3 ^ 40 * 6363635 * 2
def baseEnd_6363635 : Nat := 1089201154924771660832227

theorem tailTrace_6363635 : CollatzResearch.WordTrace tailWord_6363635 prefixEnd_6363635 1089201154924771660832227 := by
  unfold tailWord_6363635
  simp only [CollatzResearch.WordTrace]
  refine ⟨232100836300644692176764359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154733890867096461451176239 232100836300644692176764359)
  ·
    refine ⟨348151254450967038265146539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232100836300644692176764359 348151254450967038265146539)
    ·
      refine ⟨522226881676450557397719809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348151254450967038265146539 522226881676450557397719809)
      ·
        refine ⟨391670161257337918048289857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 522226881676450557397719809 391670161257337918048289857)
        ·
          refine ⟨293752620943003438536217393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 391670161257337918048289857 293752620943003438536217393)
          ·
            refine ⟨220314465707252578902163045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 293752620943003438536217393 220314465707252578902163045)
            ·
              refine ⟨41308962320109858544155571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 220314465707252578902163045 41308962320109858544155571)
              ·
                refine ⟨61963443480164787816233357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41308962320109858544155571 61963443480164787816233357)
                ·
                  refine ⟨23236291305061795431087509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61963443480164787816233357 23236291305061795431087509)
                  ·
                    refine ⟨1089201154924771660832227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23236291305061795431087509 1089201154924771660832227)
                    ·
                      rfl

theorem cell23_6363635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 1, 3, 6].length) (baseStart_6363635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6363635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6363635 prefixEnd_6363635 := by exact prefixLift 6363635
  have htrace : WordTrace (prefixWord ++ tailWord_6363635) baseStart_6363635 baseEnd_6363635 := by
    simpa [prefixWord, tailWord_6363635, baseEnd_6363635] using wordTrace_append hprefix tailTrace_6363635
  have hstable : (prefixWord ++ tailWord_6363635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6363635).length < 2 ^ (prefixWord ++ tailWord_6363635).sum := by decide
  have hdescent : baseEnd_6363635 < baseStart_6363635 := by decide
  rcases family_descends (prefixWord ++ tailWord_6363635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6363669 : List Nat := [1, 3, 2, 1, 3, 1, 3, 3, 2, 4]
def baseStart_6363669 : Nat := 118140960795 + 6363669 * 2 ^ 59
def prefixEnd_6363669 : Nat := 4983230072969 + 3 ^ 40 * 6363669 * 2
def baseEnd_6363669 : Nat := 1089206974372189283157175

theorem tailTrace_6363669 : CollatzResearch.WordTrace tailWord_6363669 prefixEnd_6363669 1089206974372189283157175 := by
  unfold tailWord_6363669
  simp only [CollatzResearch.WordTrace]
  refine ⟨232102076382521515983502061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154734717588347677322334707 232102076382521515983502061)
  ·
    refine ⟨87038278643445568493813273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 232102076382521515983502061 87038278643445568493813273)
    ·
      refine ⟨65278708982584176370359955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87038278643445568493813273 65278708982584176370359955)
      ·
        refine ⟨97918063473876264555539933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65278708982584176370359955 97918063473876264555539933)
        ·
          refine ⟨36719273802703599208327475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97918063473876264555539933 36719273802703599208327475)
          ·
            refine ⟨55078910704055398812491213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36719273802703599208327475 55078910704055398812491213)
            ·
              refine ⟨20654591514020774554684205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55078910704055398812491213 20654591514020774554684205)
              ·
                refine ⟨7745471817757790458006577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20654591514020774554684205 7745471817757790458006577)
                ·
                  refine ⟨5809103863318342843504933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7745471817757790458006577 5809103863318342843504933)
                  ·
                    refine ⟨1089206974372189283157175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5809103863318342843504933 1089206974372189283157175)
                    ·
                      rfl

theorem cell23_6363669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 3, 2, 4].length) (baseStart_6363669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6363669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6363669 prefixEnd_6363669 := by exact prefixLift 6363669
  have htrace : WordTrace (prefixWord ++ tailWord_6363669) baseStart_6363669 baseEnd_6363669 := by
    simpa [prefixWord, tailWord_6363669, baseEnd_6363669] using wordTrace_append hprefix tailTrace_6363669
  have hstable : (prefixWord ++ tailWord_6363669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6363669).length < 2 ^ (prefixWord ++ tailWord_6363669).sum := by decide
  have hdescent : baseEnd_6363669 < baseStart_6363669 := by decide
  rcases family_descends (prefixWord ++ tailWord_6363669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6363672 : List Nat := [2, 1, 2, 3, 3, 1, 2, 1, 1, 1, 6]
def baseStart_6363672 : Nat := 118140960795 + 6363672 * 2 ^ 59
def prefixEnd_6363672 : Nat := 4983230072969 + 3 ^ 40 * 6363672 * 2
def baseEnd_6363672 : Nat := 3267622463558531337734011

theorem tailTrace_6363672 : CollatzResearch.WordTrace tailWord_6363672 prefixEnd_6363672 3267622463558531337734011 := by
  unfold tailWord_6363672
  simp only [CollatzResearch.WordTrace]
  refine ⟨116051092900755323747930635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154734790534340431663907513 116051092900755323747930635)
  ·
    refine ⟨174076639351132985621895953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116051092900755323747930635 174076639351132985621895953)
    ·
      refine ⟨130557479513349739216421965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174076639351132985621895953 130557479513349739216421965)
      ·
        refine ⟨48959054817506152206158237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130557479513349739216421965 48959054817506152206158237)
        ·
          refine ⟨18359645556564807077309339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48959054817506152206158237 18359645556564807077309339)
          ·
            refine ⟨27539468334847210615964009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18359645556564807077309339 27539468334847210615964009)
            ·
              refine ⟨20654601251135407961973007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27539468334847210615964009 20654601251135407961973007)
              ·
                refine ⟨30981901876703111942959511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20654601251135407961973007 30981901876703111942959511)
                ·
                  refine ⟨46472852815054667914439267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30981901876703111942959511 46472852815054667914439267)
                  ·
                    refine ⟨69709279222582001871658901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46472852815054667914439267 69709279222582001871658901)
                    ·
                      refine ⟨3267622463558531337734011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69709279222582001871658901 3267622463558531337734011)
                      ·
                        rfl

theorem cell23_6363672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 1, 1, 1, 6].length) (baseStart_6363672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6363672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6363672 prefixEnd_6363672 := by exact prefixLift 6363672
  have htrace : WordTrace (prefixWord ++ tailWord_6363672) baseStart_6363672 baseEnd_6363672 := by
    simpa [prefixWord, tailWord_6363672, baseEnd_6363672] using wordTrace_append hprefix tailTrace_6363672
  have hstable : (prefixWord ++ tailWord_6363672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6363672).length < 2 ^ (prefixWord ++ tailWord_6363672).sum := by decide
  have hdescent : baseEnd_6363672 < baseStart_6363672 := by decide
  rcases family_descends (prefixWord ++ tailWord_6363672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6363676 : List Nat := [2, 2, 3, 1, 2, 4, 1, 2, 1, 1, 4]
def baseStart_6363676 : Nat := 118140960795 + 6363676 * 2 ^ 59
def prefixEnd_6363676 : Nat := 4983230072969 + 3 ^ 40 * 6363676 * 2
def baseEnd_6363676 : Nat := 3267624517481149322083993

theorem tailTrace_6363676 : CollatzResearch.WordTrace tailWord_6363676 prefixEnd_6363676 3267624517481149322083993 := by
  unfold tailWord_6363676
  simp only [CollatzResearch.WordTrace]
  refine ⟨116051165846748078089503441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154734887795664104119337921 116051165846748078089503441)
  ·
    refine ⟨87038374385061058567127581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116051165846748078089503441 87038374385061058567127581)
    ·
      refine ⟨32639390394397896962672843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87038374385061058567127581 32639390394397896962672843)
      ·
        refine ⟨48959085591596845444009265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32639390394397896962672843 48959085591596845444009265)
        ·
          refine ⟨36719314193697634083006949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48959085591596845444009265 36719314193697634083006949)
          ·
            refine ⟨6884871411318306390563803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36719314193697634083006949 6884871411318306390563803)
            ·
              refine ⟨10327307116977459585845705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6884871411318306390563803 10327307116977459585845705)
              ·
                refine ⟨7745480337733094689384279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10327307116977459585845705 7745480337733094689384279)
                ·
                  refine ⟨11618220506599642034076419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7745480337733094689384279 11618220506599642034076419)
                  ·
                    refine ⟨17427330759899463051114629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11618220506599642034076419 17427330759899463051114629)
                    ·
                      refine ⟨3267624517481149322083993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17427330759899463051114629 3267624517481149322083993)
                      ·
                        rfl

theorem cell23_6363676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 2, 1, 1, 4].length) (baseStart_6363676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6363676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6363676 prefixEnd_6363676 := by exact prefixLift 6363676
  have htrace : WordTrace (prefixWord ++ tailWord_6363676) baseStart_6363676 baseEnd_6363676 := by
    simpa [prefixWord, tailWord_6363676, baseEnd_6363676] using wordTrace_append hprefix tailTrace_6363676
  have hstable : (prefixWord ++ tailWord_6363676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6363676).length < 2 ^ (prefixWord ++ tailWord_6363676).sum := by decide
  have hdescent : baseEnd_6363676 < baseStart_6363676 := by decide
  rcases family_descends (prefixWord ++ tailWord_6363676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6363695 : List Nat := [1, 1, 2, 1, 2, 1, 1, 1, 6, 7]
def baseStart_6363695 : Nat := 118140960795 + 6363695 * 2 ^ 59
def prefixEnd_6363695 : Nat := 4983230072969 + 3 ^ 40 * 6363695 * 2
def baseEnd_6363695 : Nat := 1089211424537861582582135

theorem tailTrace_6363695 : CollatzResearch.WordTrace tailWord_6363695 prefixEnd_6363695 1089211424537861582582135 := by
  unfold tailWord_6363695
  simp only [CollatzResearch.WordTrace]
  refine ⟨232103024680427322423948539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154735349786951548282632359 232103024680427322423948539)
  ·
    refine ⟨348154537020640983635922809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232103024680427322423948539 348154537020640983635922809)
    ·
      refine ⟨261115902765480737726942107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 348154537020640983635922809 261115902765480737726942107)
      ·
        refine ⟨391673854148221106590413161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261115902765480737726942107 391673854148221106590413161)
        ·
          refine ⟨293755390611165829942809871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 391673854148221106590413161 293755390611165829942809871)
          ·
            refine ⟨440633085916748744914214807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 293755390611165829942809871 440633085916748744914214807)
            ·
              refine ⟨660949628875123117371322211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 440633085916748744914214807 660949628875123117371322211)
              ·
                refine ⟨991424443312684676056983317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 660949628875123117371322211 991424443312684676056983317)
                ·
                  refine ⟨46473020780282094190171093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 991424443312684676056983317 46473020780282094190171093)
                  ·
                    refine ⟨1089211424537861582582135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46473020780282094190171093 1089211424537861582582135)
                    ·
                      rfl

theorem cell23_6363695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 6, 7].length) (baseStart_6363695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6363695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6363695 prefixEnd_6363695 := by exact prefixLift 6363695
  have htrace : WordTrace (prefixWord ++ tailWord_6363695) baseStart_6363695 baseEnd_6363695 := by
    simpa [prefixWord, tailWord_6363695, baseEnd_6363695] using wordTrace_append hprefix tailTrace_6363695
  have hstable : (prefixWord ++ tailWord_6363695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6363695).length < 2 ^ (prefixWord ++ tailWord_6363695).sum := by decide
  have hdescent : baseEnd_6363695 < baseStart_6363695 := by decide
  rcases family_descends (prefixWord ++ tailWord_6363695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6363726 : List Nat := [4, 1, 1, 1, 1, 2, 4, 3, 2, 1, 3]
def baseStart_6363726 : Nat := 118140960795 + 6363726 * 2 ^ 59
def prefixEnd_6363726 : Nat := 4983230072969 + 3 ^ 40 * 6363726 * 2
def baseEnd_6363726 : Nat := 3267650191513874126458763

theorem tailTrace_6363726 : CollatzResearch.WordTrace tailWord_6363726 prefixEnd_6363726 3267650191513874126458763 := by
  unfold tailWord_6363726
  simp only [CollatzResearch.WordTrace]
  refine ⟨29013019417914376839790879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154736103562210009812218021 29013019417914376839790879)
  ·
    refine ⟨43519529126871565259686319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29013019417914376839790879 43519529126871565259686319)
    ·
      refine ⟨65279293690307347889529479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43519529126871565259686319 65279293690307347889529479)
      ·
        refine ⟨97918940535461021834294219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65279293690307347889529479 97918940535461021834294219)
        ·
          refine ⟨146878410803191532751441329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97918940535461021834294219 146878410803191532751441329)
          ·
            refine ⟨110158808102393649563580997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146878410803191532751441329 110158808102393649563580997)
            ·
              refine ⟨20654776519198809293171437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 110158808102393649563580997 20654776519198809293171437)
              ·
                refine ⟨7745541194699553484939289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20654776519198809293171437 7745541194699553484939289)
                ·
                  refine ⟨5809155896024665113704467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7745541194699553484939289 5809155896024665113704467)
                  ·
                    refine ⟨8713733844036997670556701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5809155896024665113704467 8713733844036997670556701)
                    ·
                      refine ⟨3267650191513874126458763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8713733844036997670556701 3267650191513874126458763)
                      ·
                        rfl

theorem cell23_6363726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 3, 2, 1, 3].length) (baseStart_6363726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6363726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6363726 prefixEnd_6363726 := by exact prefixLift 6363726
  have htrace : WordTrace (prefixWord ++ tailWord_6363726) baseStart_6363726 baseEnd_6363726 := by
    simpa [prefixWord, tailWord_6363726, baseEnd_6363726] using wordTrace_append hprefix tailTrace_6363726
  have hstable : (prefixWord ++ tailWord_6363726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6363726).length < 2 ^ (prefixWord ++ tailWord_6363726).sum := by decide
  have hdescent : baseEnd_6363726 < baseStart_6363726 := by decide
  rcases family_descends (prefixWord ++ tailWord_6363726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6363760 : List Nat := [2, 1, 1, 1, 8, 1, 1, 2, 2, 1, 3]
def baseStart_6363760 : Nat := 118140960795 + 6363760 * 2 ^ 59
def prefixEnd_6363760 : Nat := 4983230072969 + 3 ^ 40 * 6363760 * 2
def baseEnd_6363760 : Nat := 3267667649856126993433607

theorem tailTrace_6363760 : CollatzResearch.WordTrace tailWord_6363760 prefixEnd_6363760 3267667649856126993433607 := by
  unfold tailWord_6363760
  simp only [CollatzResearch.WordTrace]
  refine ⟨116052697712595919262532367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154736930283461225683376489 116052697712595919262532367)
  ·
    refine ⟨174079046568893878893798551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116052697712595919262532367 174079046568893878893798551)
    ·
      refine ⟨261118569853340818340697827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174079046568893878893798551 261118569853340818340697827)
      ·
        refine ⟨391677854780011227511046741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261118569853340818340697827 391677854780011227511046741)
        ·
          refine ⟨4589974860703256572395079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 391677854780011227511046741 4589974860703256572395079)
          ·
            refine ⟨6884962291054884858592619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4589974860703256572395079 6884962291054884858592619)
            ·
              refine ⟨10327443436582327287888929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6884962291054884858592619 10327443436582327287888929)
              ·
                refine ⟨7745582577436745465916697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10327443436582327287888929 7745582577436745465916697)
                ·
                  refine ⟨5809186933077559099437523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7745582577436745465916697 5809186933077559099437523)
                  ·
                    refine ⟨8713780399616338649156285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5809186933077559099437523 8713780399616338649156285)
                    ·
                      refine ⟨3267667649856126993433607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8713780399616338649156285 3267667649856126993433607)
                      ·
                        rfl

theorem cell23_6363760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 2, 2, 1, 3].length) (baseStart_6363760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6363760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6363760 prefixEnd_6363760 := by exact prefixLift 6363760
  have htrace : WordTrace (prefixWord ++ tailWord_6363760) baseStart_6363760 baseEnd_6363760 := by
    simpa [prefixWord, tailWord_6363760, baseEnd_6363760] using wordTrace_append hprefix tailTrace_6363760
  have hstable : (prefixWord ++ tailWord_6363760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6363760).length < 2 ^ (prefixWord ++ tailWord_6363760).sum := by decide
  have hdescent : baseEnd_6363760 < baseStart_6363760 := by decide
  rcases family_descends (prefixWord ++ tailWord_6363760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6363772 : List Nat := [2, 2, 2, 1, 1, 2, 3, 3, 7]
def baseStart_6363772 : Nat := 118140960795 + 6363772 * 2 ^ 59
def prefixEnd_6363772 : Nat := 4983230072969 + 3 ^ 40 * 6363772 * 2
def baseEnd_6363772 : Nat := 363074867958220105164839

theorem tailTrace_6363772 : CollatzResearch.WordTrace tailWord_6363772 prefixEnd_6363772 363074867958220105164839 := by
  unfold tailWord_6363772
  simp only [CollatzResearch.WordTrace]
  refine ⟨116052916550574182287250785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154737222067432243049667713 116052916550574182287250785)
  ·
    refine ⟨87039687412930636715438089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116052916550574182287250785 87039687412930636715438089)
    ·
      refine ⟨65279765559697977536578567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87039687412930636715438089 65279765559697977536578567)
      ·
        refine ⟨97919648339546966304867851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65279765559697977536578567 97919648339546966304867851)
        ·
          refine ⟨146879472509320449457301777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97919648339546966304867851 146879472509320449457301777)
          ·
            refine ⟨110159604381990337092976333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146879472509320449457301777 110159604381990337092976333)
            ·
              refine ⟨41309851643246376409866125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110159604381990337092976333 41309851643246376409866125)
              ·
                refine ⟨15491194366217391153699797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41309851643246376409866125 15491194366217391153699797)
                ·
                  refine ⟨363074867958220105164839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15491194366217391153699797 363074867958220105164839)
                  ·
                    rfl

theorem cell23_6363772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 3, 7].length) (baseStart_6363772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6363772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6363772 prefixEnd_6363772 := by exact prefixLift 6363772
  have htrace : WordTrace (prefixWord ++ tailWord_6363772) baseStart_6363772 baseEnd_6363772 := by
    simpa [prefixWord, tailWord_6363772, baseEnd_6363772] using wordTrace_append hprefix tailTrace_6363772
  have hstable : (prefixWord ++ tailWord_6363772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6363772).length < 2 ^ (prefixWord ++ tailWord_6363772).sum := by decide
  have hdescent : baseEnd_6363772 < baseStart_6363772 := by decide
  rcases family_descends (prefixWord ++ tailWord_6363772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6363829 : List Nat := [1, 3, 3, 3, 1, 1, 1, 1, 1, 1, 7]
def baseStart_6363829 : Nat := 118140960795 + 6363829 * 2 ^ 59
def prefixEnd_6363829 : Nat := 4983230072969 + 3 ^ 40 * 6363829 * 2
def baseEnd_6363829 : Nat := 3267703080021287223470789

theorem tailTrace_6363829 : CollatzResearch.WordTrace tailWord_6363829 prefixEnd_6363829 3267703080021287223470789 := by
  unfold tailWord_6363829
  simp only [CollatzResearch.WordTrace]
  refine ⟨232107912061941863309326541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154738608041294575539551027 232107912061941863309326541)
  ·
    refine ⟨87040467023228198740997453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 232107912061941863309326541 87040467023228198740997453)
    ·
      refine ⟨32640175133710574527874045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87040467023228198740997453 32640175133710574527874045)
      ·
        refine ⟨12240065675141465447952767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32640175133710574527874045 12240065675141465447952767)
        ·
          refine ⟨18360098512712198171929151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12240065675141465447952767 18360098512712198171929151)
          ·
            refine ⟨27540147769068297257893727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18360098512712198171929151 27540147769068297257893727)
            ·
              refine ⟨41310221653602445886840591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27540147769068297257893727 41310221653602445886840591)
              ·
                refine ⟨61965332480403668830260887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41310221653602445886840591 61965332480403668830260887)
                ·
                  refine ⟨92947998720605503245391331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61965332480403668830260887 92947998720605503245391331)
                  ·
                    refine ⟨139421998080908254868086997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 92947998720605503245391331 139421998080908254868086997)
                    ·
                      refine ⟨3267703080021287223470789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 139421998080908254868086997 3267703080021287223470789)
                      ·
                        rfl

theorem cell23_6363829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_6363829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6363829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6363829 prefixEnd_6363829 := by exact prefixLift 6363829
  have htrace : WordTrace (prefixWord ++ tailWord_6363829) baseStart_6363829 baseEnd_6363829 := by
    simpa [prefixWord, tailWord_6363829, baseEnd_6363829] using wordTrace_append hprefix tailTrace_6363829
  have hstable : (prefixWord ++ tailWord_6363829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6363829).length < 2 ^ (prefixWord ++ tailWord_6363829).sum := by decide
  have hdescent : baseEnd_6363829 < baseStart_6363829 := by decide
  rcases family_descends (prefixWord ++ tailWord_6363829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6363876 : List Nat := [2, 3, 1, 1, 1, 4, 2, 2, 2, 2, 3]
def baseStart_6363876 : Nat := 118140960795 + 6363876 * 2 ^ 59
def prefixEnd_6363876 : Nat := 4983230072969 + 3 ^ 40 * 6363876 * 2
def baseEnd_6363876 : Nat := 3267727213612048539583073

theorem tailTrace_6363876 : CollatzResearch.WordTrace tailWord_6363876 prefixEnd_6363876 3267727213612048539583073 := by
  unfold tailWord_6363876
  simp only [CollatzResearch.WordTrace]
  refine ⟨116054813146385795168143741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154739750861847726890858321 116054813146385795168143741)
  ·
    refine ⟨43520554929894673188053903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116054813146385795168143741 43520554929894673188053903)
    ·
      refine ⟨65280832394842009782080855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43520554929894673188053903 65280832394842009782080855)
      ·
        refine ⟨97921248592263014673121283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65280832394842009782080855 97921248592263014673121283)
        ·
          refine ⟨146881872888394522009681925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97921248592263014673121283 146881872888394522009681925)
          ·
            refine ⟨27540351166573972876815361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 146881872888394522009681925 27540351166573972876815361)
            ·
              refine ⟨20655263374930479657611521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27540351166573972876815361 20655263374930479657611521)
              ·
                refine ⟨15491447531197859743208641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20655263374930479657611521 15491447531197859743208641)
                ·
                  refine ⟨11618585648398394807406481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15491447531197859743208641 11618585648398394807406481)
                  ·
                    refine ⟨8713939236298796105554861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11618585648398394807406481 8713939236298796105554861)
                    ·
                      refine ⟨3267727213612048539583073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8713939236298796105554861 3267727213612048539583073)
                      ·
                        rfl

theorem cell23_6363876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 2, 2, 2, 3].length) (baseStart_6363876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6363876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6363876 prefixEnd_6363876 := by exact prefixLift 6363876
  have htrace : WordTrace (prefixWord ++ tailWord_6363876) baseStart_6363876 baseEnd_6363876 := by
    simpa [prefixWord, tailWord_6363876, baseEnd_6363876] using wordTrace_append hprefix tailTrace_6363876
  have hstable : (prefixWord ++ tailWord_6363876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6363876).length < 2 ^ (prefixWord ++ tailWord_6363876).sum := by decide
  have hdescent : baseEnd_6363876 < baseStart_6363876 := by decide
  rcases family_descends (prefixWord ++ tailWord_6363876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6363929 : List Nat := [1, 2, 1, 2, 1, 1, 1, 4, 5, 1, 4]
def baseStart_6363929 : Nat := 118140960795 + 6363929 * 2 ^ 59
def prefixEnd_6363929 : Nat := 4983230072969 + 3 ^ 40 * 6363929 * 2
def baseEnd_6363929 : Nat := 3267754428086736832220329

theorem tailTrace_6363929 : CollatzResearch.WordTrace tailWord_6363929 prefixEnd_6363929 3267754428086736832220329 := by
  unfold tailWord_6363929
  simp only [CollatzResearch.WordTrace]
  refine ⟨232111559361579580387966841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154741039574386386925311227 232111559361579580387966841)
  ·
    refine ⟨174083669521184685290975131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232111559361579580387966841 174083669521184685290975131)
    ·
      refine ⟨261125504281777027936462697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174083669521184685290975131 261125504281777027936462697)
      ·
        refine ⟨195844128211332770952347023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 261125504281777027936462697 195844128211332770952347023)
        ·
          refine ⟨293766192316999156428520535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195844128211332770952347023 293766192316999156428520535)
          ·
            refine ⟨440649288475498734642780803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 293766192316999156428520535 440649288475498734642780803)
            ·
              refine ⟨660973932713248101964171205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 440649288475498734642780803 660973932713248101964171205)
              ·
                refine ⟨123932612383734019118282101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 660973932713248101964171205 123932612383734019118282101)
                ·
                  refine ⟨11618682410975064292338947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 123932612383734019118282101 11618682410975064292338947)
                  ·
                    refine ⟨17428023616462596438508421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11618682410975064292338947 17428023616462596438508421)
                    ·
                      refine ⟨3267754428086736832220329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17428023616462596438508421 3267754428086736832220329)
                      ·
                        rfl

theorem cell23_6363929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 5, 1, 4].length) (baseStart_6363929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6363929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6363929 prefixEnd_6363929 := by exact prefixLift 6363929
  have htrace : WordTrace (prefixWord ++ tailWord_6363929) baseStart_6363929 baseEnd_6363929 := by
    simpa [prefixWord, tailWord_6363929, baseEnd_6363929] using wordTrace_append hprefix tailTrace_6363929
  have hstable : (prefixWord ++ tailWord_6363929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6363929).length < 2 ^ (prefixWord ++ tailWord_6363929).sum := by decide
  have hdescent : baseEnd_6363929 < baseStart_6363929 := by decide
  rcases family_descends (prefixWord ++ tailWord_6363929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6363940 : List Nat := [2, 3, 1, 3, 3, 1, 2, 1, 3, 1, 3]
def baseStart_6363940 : Nat := 118140960795 + 6363940 * 2 ^ 59
def prefixEnd_6363940 : Nat := 4983230072969 + 3 ^ 40 * 6363940 * 2
def baseEnd_6363940 : Nat := 3267760076373936289182779

theorem tailTrace_6363940 : CollatzResearch.WordTrace tailWord_6363940 prefixEnd_6363940 3267760076373936289182779 := by
  unfold tailWord_6363940
  simp only [CollatzResearch.WordTrace]
  refine ⟨116055980282269864633308637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154741307043026486177744849 116055980282269864633308637)
  ·
    refine ⟨43520992605851199237490739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116055980282269864633308637 43520992605851199237490739)
    ·
      refine ⟨65281488908776798856236109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43520992605851199237490739 65281488908776798856236109)
      ·
        refine ⟨24480558340791299571088541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65281488908776798856236109 24480558340791299571088541)
        ·
          refine ⟨9180209377796737339158203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24480558340791299571088541 9180209377796737339158203)
          ·
            refine ⟨13770314066695106008737305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9180209377796737339158203 13770314066695106008737305)
            ·
              refine ⟨10327735550021329506552979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13770314066695106008737305 10327735550021329506552979)
              ·
                refine ⟨15491603325031994259829469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10327735550021329506552979 15491603325031994259829469)
                ·
                  refine ⟨5809351246886997847436051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15491603325031994259829469 5809351246886997847436051)
                  ·
                    refine ⟨8714026870330496771154077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5809351246886997847436051 8714026870330496771154077)
                    ·
                      refine ⟨3267760076373936289182779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8714026870330496771154077 3267760076373936289182779)
                      ·
                        rfl

theorem cell23_6363940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 1, 3, 1, 3].length) (baseStart_6363940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6363940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6363940 prefixEnd_6363940 := by exact prefixLift 6363940
  have htrace : WordTrace (prefixWord ++ tailWord_6363940) baseStart_6363940 baseEnd_6363940 := by
    simpa [prefixWord, tailWord_6363940, baseEnd_6363940] using wordTrace_append hprefix tailTrace_6363940
  have hstable : (prefixWord ++ tailWord_6363940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6363940).length < 2 ^ (prefixWord ++ tailWord_6363940).sum := by decide
  have hdescent : baseEnd_6363940 < baseStart_6363940 := by decide
  rcases family_descends (prefixWord ++ tailWord_6363940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6363959 : List Nat := [1, 1, 3, 1, 2, 1, 5, 1, 1, 1, 6]
def baseStart_6363959 : Nat := 118140960795 + 6363959 * 2 ^ 59
def prefixEnd_6363959 : Nat := 4983230072969 + 3 ^ 40 * 6363959 * 2
def baseEnd_6363959 : Nat := 3267769832506371714845191

theorem tailTrace_6363959 : CollatzResearch.WordTrace tailWord_6363959 prefixEnd_6363959 3267769832506371714845191 := by
  unfold tailWord_6363959
  simp only [CollatzResearch.WordTrace]
  refine ⟨232112653551470895511558931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154741769034313930341039287 232112653551470895511558931)
  ·
    refine ⟨348168980327206343267338397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232112653551470895511558931 348168980327206343267338397)
    ·
      refine ⟨130563367622702378725251899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 348168980327206343267338397 130563367622702378725251899)
      ·
        refine ⟨195845051434053568087877849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130563367622702378725251899 195845051434053568087877849)
        ·
          refine ⟨146883788575540176065908387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 195845051434053568087877849 146883788575540176065908387)
          ·
            refine ⟨220325682863310264098862581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146883788575540176065908387 220325682863310264098862581)
            ·
              refine ⟨20655532768435337259268367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 220325682863310264098862581 20655532768435337259268367)
              ·
                refine ⟨30983299152653005888902551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20655532768435337259268367 30983299152653005888902551)
                ·
                  refine ⟨46474948728979508833353827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30983299152653005888902551 46474948728979508833353827)
                  ·
                    refine ⟨69712423093469263250030741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46474948728979508833353827 69712423093469263250030741)
                    ·
                      refine ⟨3267769832506371714845191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69712423093469263250030741 3267769832506371714845191)
                      ·
                        rfl

theorem cell23_6363959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 1, 1, 1, 6].length) (baseStart_6363959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6363959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6363959 prefixEnd_6363959 := by exact prefixLift 6363959
  have htrace : WordTrace (prefixWord ++ tailWord_6363959) baseStart_6363959 baseEnd_6363959 := by
    simpa [prefixWord, tailWord_6363959, baseEnd_6363959] using wordTrace_append hprefix tailTrace_6363959
  have hstable : (prefixWord ++ tailWord_6363959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6363959).length < 2 ^ (prefixWord ++ tailWord_6363959).sum := by decide
  have hdescent : baseEnd_6363959 < baseStart_6363959 := by decide
  rcases family_descends (prefixWord ++ tailWord_6363959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6363999 : List Nat := [1, 1, 2, 3, 1, 3, 2, 1, 2, 7]
def baseStart_6363999 : Nat := 118140960795 + 6363999 * 2 ^ 59
def prefixEnd_6363999 : Nat := 4983230072969 + 3 ^ 40 * 6363999 * 2
def baseEnd_6363999 : Nat := 1089263457244183852781669

theorem tailTrace_6363999 : CollatzResearch.WordTrace tailWord_6363999 prefixEnd_6363999 1089263457244183852781669 := by
  unfold tailWord_6363999
  simp only [CollatzResearch.WordTrace]
  refine ⟨232114112471325982343015051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154742741647550654895343367 232114112471325982343015051)
  ·
    refine ⟨348171168706988973514522577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232114112471325982343015051 348171168706988973514522577)
    ·
      refine ⟨261128376530241730135891933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 348171168706988973514522577 261128376530241730135891933)
      ·
        refine ⟨97923141198840648800959475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 261128376530241730135891933 97923141198840648800959475)
        ·
          refine ⟨146884711798260973201439213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97923141198840648800959475 146884711798260973201439213)
          ·
            refine ⟨55081766924347864950539705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 146884711798260973201439213 55081766924347864950539705)
            ·
              refine ⟨41311325193260898712904779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55081766924347864950539705 41311325193260898712904779)
              ·
                refine ⟨61966987789891348069357169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41311325193260898712904779 61966987789891348069357169)
                ·
                  refine ⟨46475240842418511052017877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61966987789891348069357169 46475240842418511052017877)
                  ·
                    refine ⟨1089263457244183852781669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46475240842418511052017877 1089263457244183852781669)
                    ·
                      rfl

theorem cell23_6363999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 1, 2, 7].length) (baseStart_6363999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6363999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6363999 prefixEnd_6363999 := by exact prefixLift 6363999
  have htrace : WordTrace (prefixWord ++ tailWord_6363999) baseStart_6363999 baseEnd_6363999 := by
    simpa [prefixWord, tailWord_6363999, baseEnd_6363999] using wordTrace_append hprefix tailTrace_6363999
  have hstable : (prefixWord ++ tailWord_6363999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6363999).length < 2 ^ (prefixWord ++ tailWord_6363999).sum := by decide
  have hdescent : baseEnd_6363999 < baseStart_6363999 := by decide
  rcases family_descends (prefixWord ++ tailWord_6363999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6364034 : List Nat := [3, 4, 2, 2, 2, 1, 1, 1, 1, 1, 5]
def baseStart_6364034 : Nat := 118140960795 + 6364034 * 2 ^ 59
def prefixEnd_6364034 : Nat := 4983230072969 + 3 ^ 40 * 6364034 * 2
def baseEnd_6364034 : Nat := 3267808343555458921407347

theorem tailTrace_6364034 : CollatzResearch.WordTrace tailWord_6364034 prefixEnd_6364034 3267808343555458921407347 := by
  unfold tailWord_6364034
  simp only [CollatzResearch.WordTrace]
  refine ⟨58028847256549795830134789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154743592684132788880359437 58028847256549795830134789)
  ·
    refine ⟨10880408860603086718150273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58028847256549795830134789 10880408860603086718150273)
    ·
      refine ⟨8160306645452315038612705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10880408860603086718150273 8160306645452315038612705)
      ·
        refine ⟨6120229984089236278959529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8160306645452315038612705 6120229984089236278959529)
        ·
          refine ⟨4590172488066927209219647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6120229984089236278959529 4590172488066927209219647)
          ·
            refine ⟨6885258732100390813829471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4590172488066927209219647 6885258732100390813829471)
            ·
              refine ⟨10327888098150586220744207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6885258732100390813829471 10327888098150586220744207)
              ·
                refine ⟨15491832147225879331116311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10327888098150586220744207 15491832147225879331116311)
                ·
                  refine ⟨23237748220838818996674467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15491832147225879331116311 23237748220838818996674467)
                  ·
                    refine ⟨34856622331258228495011701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23237748220838818996674467 34856622331258228495011701)
                    ·
                      refine ⟨3267808343555458921407347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34856622331258228495011701 3267808343555458921407347)
                      ·
                        rfl

theorem cell23_6364034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_6364034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6364034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6364034 prefixEnd_6364034 := by exact prefixLift 6364034
  have htrace : WordTrace (prefixWord ++ tailWord_6364034) baseStart_6364034 baseEnd_6364034 := by
    simpa [prefixWord, tailWord_6364034, baseEnd_6364034] using wordTrace_append hprefix tailTrace_6364034
  have hstable : (prefixWord ++ tailWord_6364034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6364034).length < 2 ^ (prefixWord ++ tailWord_6364034).sum := by decide
  have hdescent : baseEnd_6364034 < baseStart_6364034 := by decide
  rcases family_descends (prefixWord ++ tailWord_6364034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6364049 : List Nat := [1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 6]
def baseStart_6364049 : Nat := 118140960795 + 6364049 * 2 ^ 59
def prefixEnd_6364049 : Nat := 4983230072969 + 3 ^ 40 * 6364049 * 2
def baseEnd_6364049 : Nat := 3267816045765276362719777

theorem tailTrace_6364049 : CollatzResearch.WordTrace tailWord_6364049 prefixEnd_6364049 3267816045765276362719777 := by
  unfold tailWord_6364049
  simp only [CollatzResearch.WordTrace]
  refine ⟨232115936121144840882335201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154743957414096560588223467 232115936121144840882335201)
  ·
    refine ⟨174086952090858630661751401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232115936121144840882335201 174086952090858630661751401)
    ·
      refine ⟨130565214068143972996313551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174086952090858630661751401 130565214068143972996313551)
      ·
        refine ⟨195847821102215959494470327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130565214068143972996313551 195847821102215959494470327)
        ·
          refine ⟨293771731653323939241705491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195847821102215959494470327 293771731653323939241705491)
          ·
            refine ⟨440657597479985908862558237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 293771731653323939241705491 440657597479985908862558237)
            ·
              refine ⟨165246599054994715823459339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 440657597479985908862558237 165246599054994715823459339)
              ·
                refine ⟨247869898582492073735189009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 165246599054994715823459339 247869898582492073735189009)
                ·
                  refine ⟨185902423936869055301391757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 247869898582492073735189009 185902423936869055301391757)
                  ·
                    refine ⟨69713408976325895738021909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 185902423936869055301391757 69713408976325895738021909)
                    ·
                      refine ⟨3267816045765276362719777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69713408976325895738021909 3267816045765276362719777)
                      ·
                        rfl

theorem cell23_6364049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 6].length) (baseStart_6364049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6364049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6364049 prefixEnd_6364049 := by exact prefixLift 6364049
  have htrace : WordTrace (prefixWord ++ tailWord_6364049) baseStart_6364049 baseEnd_6364049 := by
    simpa [prefixWord, tailWord_6364049, baseEnd_6364049] using wordTrace_append hprefix tailTrace_6364049
  have hstable : (prefixWord ++ tailWord_6364049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6364049).length < 2 ^ (prefixWord ++ tailWord_6364049).sum := by decide
  have hdescent : baseEnd_6364049 < baseStart_6364049 := by decide
  rcases family_descends (prefixWord ++ tailWord_6364049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6364104 : List Nat := [2, 1, 3, 1, 5, 2, 1, 2, 2, 2, 2]
def baseStart_6364104 : Nat := 118140960795 + 6364104 * 2 ^ 59
def prefixEnd_6364104 : Nat := 4983230072969 + 3 ^ 40 * 6364104 * 2
def baseEnd_6364104 : Nat := 3267844287201273647532025

theorem tailTrace_6364104 : CollatzResearch.WordTrace tailWord_6364104 prefixEnd_6364104 3267844287201273647532025 := by
  unfold tailWord_6364104
  simp only [CollatzResearch.WordTrace]
  refine ⟨116058971067972792637793683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154745294757297056850391577 116058971067972792637793683)
  ·
    refine ⟨174088456601959188956690525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116058971067972792637793683 174088456601959188956690525)
    ·
      refine ⟨65283171225734695858758947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174088456601959188956690525 65283171225734695858758947)
      ·
        refine ⟨97924756838602043788138421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65283171225734695858758947 97924756838602043788138421)
        ·
          refine ⟨9180445953618941605137977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 97924756838602043788138421 9180445953618941605137977)
          ·
            refine ⟨6885334465214206203853483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9180445953618941605137977 6885334465214206203853483)
            ·
              refine ⟨10328001697821309305780225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6885334465214206203853483 10328001697821309305780225)
              ·
                refine ⟨7746001273365981979335169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10328001697821309305780225 7746001273365981979335169)
                ·
                  refine ⟨5809500955024486484501377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7746001273365981979335169 5809500955024486484501377)
                  ·
                    refine ⟨4357125716268364863376033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5809500955024486484501377 4357125716268364863376033)
                    ·
                      refine ⟨3267844287201273647532025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4357125716268364863376033 3267844287201273647532025)
                      ·
                        rfl

theorem cell23_6364104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 2, 2, 2, 2].length) (baseStart_6364104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6364104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6364104 prefixEnd_6364104 := by exact prefixLift 6364104
  have htrace : WordTrace (prefixWord ++ tailWord_6364104) baseStart_6364104 baseEnd_6364104 := by
    simpa [prefixWord, tailWord_6364104, baseEnd_6364104] using wordTrace_append hprefix tailTrace_6364104
  have hstable : (prefixWord ++ tailWord_6364104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6364104).length < 2 ^ (prefixWord ++ tailWord_6364104).sum := by decide
  have hdescent : baseEnd_6364104 < baseStart_6364104 := by decide
  rcases family_descends (prefixWord ++ tailWord_6364104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6364106 : List Nat := [3, 1, 2, 1, 2, 1, 1, 3, 4, 5]
def baseStart_6364106 : Nat := 118140960795 + 6364106 * 2 ^ 59
def prefixEnd_6364106 : Nat := 4983230072969 + 3 ^ 40 * 6364106 * 2
def baseEnd_6364106 : Nat := 1089281771387527546569005

theorem tailTrace_6364106 : CollatzResearch.WordTrace tailWord_6364106 prefixEnd_6364106 1089281771387527546569005 := by
  unfold tailWord_6364106
  simp only [CollatzResearch.WordTrace]
  refine ⟨58029503770484584904290043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154745343387958893078106781 58029503770484584904290043)
  ·
    refine ⟨87044255655726877356435065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58029503770484584904290043 87044255655726877356435065)
    ·
      refine ⟨65283191741795158017326299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87044255655726877356435065 65283191741795158017326299)
      ·
        refine ⟨97924787612692737025989449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65283191741795158017326299 97924787612692737025989449)
        ·
          refine ⟨73443590709519552769492087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97924787612692737025989449 73443590709519552769492087)
          ·
            refine ⟨110165386064279329154238131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73443590709519552769492087 110165386064279329154238131)
            ·
              refine ⟨165248079096418993731357197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110165386064279329154238131 165248079096418993731357197)
              ·
                refine ⟨61968029661157122649258949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 165248079096418993731357197 61968029661157122649258949)
                ·
                  refine ⟨11619005561466960496736053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61968029661157122649258949 11619005561466960496736053)
                  ·
                    refine ⟨1089281771387527546569005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11619005561466960496736053 1089281771387527546569005)
                    ·
                      rfl

theorem cell23_6364106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 3, 4, 5].length) (baseStart_6364106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6364106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6364106 prefixEnd_6364106 := by exact prefixLift 6364106
  have htrace : WordTrace (prefixWord ++ tailWord_6364106) baseStart_6364106 baseEnd_6364106 := by
    simpa [prefixWord, tailWord_6364106, baseEnd_6364106] using wordTrace_append hprefix tailTrace_6364106
  have hstable : (prefixWord ++ tailWord_6364106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6364106).length < 2 ^ (prefixWord ++ tailWord_6364106).sum := by decide
  have hdescent : baseEnd_6364106 < baseStart_6364106 := by decide
  rcases family_descends (prefixWord ++ tailWord_6364106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6364170 : List Nat := [3, 1, 2, 2, 3, 1, 3, 1, 3, 4]
def baseStart_6364170 : Nat := 118140960795 + 6364170 * 2 ^ 59
def prefixEnd_6364170 : Nat := 4983230072969 + 3 ^ 40 * 6364170 * 2
def baseEnd_6364170 : Nat := 1089292725641490129768907

theorem tailTrace_6364170 : CollatzResearch.WordTrace tailWord_6364170 prefixEnd_6364170 1089292725641490129768907 := by
  unfold tailWord_6364170
  simp only [CollatzResearch.WordTrace]
  refine ⟨58030087338426619636872491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154746899569137652364993309 58030087338426619636872491)
  ·
    refine ⟨87045131007639929455308737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58030087338426619636872491 87045131007639929455308737)
    ·
      refine ⟨65283848255729947091481553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87045131007639929455308737 65283848255729947091481553)
      ·
        refine ⟨48962886191797460318611165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65283848255729947091481553 48962886191797460318611165)
        ·
          refine ⟨18361082321924047619479187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48962886191797460318611165 18361082321924047619479187)
          ·
            refine ⟨27541623482886071429218781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18361082321924047619479187 27541623482886071429218781)
            ·
              refine ⟨10328108806082276785957043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27541623482886071429218781 10328108806082276785957043)
              ·
                refine ⟨15492163209123415178935565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10328108806082276785957043 15492163209123415178935565)
                ·
                  refine ⟨5809561203421280692100837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15492163209123415178935565 5809561203421280692100837)
                  ·
                    refine ⟨1089292725641490129768907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5809561203421280692100837 1089292725641490129768907)
                    ·
                      rfl

theorem cell23_6364170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 1, 3, 4].length) (baseStart_6364170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6364170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6364170 prefixEnd_6364170 := by exact prefixLift 6364170
  have htrace : WordTrace (prefixWord ++ tailWord_6364170) baseStart_6364170 baseEnd_6364170 := by
    simpa [prefixWord, tailWord_6364170, baseEnd_6364170] using wordTrace_append hprefix tailTrace_6364170
  have hstable : (prefixWord ++ tailWord_6364170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6364170).length < 2 ^ (prefixWord ++ tailWord_6364170).sum := by decide
  have hdescent : baseEnd_6364170 < baseStart_6364170 := by decide
  rcases family_descends (prefixWord ++ tailWord_6364170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6364227 : List Nat := [1, 1, 1, 3, 1, 2, 5, 4, 1, 1, 3]
def baseStart_6364227 : Nat := 118140960795 + 6364227 * 2 ^ 59
def prefixEnd_6364227 : Nat := 4983230072969 + 3 ^ 40 * 6364227 * 2
def baseEnd_6364227 : Nat := 3267907445321776666293959

theorem tailTrace_6364227 : CollatzResearch.WordTrace tailWord_6364227 prefixEnd_6364227 3267907445321776666293959 := by
  unfold tailWord_6364227
  simp only [CollatzResearch.WordTrace]
  refine ⟨232122428314499977282314935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154748285542999984854876623 232122428314499977282314935)
  ·
    refine ⟨348183642471749965923472403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232122428314499977282314935 348183642471749965923472403)
    ·
      refine ⟨522275463707624948885208605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348183642471749965923472403 522275463707624948885208605)
      ·
        refine ⟨195853298890359355831953227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 522275463707624948885208605 195853298890359355831953227)
        ·
          refine ⟨293779948335539033747929841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195853298890359355831953227 293779948335539033747929841)
          ·
            refine ⟨220334961251654275310947381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 293779948335539033747929841 220334961251654275310947381)
            ·
              refine ⟨20656402617342588310401317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 220334961251654275310947381 20656402617342588310401317)
              ·
                refine ⟨3873075490751735308200247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20656402617342588310401317 3873075490751735308200247)
                ·
                  refine ⟨5809613236127602962300371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3873075490751735308200247 5809613236127602962300371)
                  ·
                    refine ⟨8714419854191404443450557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5809613236127602962300371 8714419854191404443450557)
                    ·
                      refine ⟨3267907445321776666293959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8714419854191404443450557 3267907445321776666293959)
                      ·
                        rfl

theorem cell23_6364227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 4, 1, 1, 3].length) (baseStart_6364227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6364227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6364227 prefixEnd_6364227 := by exact prefixLift 6364227
  have htrace : WordTrace (prefixWord ++ tailWord_6364227) baseStart_6364227 baseEnd_6364227 := by
    simpa [prefixWord, tailWord_6364227, baseEnd_6364227] using wordTrace_append hprefix tailTrace_6364227
  have hstable : (prefixWord ++ tailWord_6364227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6364227).length < 2 ^ (prefixWord ++ tailWord_6364227).sum := by decide
  have hdescent : baseEnd_6364227 < baseStart_6364227 := by decide
  rcases family_descends (prefixWord ++ tailWord_6364227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6364283 : List Nat := [1, 1, 1, 1, 1, 4, 1, 4, 3, 3, 3]
def baseStart_6364283 : Nat := 118140960795 + 6364283 * 2 ^ 59
def prefixEnd_6364283 : Nat := 4983230072969 + 3 ^ 40 * 6364283 * 2
def baseEnd_6364283 : Nat := 3267936200238428447193701

theorem tailTrace_6364283 : CollatzResearch.WordTrace tailWord_6364283 prefixEnd_6364283 3267936200238428447193701 := by
  unfold tailWord_6364283
  simp only [CollatzResearch.WordTrace]
  refine ⟨232124470802297098846353503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154749647201531399230902335 232124470802297098846353503)
  ·
    refine ⟨348186706203445648269530255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232124470802297098846353503 348186706203445648269530255)
    ·
      refine ⟨522280059305168472404295383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348186706203445648269530255 522280059305168472404295383)
      ·
        refine ⟨783420088957752708606443075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 522280059305168472404295383 783420088957752708606443075)
        ·
          refine ⟨1175130133436629062909664613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 783420088957752708606443075 1175130133436629062909664613)
          ·
            refine ⟨220336900019367949295562115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1175130133436629062909664613 220336900019367949295562115)
            ·
              refine ⟨330505350029051923943343173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 220336900019367949295562115 330505350029051923943343173)
              ·
                refine ⟨61969753130447235739376845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 330505350029051923943343173 61969753130447235739376845)
                ·
                  refine ⟨23238657423917713402266317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61969753130447235739376845 23238657423917713402266317)
                  ·
                    refine ⟨8714496533969142525849869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23238657423917713402266317 8714496533969142525849869)
                    ·
                      refine ⟨3267936200238428447193701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8714496533969142525849869 3267936200238428447193701)
                      ·
                        rfl

theorem cell23_6364283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 4, 3, 3, 3].length) (baseStart_6364283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6364283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6364283 prefixEnd_6364283 := by exact prefixLift 6364283
  have htrace : WordTrace (prefixWord ++ tailWord_6364283) baseStart_6364283 baseEnd_6364283 := by
    simpa [prefixWord, tailWord_6364283, baseEnd_6364283] using wordTrace_append hprefix tailTrace_6364283
  have hstable : (prefixWord ++ tailWord_6364283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6364283).length < 2 ^ (prefixWord ++ tailWord_6364283).sum := by decide
  have hdescent : baseEnd_6364283 < baseStart_6364283 := by decide
  rcases family_descends (prefixWord ++ tailWord_6364283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6364284 : List Nat := [2, 2, 2, 1, 1, 3, 1, 6, 1, 2, 2]
def baseStart_6364284 : Nat := 118140960795 + 6364284 * 2 ^ 59
def prefixEnd_6364284 : Nat := 4983230072969 + 3 ^ 40 * 6364284 * 2
def baseEnd_6364284 : Nat := 3267936713719082943281197

theorem tailTrace_6364284 : CollatzResearch.WordTrace tailWord_6364284 prefixEnd_6364284 3267936713719082943281197 := by
  unfold tailWord_6364284
  simp only [CollatzResearch.WordTrace]
  refine ⟨116062253637646738008569953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154749671516862317344759937 116062253637646738008569953)
  ·
    refine ⟨87046690228235053506427465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116062253637646738008569953 87046690228235053506427465)
    ·
      refine ⟨65285017671176290129820599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87046690228235053506427465 65285017671176290129820599)
      ·
        refine ⟨97927526506764435194730899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65285017671176290129820599 97927526506764435194730899)
        ·
          refine ⟨146891289760146652792096349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97927526506764435194730899 146891289760146652792096349)
          ·
            refine ⟨55084233660054994797036131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 146891289760146652792096349 55084233660054994797036131)
            ·
              refine ⟨82626350490082492195554197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55084233660054994797036131 82626350490082492195554197)
              ·
                refine ⟨3873110179222616821666603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 82626350490082492195554197 3873110179222616821666603)
                ·
                  refine ⟨5809665268833925232499905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3873110179222616821666603 5809665268833925232499905)
                  ·
                    refine ⟨4357248951625443924374929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5809665268833925232499905 4357248951625443924374929)
                    ·
                      refine ⟨3267936713719082943281197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4357248951625443924374929 3267936713719082943281197)
                      ·
                        rfl

theorem cell23_6364284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 6, 1, 2, 2].length) (baseStart_6364284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6364284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6364284 prefixEnd_6364284 := by exact prefixLift 6364284
  have htrace : WordTrace (prefixWord ++ tailWord_6364284) baseStart_6364284 baseEnd_6364284 := by
    simpa [prefixWord, tailWord_6364284, baseEnd_6364284] using wordTrace_append hprefix tailTrace_6364284
  have hstable : (prefixWord ++ tailWord_6364284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6364284).length < 2 ^ (prefixWord ++ tailWord_6364284).sum := by decide
  have hdescent : baseEnd_6364284 < baseStart_6364284 := by decide
  rcases family_descends (prefixWord ++ tailWord_6364284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6364318 : List Nat := [4, 3, 1, 1, 2, 1, 3, 3, 1, 2, 2]
def baseStart_6364318 : Nat := 118140960795 + 6364318 * 2 ^ 59
def prefixEnd_6364318 : Nat := 4983230072969 + 3 ^ 40 * 6364318 * 2
def baseEnd_6364318 : Nat := 3267954172061335810256041

theorem tailTrace_6364318 : CollatzResearch.WordTrace tailWord_6364318 prefixEnd_6364318 3267954172061335810256041 := by
  unfold tailWord_6364318
  simp only [CollatzResearch.WordTrace]
  refine ⟨29015718419646287477984701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154750498238113533215918405 29015718419646287477984701)
  ·
    refine ⟨10880894407367357804244263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29015718419646287477984701 10880894407367357804244263)
    ·
      refine ⟨16321341611051036706366395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10880894407367357804244263 16321341611051036706366395)
      ·
        refine ⟨24482012416576555059549593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16321341611051036706366395 24482012416576555059549593)
        ·
          refine ⟨18361509312432416294662195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24482012416576555059549593 18361509312432416294662195)
          ·
            refine ⟨27542263968648624441993293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18361509312432416294662195 27542263968648624441993293)
            ·
              refine ⟨10328348988243234165747485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27542263968648624441993293 10328348988243234165747485)
              ·
                refine ⟨3873130870591212812155307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10328348988243234165747485 3873130870591212812155307)
                ·
                  refine ⟨5809696305886819218232961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3873130870591212812155307 5809696305886819218232961)
                  ·
                    refine ⟨4357272229415114413674721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5809696305886819218232961 4357272229415114413674721)
                    ·
                      refine ⟨3267954172061335810256041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4357272229415114413674721 3267954172061335810256041)
                      ·
                        rfl

theorem cell23_6364318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 3, 1, 2, 2].length) (baseStart_6364318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6364318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6364318 prefixEnd_6364318 := by exact prefixLift 6364318
  have htrace : WordTrace (prefixWord ++ tailWord_6364318) baseStart_6364318 baseEnd_6364318 := by
    simpa [prefixWord, tailWord_6364318, baseEnd_6364318] using wordTrace_append hprefix tailTrace_6364318
  have hstable : (prefixWord ++ tailWord_6364318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6364318).length < 2 ^ (prefixWord ++ tailWord_6364318).sum := by decide
  have hdescent : baseEnd_6364318 < baseStart_6364318 := by decide
  rcases family_descends (prefixWord ++ tailWord_6364318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6364343 : List Nat := [1, 1, 3, 1, 4, 1, 1, 2, 1, 3, 5]
def baseStart_6364343 : Nat := 118140960795 + 6364343 * 2 ^ 59
def prefixEnd_6364343 : Nat := 4983230072969 + 3 ^ 40 * 6364343 * 2
def baseEnd_6364343 : Nat := 3267967009077698212443425

theorem tailTrace_6364343 : CollatzResearch.WordTrace tailWord_6364343 prefixEnd_6364343 3267967009077698212443425 := by
  unfold tailWord_6364343
  simp only [CollatzResearch.WordTrace]
  refine ⟨232126659182079729093537683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154751106121386486062358455 232126659182079729093537683)
  ·
    refine ⟨348189988773119593640306525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232126659182079729093537683 348189988773119593640306525)
    ·
      refine ⟨130571245789919847615114947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 348189988773119593640306525 130571245789919847615114947)
      ·
        refine ⟨195856868684879771422672421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130571245789919847615114947 195856868684879771422672421)
        ·
          refine ⟨36723162878414957141751079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 195856868684879771422672421 36723162878414957141751079)
          ·
            refine ⟨55084744317622435712626619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36723162878414957141751079 55084744317622435712626619)
            ·
              refine ⟨82627116476433653568939929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55084744317622435712626619 82627116476433653568939929)
              ·
                refine ⟨61970337357325240176704947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82627116476433653568939929 61970337357325240176704947)
                ·
                  refine ⟨92955506035987860265057421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61970337357325240176704947 92955506035987860265057421)
                  ·
                    refine ⟨34858314763495447599396533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 92955506035987860265057421 34858314763495447599396533)
                    ·
                      refine ⟨3267967009077698212443425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34858314763495447599396533 3267967009077698212443425)
                      ·
                        rfl

theorem cell23_6364343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 2, 1, 3, 5].length) (baseStart_6364343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6364343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6364343 prefixEnd_6364343 := by exact prefixLift 6364343
  have htrace : WordTrace (prefixWord ++ tailWord_6364343) baseStart_6364343 baseEnd_6364343 := by
    simpa [prefixWord, tailWord_6364343, baseEnd_6364343] using wordTrace_append hprefix tailTrace_6364343
  have hstable : (prefixWord ++ tailWord_6364343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6364343).length < 2 ^ (prefixWord ++ tailWord_6364343).sum := by decide
  have hdescent : baseEnd_6364343 < baseStart_6364343 := by decide
  rcases family_descends (prefixWord ++ tailWord_6364343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6364427 : List Nat := [1, 1, 1, 1, 5, 5, 1, 1, 2, 5]
def baseStart_6364427 : Nat := 118140960795 + 6364427 * 2 ^ 59
def prefixEnd_6364427 : Nat := 4983230072969 + 3 ^ 40 * 6364427 * 2
def baseEnd_6364427 : Nat := 1089336713817558627931013

theorem tailTrace_6364427 : CollatzResearch.WordTrace tailWord_6364427 prefixEnd_6364427 1089336713817558627931013 := by
  unfold tailWord_6364427
  simp only [CollatzResearch.WordTrace]
  refine ⟨232129722913775411439595535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154753148609183607626397023 232129722913775411439595535)
  ·
    refine ⟨348194584370663117159393303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232129722913775411439595535 348194584370663117159393303)
    ·
      refine ⟨522291876555994675739089955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348194584370663117159393303 522291876555994675739089955)
      ·
        refine ⟨783437814833992013608634933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 522291876555994675739089955 783437814833992013608634933)
        ·
          refine ⟨73447295140686751275809525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 783437814833992013608634933 73447295140686751275809525)
          ·
            refine ⟨6885683919439382932107143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 73447295140686751275809525 6885683919439382932107143)
            ·
              refine ⟨10328525879159074398160715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6885683919439382932107143 10328525879159074398160715)
              ·
                refine ⟨15492788818738611597241073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10328525879159074398160715 15492788818738611597241073)
                ·
                  refine ⟨11619591614053958697930805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15492788818738611597241073 11619591614053958697930805)
                  ·
                    refine ⟨1089336713817558627931013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11619591614053958697930805 1089336713817558627931013)
                    ·
                      rfl

theorem cell23_6364427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 1, 2, 5].length) (baseStart_6364427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6364427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6364427 prefixEnd_6364427 := by exact prefixLift 6364427
  have htrace : WordTrace (prefixWord ++ tailWord_6364427) baseStart_6364427 baseEnd_6364427 := by
    simpa [prefixWord, tailWord_6364427, baseEnd_6364427] using wordTrace_append hprefix tailTrace_6364427
  have hstable : (prefixWord ++ tailWord_6364427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6364427).length < 2 ^ (prefixWord ++ tailWord_6364427).sum := by decide
  have hdescent : baseEnd_6364427 < baseStart_6364427 := by decide
  rcases family_descends (prefixWord ++ tailWord_6364427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6364480 : List Nat := [2, 1, 1, 2, 2, 1, 3, 1, 2, 5, 3]
def baseStart_6364480 : Nat := 118140960795 + 6364480 * 2 ^ 59
def prefixEnd_6364480 : Nat := 4983230072969 + 3 ^ 40 * 6364480 * 2
def baseEnd_6364480 : Nat := 3268037355927364176430295

theorem tailTrace_6364480 : CollatzResearch.WordTrace tailWord_6364480 prefixEnd_6364480 3268037355927364176430295 := by
  unfold tailWord_6364480
  simp only [CollatzResearch.WordTrace]
  refine ⟨116065827991291700745637447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154754437321722267660849929 116065827991291700745637447)
  ·
    refine ⟨174098741986937551118456171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116065827991291700745637447 174098741986937551118456171)
    ·
      refine ⟨261148112980406326677684257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174098741986937551118456171 261148112980406326677684257)
      ·
        refine ⟨195861084735304745008263193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 261148112980406326677684257 195861084735304745008263193)
        ·
          refine ⟨146895813551478558756197395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 195861084735304745008263193 146895813551478558756197395)
          ·
            refine ⟨220343720327217838134296093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146895813551478558756197395 220343720327217838134296093)
            ·
              refine ⟨82628895122706689300361035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 220343720327217838134296093 82628895122706689300361035)
              ·
                refine ⟨123943342684060033950541553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82628895122706689300361035 123943342684060033950541553)
                ·
                  refine ⟨92957507013045025462906165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 123943342684060033950541553 92957507013045025462906165)
                  ·
                    refine ⟨8714766282472971137147453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 92957507013045025462906165 8714766282472971137147453)
                    ·
                      refine ⟨3268037355927364176430295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8714766282472971137147453 3268037355927364176430295)
                      ·
                        rfl

theorem cell23_6364480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 2, 5, 3].length) (baseStart_6364480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6364480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6364480 prefixEnd_6364480 := by exact prefixLift 6364480
  have htrace : WordTrace (prefixWord ++ tailWord_6364480) baseStart_6364480 baseEnd_6364480 := by
    simpa [prefixWord, tailWord_6364480, baseEnd_6364480] using wordTrace_append hprefix tailTrace_6364480
  have hstable : (prefixWord ++ tailWord_6364480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6364480).length < 2 ^ (prefixWord ++ tailWord_6364480).sum := by decide
  have hdescent : baseEnd_6364480 < baseStart_6364480 := by decide
  rcases family_descends (prefixWord ++ tailWord_6364480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6364484 : List Nat := [2, 3, 4, 1, 1, 1, 2, 1, 1, 4, 3]
def baseStart_6364484 : Nat := 118140960795 + 6364484 * 2 ^ 59
def prefixEnd_6364484 : Nat := 4983230072969 + 3 ^ 40 * 6364484 * 2
def baseEnd_6364484 : Nat := 3268039409849982160780277

theorem tailTrace_6364484 : CollatzResearch.WordTrace tailWord_6364484 prefixEnd_6364484 3268039409849982160780277 := by
  unfold tailWord_6364484
  simp only [CollatzResearch.WordTrace]
  refine ⟨116065900937284455087210253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154754534583045940116280337 116065900937284455087210253)
  ·
    refine ⟨43524712851481670657703845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116065900937284455087210253 43524712851481670657703845)
    ·
      refine ⟨8160883659652813248319471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43524712851481670657703845 8160883659652813248319471)
      ·
        refine ⟨12241325489479219872479207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8160883659652813248319471 12241325489479219872479207)
        ·
          refine ⟨18361988234218829808718811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12241325489479219872479207 18361988234218829808718811)
          ·
            refine ⟨27542982351328244713078217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18361988234218829808718811 27542982351328244713078217)
            ·
              refine ⟨20657236763496183534808663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27542982351328244713078217 20657236763496183534808663)
              ·
                refine ⟨30985855145244275302212995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20657236763496183534808663 30985855145244275302212995)
                ·
                  refine ⟨46478782717866412953319493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30985855145244275302212995 46478782717866412953319493)
                  ·
                    refine ⟨8714771759599952428747405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46478782717866412953319493 8714771759599952428747405)
                    ·
                      refine ⟨3268039409849982160780277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8714771759599952428747405 3268039409849982160780277)
                      ·
                        rfl

theorem cell23_6364484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_6364484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6364484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6364484 prefixEnd_6364484 := by exact prefixLift 6364484
  have htrace : WordTrace (prefixWord ++ tailWord_6364484) baseStart_6364484 baseEnd_6364484 := by
    simpa [prefixWord, tailWord_6364484, baseEnd_6364484] using wordTrace_append hprefix tailTrace_6364484
  have hstable : (prefixWord ++ tailWord_6364484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6364484).length < 2 ^ (prefixWord ++ tailWord_6364484).sum := by decide
  have hdescent : baseEnd_6364484 < baseStart_6364484 := by decide
  rcases family_descends (prefixWord ++ tailWord_6364484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6364537 : List Nat := [1, 2, 1, 3, 2, 1, 2, 1, 2, 6, 2]
def baseStart_6364537 : Nat := 118140960795 + 6364537 * 2 ^ 59
def prefixEnd_6364537 : Nat := 4983230072969 + 3 ^ 40 * 6364537 * 2
def baseEnd_6364537 : Nat := 3268066624324670453417533

theorem tailTrace_6364537 : CollatzResearch.WordTrace tailWord_6364537 prefixEnd_6364537 3268066624324670453417533 := by
  unfold tailWord_6364537
  simp only [CollatzResearch.WordTrace]
  refine ⟨232133734943376900226099865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154755823295584600150733243 232133734943376900226099865)
  ·
    refine ⟨174100301207532675169574899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232133734943376900226099865 174100301207532675169574899)
    ·
      refine ⟨261150451811299012754362349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174100301207532675169574899 261150451811299012754362349)
      ·
        refine ⟨97931419429237129782885881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 261150451811299012754362349 97931419429237129782885881)
        ·
          refine ⟨73448564571927847337164411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97931419429237129782885881 73448564571927847337164411)
          ·
            refine ⟨110172846857891771005746617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73448564571927847337164411 110172846857891771005746617)
            ·
              refine ⟨82629635143418828254309963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110172846857891771005746617 82629635143418828254309963)
              ·
                refine ⟨123944452715128242381464945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82629635143418828254309963 123944452715128242381464945)
                ·
                  refine ⟨92958339536346181786098709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 123944452715128242381464945 92958339536346181786098709)
                  ·
                    refine ⟨4357422165766227271223377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 92958339536346181786098709 4357422165766227271223377)
                    ·
                      refine ⟨3268066624324670453417533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4357422165766227271223377 3268066624324670453417533)
                      ·
                        rfl

theorem cell23_6364537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 2, 6, 2].length) (baseStart_6364537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6364537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6364537 prefixEnd_6364537 := by exact prefixLift 6364537
  have htrace : WordTrace (prefixWord ++ tailWord_6364537) baseStart_6364537 baseEnd_6364537 := by
    simpa [prefixWord, tailWord_6364537, baseEnd_6364537] using wordTrace_append hprefix tailTrace_6364537
  have hstable : (prefixWord ++ tailWord_6364537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6364537).length < 2 ^ (prefixWord ++ tailWord_6364537).sum := by decide
  have hdescent : baseEnd_6364537 < baseStart_6364537 := by decide
  rcases family_descends (prefixWord ++ tailWord_6364537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6364547 : List Nat := [1, 1, 1, 3, 5, 2, 1, 2, 1, 6]
def baseStart_6364547 : Nat := 118140960795 + 6364547 * 2 ^ 59
def prefixEnd_6364547 : Nat := 4983230072969 + 3 ^ 40 * 6364547 * 2
def baseEnd_6364547 : Nat := 1089357253043738471430829

theorem tailTrace_6364547 : CollatzResearch.WordTrace tailWord_6364547 prefixEnd_6364547 1089357253043738471430829 := by
  unfold tailWord_6364547
  simp only [CollatzResearch.WordTrace]
  refine ⟨232134099673340671933963895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154756066448893781289309263 232134099673340671933963895)
  ·
    refine ⟨348201149510011007900945843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232134099673340671933963895 348201149510011007900945843)
    ·
      refine ⟨522301724265016511851418765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348201149510011007900945843 522301724265016511851418765)
      ·
        refine ⟨195863146599381191944282037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 522301724265016511851418765 195863146599381191944282037)
        ·
          refine ⟨18362169993691986744776441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 195863146599381191944282037 18362169993691986744776441)
          ·
            refine ⟨13771627495268990058582331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18362169993691986744776441 13771627495268990058582331)
            ·
              refine ⟨20657441242903485087873497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13771627495268990058582331 20657441242903485087873497)
              ·
                refine ⟨15493080932177613815905123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20657441242903485087873497 15493080932177613815905123)
                ·
                  refine ⟨23239621398266420723857685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15493080932177613815905123 23239621398266420723857685)
                  ·
                    refine ⟨1089357253043738471430829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23239621398266420723857685 1089357253043738471430829)
                    ·
                      rfl

theorem cell23_6364547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 2, 1, 6].length) (baseStart_6364547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6364547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6364547 prefixEnd_6364547 := by exact prefixLift 6364547
  have htrace : WordTrace (prefixWord ++ tailWord_6364547) baseStart_6364547 baseEnd_6364547 := by
    simpa [prefixWord, tailWord_6364547, baseEnd_6364547] using wordTrace_append hprefix tailTrace_6364547
  have hstable : (prefixWord ++ tailWord_6364547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6364547).length < 2 ^ (prefixWord ++ tailWord_6364547).sum := by decide
  have hdescent : baseEnd_6364547 < baseStart_6364547 := by decide
  rcases family_descends (prefixWord ++ tailWord_6364547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6364747 : List Nat := [1, 1, 1, 1, 3, 1, 3, 2, 2, 4, 4]
def baseStart_6364747 : Nat := 118140960795 + 6364747 * 2 ^ 59
def prefixEnd_6364747 : Nat := 4983230072969 + 3 ^ 40 * 6364747 * 2
def baseEnd_6364747 : Nat := 3268174455262114631791567

theorem tailTrace_6364747 : CollatzResearch.WordTrace tailWord_6364747 prefixEnd_6364747 3268174455262114631791567 := by
  unfold tailWord_6364747
  simp only [CollatzResearch.WordTrace]
  refine ⟨232141394272616106091244495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154760929515077404060829663 232141394272616106091244495)
  ·
    refine ⟨348212091408924159136866743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232141394272616106091244495 348212091408924159136866743)
    ·
      refine ⟨522318137113386238705300115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348212091408924159136866743 522318137113386238705300115)
      ·
        refine ⟨783477205670079358057950173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 522318137113386238705300115 783477205670079358057950173)
        ·
          refine ⟨293803952126279759271731315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 783477205670079358057950173 293803952126279759271731315)
          ·
            refine ⟨440705928189419638907596973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 293803952126279759271731315 440705928189419638907596973)
            ·
              refine ⟨165264723071032364590348865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 440705928189419638907596973 165264723071032364590348865)
              ·
                refine ⟨123948542303274273442761649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 165264723071032364590348865 123948542303274273442761649)
                ·
                  refine ⟨92961406727455705082071237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 123948542303274273442761649 92961406727455705082071237)
                  ·
                    refine ⟨17430263761397944702888357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 92961406727455705082071237 17430263761397944702888357)
                    ·
                      refine ⟨3268174455262114631791567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17430263761397944702888357 3268174455262114631791567)
                      ·
                        rfl

theorem cell23_6364747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 4, 4].length) (baseStart_6364747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6364747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6364747 prefixEnd_6364747 := by exact prefixLift 6364747
  have htrace : WordTrace (prefixWord ++ tailWord_6364747) baseStart_6364747 baseEnd_6364747 := by
    simpa [prefixWord, tailWord_6364747, baseEnd_6364747] using wordTrace_append hprefix tailTrace_6364747
  have hstable : (prefixWord ++ tailWord_6364747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6364747).length < 2 ^ (prefixWord ++ tailWord_6364747).sum := by decide
  have hdescent : baseEnd_6364747 < baseStart_6364747 := by decide
  rcases family_descends (prefixWord ++ tailWord_6364747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6364757 : List Nat := [1, 3, 2, 2, 1, 1, 1, 2, 10]
def baseStart_6364757 : Nat := 118140960795 + 6364757 * 2 ^ 59
def prefixEnd_6364757 : Nat := 4983230072969 + 3 ^ 40 * 6364757 * 2
def baseEnd_6364757 : Nat := 363131065563184399185169

theorem tailTrace_6364757 : CollatzResearch.WordTrace tailWord_6364757 prefixEnd_6364757 363131065563184399185169 := by
  unfold tailWord_6364757
  simp only [CollatzResearch.WordTrace]
  refine ⟨232141759002579877799108525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154761172668386585199405683 232141759002579877799108525)
  ·
    refine ⟨87053159625967454174665697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 232141759002579877799108525 87053159625967454174665697)
    ·
      refine ⟨65289869719475590630999273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87053159625967454174665697 65289869719475590630999273)
      ·
        refine ⟨48967402289606692973249455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65289869719475590630999273 48967402289606692973249455)
        ·
          refine ⟨73451103434410039459874183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48967402289606692973249455 73451103434410039459874183)
          ·
            refine ⟨110176655151615059189811275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73451103434410039459874183 110176655151615059189811275)
            ·
              refine ⟨165264982727422588784716913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110176655151615059189811275 165264982727422588784716913)
              ·
                refine ⟨123948737045566941588537685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 165264982727422588784716913 123948737045566941588537685)
                ·
                  refine ⟨363131065563184399185169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 123948737045566941588537685 363131065563184399185169)
                  ·
                    rfl

theorem cell23_6364757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 10].length) (baseStart_6364757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6364757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6364757 prefixEnd_6364757 := by exact prefixLift 6364757
  have htrace : WordTrace (prefixWord ++ tailWord_6364757) baseStart_6364757 baseEnd_6364757 := by
    simpa [prefixWord, tailWord_6364757, baseEnd_6364757] using wordTrace_append hprefix tailTrace_6364757
  have hstable : (prefixWord ++ tailWord_6364757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6364757).length < 2 ^ (prefixWord ++ tailWord_6364757).sum := by decide
  have hdescent : baseEnd_6364757 < baseStart_6364757 := by decide
  rcases family_descends (prefixWord ++ tailWord_6364757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
